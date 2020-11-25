open CAST
open Genlab

let compile out decl_list =
  let rec string_of_dec l n = match l with
    |[] -> "",n,[]
    |h::suite ->
      let l,var_cnt,var_list = string_of_dec suite n in
      begin
        match h with
        |CDECL(_,var) ->"",var_cnt +1,((var,var_cnt)::var_list)
        |CFUN(_,f,args,(_,code)) ->
          let dec_string , new_var_cnt, new_var_list = string_of_dec args var_cnt in
          String.concat "" ["fn_";f;":\n";
                            "push %rbp\n";"mov %rsp, %rbp\n";
                            dec_string;
                            string_of_code code (n+2);String.make n ' ';l] , 0, var_list
      end
  and string_of_code c n = match c with
    |CBLOCK(decs,code) ->
      let dec_string, var_cnt,var_list = string_of_dec decs n in
      String.concat "" [dec_string;
                        string_of_codelist code (n+2)]
    |CEXPR((_,e)) ->
      String.concat "" [String.make n ' ';"CEXPR{";string_of_expr e "";"}\n"]
    |CIF((_,e),(_,c1),(_,c2)) ->
      String.concat "" [String.make n ' ';
                        "CIF{\n";
                        string_of_expr e  "";"\n";
                        string_of_code c1 0;"\n";
                        string_of_code c2 0;"\n";
                        String.make n ' ';"}\n"]
    |CWHILE((_,e),(_,c)) ->
      String.concat "" [String.make n ' ';
                        "CWHILE{\n";string_of_expr e "";string_of_code c (n+2);
                        String.make n ' ';"}\n"]
    |CRETURN(Some(_,e)) ->
      String.concat "" [string_of_expr e "%eax";"pop %rbp\nret"]
    |CRETURN(None) ->
      String.concat "" [String.make n ' ';"CRETURN{ }\n"]
  and string_of_expr e loc_var = match e with
    |VAR(s) ->
      String.concat "" ["VAR{";s;"}"]
    |CST(p) ->
      String.concat "" ["mov $";string_of_int p;", ";loc_var;"\n"]
    |STRING(s) ->
      String.concat "" ["STRING{";s;"}"]
    |SET_VAR(s,(_,e1)) ->
      String.concat "" ["SET_VAR{";s;", ";string_of_expr e1 loc_var;"}"]
    |SET_ARRAY(s,(_,e1),(_,e2)) ->
      String.concat "" ["SET_ARRAY{";s;", ";
                        string_of_expr e1 loc_var;", ";
                        string_of_expr e2 loc_var;"}"]
    |CALL(s,l) ->
      let list=string_of_exprlist l 0 in
      String.concat "" ["CALL{";s;", ";list;"}"]
    |OP1(mop,(_,e1)) ->
      String.concat "" ["OP1{";string_of_monop mop;"{";string_of_expr e1 loc_var;"}} "]
    |OP2(bop,(_,e1),(_,e2)) ->
      String.concat "" ["OP2{";string_of_binop bop;"{";string_of_expr e1 loc_var;", ";string_of_expr e2 loc_var;"}"]
    |CMP(cop,(_,e1),(_,e2)) ->
      String.concat "" ["CMP{";string_of_cmpop cop;"{"; string_of_expr e1 loc_var;", ";string_of_expr e2 loc_var;"}}\n"]
    |EIF((_,e1),(_,e2),(_,e3)) ->
      String.concat "" ["EIF{\n";string_of_expr e1 loc_var;"\n";string_of_expr e2 loc_var;"\n";string_of_expr e3 loc_var;"\n";"}\n"]
    |ESEQ(l) -> let string=string_of_exprlist l 0 in
                String.concat "" ["ESEQ{";string;"}\n"]
  and string_of_exprlist l n = match l with
    |[] -> ""
    |(_,exp)::r -> String.concat ", " [string_of_expr exp "";string_of_exprlist r n]
  and string_of_codelist l n = match l with
    |[] -> ""
    |(_,code)::r ->
      String.concat "" [string_of_code code n;string_of_codelist r n]
  and string_of_monop mop = match mop with
    |M_MINUS    -> "M_MINUS"
    |M_NOT      -> "M_NOT"
    |M_POST_INC -> "M_POST_INC"
    |M_POST_DEC -> "M_POST_DEC"
    |M_PRE_INC  -> "M_PRE_INC"
    |M_PRE_DEC  -> "M_PRE_DEC"
  and string_of_binop bop = match bop with
    |S_MUL   -> "S_MUL"
    |S_DIV   -> "S_DIV"
    |S_MOD   -> "S_MOD"
    |S_ADD   -> "S_ADD"
    |S_SUB   -> "S_SUB"
    |S_INDEX -> "S_INDEX"
  and string_of_cmpop cop = match cop with
    |C_LT -> "C_LT"
    |C_LE -> "C_LE"
    |C_EQ -> "C_EQ"
  in
  let str,n,var_list = string_of_dec decl_list 0 in
  let final_str = String.concat "" [".global main\n";
  "main:\ncall fn_main\nmov %rax, %rdi # return value\nmov $60, %rax # syscall for return\nsyscall\n\n"
  ;str;"\n"] in
  Printf.fprintf out "%s" final_str;;
