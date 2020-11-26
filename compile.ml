open CAST
open Genlab

let rec print_list l =
  match l with
  |[] -> ()
  |(v,did,in_func)::t -> print_string (String.concat "" [v;", "]);
                print_list t;;

let rec search_var_id s vl = match vl with
        |[] -> failwith "Indefined variable"
        |(v,vid,in_func)::t -> if v=s then 
                                if in_func then String.concat "" ["-0x";string_of_int (8*vid) ;"(%rbp)"]
                                else String.concat "" ["global_";v ;"(%rip)"]
                      else search_var_id s t

let rec define_global_var vl = match vl with
  |[] -> ""
  |(v,_,_)::t -> String.concat "" ["    global_";v ;": .long 0\n";define_global_var t]

let compile out decl_list =
  let rec string_of_dec l n vl in_function = match l with
    |[] -> "",n,vl
    |h::suite ->
      begin
        match h with
        |CDECL(_,var) ->string_of_dec suite (n+1) ((var,n,in_function)::vl) in_function
        |CFUN(_,f,args,(_,code)) ->
          let dec_string , f_var_cnt , f_var_list = string_of_dec args 1 vl true in
          let cur_str = String.concat "" ["fn_";f;":\n    push %rbp\n    mov %rsp, %rbp\n";
                            dec_string;
                            string_of_code code f_var_cnt f_var_list]
          in let l,new_var_cnt, new_var_list = string_of_dec suite n vl in_function in
          String.concat "" [cur_str;l] , new_var_cnt, new_var_list
      end
  and string_of_code c var_cnt var_list = match c with
    |CBLOCK(decs,code) ->
      let dec_string, var_cnt,var_list = string_of_dec decs var_cnt var_list true in
      String.concat "" [dec_string;
                        string_of_codelist code var_cnt var_list]
    |CEXPR((_,e)) ->
      String.concat "" [string_of_expr e var_list ""]
    |CIF((_,e),(_,c1),(_,c2)) ->
      String.concat "" ["CIF{\n";
                        string_of_expr e var_list "";"\n";
                        string_of_code c1 var_cnt var_list;"\n";
                        string_of_code c2 var_cnt var_list;"\n";"}\n"]
    |CWHILE((_,e),(_,c)) ->
      String.concat "" ["CWHILE{\n";string_of_expr e var_list "";string_of_code c var_cnt var_list;
                        "}\n"]
    |CRETURN(Some(_,e)) ->
      String.concat "" [string_of_expr e var_list "%eax";"    pop %rbp\n    ret\n"]
    |CRETURN(None) ->
      String.concat "" ["    mov $0, %eax\n    pop %rbp\n    ret\n"]
  and string_of_expr e var_list loc_var = match e with
    |VAR(s) ->
      String.concat "" ["    mov ";search_var_id s var_list; ", ";loc_var;"\n"]
    |CST(p) ->
      String.concat "" ["    mov $";string_of_int p;", ";loc_var;"\n"]
    |STRING(s) ->
      String.concat "" ["STRING{";s;"}"]
    |SET_VAR(s,(_,e1)) ->
      let expr_str = string_of_expr e1 var_list "%rax" in
      String.concat "" [expr_str; "    mov %rax, ";search_var_id s var_list; "\n"]
    |SET_ARRAY(s,(_,e1),(_,e2)) ->
      String.concat "" ["SET_ARRAY{";s;", ";
                        string_of_expr e1 var_list loc_var;", ";
                        string_of_expr e2 var_list loc_var;"}"]
    |CALL(s,l) ->
      let list=string_of_exprlist l var_list 0 in
      String.concat "" ["CALL{";s;", ";list;"}"]
    |OP1(mop,(_,e1)) ->
      String.concat "" ["OP1{";string_of_monop mop;"{";string_of_expr e1 var_list loc_var;"}} "]
    |OP2(bop,(_,e1),(_,e2)) ->
      String.concat "" ["OP2{";string_of_binop bop;"{";string_of_expr e1 var_list loc_var;", ";string_of_expr e2 var_list loc_var;"}"]
    |CMP(cop,(_,e1),(_,e2)) ->
      String.concat "" ["CMP{";string_of_cmpop cop;"{"; string_of_expr e1 var_list loc_var;", ";string_of_expr e2 var_list loc_var;"}}\n"]
    |EIF((_,e1),(_,e2),(_,e3)) ->
      String.concat "" ["EIF{\n";string_of_expr e1 var_list loc_var;"\n";string_of_expr e2 var_list loc_var;"\n";string_of_expr e3 var_list loc_var;"\n";"}\n"]
    |ESEQ(l) -> let rec seq li = 
      match li with
        |[] -> ""
        |h::t -> String.concat "" [string_of_expr (e_of_expr h) var_list loc_var;seq t]
      in seq l
  and string_of_exprlist l var_list loc_var = match l with
    |[] -> ""
    |(_,exp)::r -> String.concat ", " [string_of_expr exp var_list "";string_of_exprlist r var_list loc_var]
  and string_of_codelist l var_cnt var_list = match l with
    |[] -> ""
    |(_,code)::r ->
      String.concat "" [string_of_code code var_cnt var_list;string_of_codelist r var_cnt var_list]
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
  let str,n,var_list = string_of_dec decl_list 1 [] false in
  let final_str = String.concat "" [".data\n.align 8\n";define_global_var var_list;".global main\n";
  "main:\n    call fn_main\n    mov %rax, %rdi\n    mov $60, %rax\n    syscall\n\n"
  ;str] in
  Printf.fprintf out "%s" final_str;;
