open CAST

let print_declarations out dec_list =
  Format.fprintf out "Todo\n"

let print_locator out nom fl fc ll lc =
  Format.fprintf out "Todo\n"
  
let print_ast out dec_list =
  let rec string_of_dec l n = match l with
    |[] -> ""
    |h::suite ->
      let l = string_of_dec suite n in
      begin
        match h with
        |CDECL(_,var) ->
          String.concat "" [String.make n ' ';"CDECL{";"VAR{";var;"}";"}\n";l]
        |CFUN(_,f,args,(_,code)) ->
          String.concat "" [String.make n ' ';
                            "CFUN{\n";String.make (n+2) ' ';f;
                            "{\n";string_of_dec args (n+4);String.make (n+2) ' ';"}\n";
                            string_of_code code (n+2);String.make n ' ';"}\n";l]
      end
  and string_of_code c n = match c with
    |CBLOCK(decs,code) ->
      String.concat "" [String.make n ' ';
                        "CBLOCK{\n";string_of_dec decs (n+2);
                        string_of_codelist code (n+2);String.make n ' ';"}\n"]
    |CEXPR((_,e)) ->
      String.concat "" [String.make n ' ';"CEXPR{";string_of_expr e 0;"}\n"]
    |CIF((_,e),(_,c1),(_,c2)) ->
      String.concat "" [String.make n ' ';
                        "CIF{\n";
                        string_of_expr e  0;"\n";
                        string_of_code c1 0;"\n";
                        string_of_code c2 0;"\n";
                        String.make n ' ';"}\n"]
    |CWHILE((_,e),(_,c)) ->
      String.concat "" [String.make n ' ';
                        "CWHILE{\n";string_of_expr e (n+2);string_of_code c (n+2);
                        String.make n ' ';"}\n"]
    |CRETURN(Some(_,e)) ->
      String.concat "" [String.make n ' ';"CRETURN{";string_of_expr e 0;"}\n"]
    |CRETURN(None) ->
      String.concat "" [String.make n ' ';"CRETURN{ }\n"]
  and string_of_expr e n = match e with
    |VAR(s) ->
      String.concat "" ["VAR{";s;"}"]
    |CST(p) ->
      String.concat "" ["CST{";string_of_int p;"}"]
    |STRING(s) ->
      String.concat "" ["STRING{";s;"}"]
    |SET_VAR(s,(_,e1)) ->
      String.concat "" ["SET_VAR{";s;", ";string_of_expr e1 0;"}"]
    |SET_ARRAY(s,(_,e1),(_,e2)) ->
      String.concat "" ["SET_ARRAY{";s;", ";
                        string_of_expr e1 0;", ";
                        string_of_expr e2 0;"}"]
    |CALL(s,l) ->
      let list=string_of_exprlist l 0 in
      String.concat "" ["CALL{";s;", ";list;"}"]
    |OP1(mop,(_,e1)) ->
      String.concat "" ["OP1{";string_of_monop mop;"{";string_of_expr e1 0;"}} "]
    |OP2(bop,(_,e1),(_,e2)) ->
      String.concat "" ["OP2{";string_of_binop bop;"{";string_of_expr e1 0;", ";string_of_expr e2 0;"}"]
    |CMP(cop,(_,e1),(_,e2)) ->
      String.concat "" [String.make n ' ';"CMP{";string_of_cmpop cop;"{"; string_of_expr e1 0;", ";string_of_expr e2 0;"}}\n"]
    |EIF((_,e1),(_,e2),(_,e3)) ->
      String.concat "" [String.make n ' ';
                        "EIF{\n";
                        String.make (n+2) ' ';string_of_expr e1 0;"\n";
                        String.make (n+2) ' ';string_of_expr e2 0;"\n";
                        String.make (n+2) ' ';string_of_expr e3 0;"\n";
                        String.make n ' ';"}\n"]
    |ESEQ(l) -> let string=string_of_exprlist l 0 in
                String.concat "" [String.make n ' ';
                                  "ESEQ{";string;"}\n"]
  and string_of_exprlist l n = match l with
    |[] -> ""
    |(_,exp)::r -> String.concat ", " [string_of_expr exp n;string_of_exprlist r n]
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
  Format.fprintf out "%s" (string_of_dec dec_list 0);;
