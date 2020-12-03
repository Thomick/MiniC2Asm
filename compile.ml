open CAST
open Genlab

let rec print_list l =
  match l with
  |[] -> ()
  |(v,did,in_func)::t -> print_string (String.concat "" [v;", "]);
    print_list t;;

let rec search_var_id s vl = match vl with
  |[] -> failwith (String.concat "" ["Indefined variable "; s])
  |(v,vid,in_func)::t -> if v=s then 
      if in_func then String.concat "" ["-";string_of_int (8*vid) ;"(%rbp)"]
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
        |CDECL(_,var) ->let nl = if in_function then n+1 else n in
          let dec_string, new_var_cnt, new_var_list = string_of_dec suite nl ((var,n,in_function)::vl) in_function
          in String.concat "" ["    push $0\n"; dec_string] , new_var_cnt,new_var_list
        |CFUN(_,f,args,(_,code)) ->
          let dec_string , f_var_cnt , f_var_list = string_of_dec args 1 vl true in
          let cur_str = String.concat "" [f;":\n    push %rbp\n    mov %rsp, %rbp\n";
                                          dec_string;
                                          string_of_code code f_var_cnt f_var_list]
          in let l,new_var_cnt, new_var_list = string_of_dec suite n vl in_function in
          String.concat "" [cur_str;l] , new_var_cnt, new_var_list
      end
  and string_of_code c var_cnt var_list = match c with
    |CBLOCK(decs,code) ->
      let dec_string, new_var_cnt,new_var_list = string_of_dec decs var_cnt var_list true in
      String.concat "" [dec_string;
                        string_of_codelist code new_var_cnt new_var_list; "    lea -";string_of_int (8*var_cnt);"(%rbp), %rsp\n"]
    |CEXPR((_,e)) ->
      String.concat "" [string_of_expr e var_list]
    |CIF((_,e),(_,c1),(_,c2)) ->
      let label_e3 = genlab "else" and label_post = genlab "if_post" in
      String.concat "" [string_of_expr e var_list ;"    cmp $0, %eax\n    je ";label_e3;"\n";string_of_code c1 var_cnt var_list ;
                        "    jmp "; label_post;"\n"; label_e3;":\n";string_of_code c2 var_cnt var_list ;label_post;":\n"]
    |CWHILE((_,e),(_,c)) ->
      let label_begin = genlab "while_begin" and label_end = genlab "while_end" in
      String.concat "" [label_begin;":\n";string_of_expr e var_list ;"    cmp $0, %eax\n    je ";label_end;"\n";string_of_code c var_cnt var_list ;
                        "    jmp "; label_begin;"\n";label_end;":\n"]
    |CRETURN(Some(_,e)) ->
      String.concat "" [string_of_expr e var_list;"    mov %rbp, %rsp\n    pop %rbp\n    ret\n"]
    |CRETURN(None) ->
      String.concat "" ["    mov $0, %rax\n    mov %rbp, %rsp\n    pop %rbp\n    ret\n"]
  and string_of_expr e var_list = match e with
    |VAR(s) ->
      String.concat "" ["    mov ";search_var_id s var_list; ", %rax\n"]
    |CST(p) ->
      String.concat "" ["    mov $";string_of_int p;", %rax\n"]
    |STRING(s) ->
      String.concat "" ["STRING{";s;"}"]
    |SET_VAR(s,(_,e1)) ->
      let expr_str = string_of_expr e1 var_list in
      String.concat "" [expr_str; "    mov %rax, ";search_var_id s var_list; "\n"]
    |SET_ARRAY(s,(_,e1),(_,e2)) ->
      String.concat "" ["SET_ARRAY{";s;", ";
                        string_of_expr e1 var_list ;", ";
                        string_of_expr e2 var_list ;"}"]
    |CALL(s,l) ->
      let list=string_of_exprlist l var_list in
      String.concat "" ["CALL{";s;", ";list;"}"]
    |OP1(mop,(_,e1)) ->
      String.concat "" [string_of_expr e1 var_list ;string_of_monop mop;]
    |OP2(bop,(_,e1),(_,e2)) ->
      String.concat "" [string_of_expr e2 var_list ;"    push %rax\n";string_of_expr e1 var_list ; "    pop %rcx\n";string_of_binop bop]
    |CMP(cop,(_,e1),(_,e2)) ->
      String.concat "" [string_of_expr e2 var_list ;"    push %rax\n";string_of_expr e1 var_list ; "    pop %rcx\n";
                        "    cmp %rcx, %rax\n    mov $0, %rax\n";string_of_cmpop cop]
    |EIF((_,e1),(_,e2),(_,e3)) ->
      let label_e3 = genlab "if_e3" and label_post = genlab "if_post" in
      String.concat "" [string_of_expr e1 var_list ;"    cmpl $0, %eax\n    je ";label_e3;"\n";string_of_expr e2 var_list ;
                        "    jmp "; label_post;"\n"; label_e3;":\n";string_of_expr e3 var_list ;label_post;":\n"]
    |ESEQ(l) -> let rec seq li = 
                  match li with
                  |[] -> ""
                  |h::t -> String.concat "" [string_of_expr (e_of_expr h) var_list ;seq t]
      in seq l
  and string_of_exprlist l var_list  = match l with
    |[] -> ""
    |(_,exp)::r -> String.concat ", " [string_of_expr exp var_list ;string_of_exprlist r var_list]
  and string_of_codelist l var_cnt var_list = match l with
    |[] -> ""
    |(_,code)::r ->
      String.concat "" [string_of_code code var_cnt var_list;string_of_codelist r var_cnt var_list]
  and string_of_monop mop = match mop with
    |M_MINUS    -> "    neg %rax\n"
    |M_NOT      -> "    not %rax\n"
    |M_POST_INC -> "M_POST_INC"
    |M_POST_DEC -> "M_POST_DEC"
    |M_PRE_INC  -> "M_PRE_INC"
    |M_PRE_DEC  -> "M_PRE_DEC"
  and string_of_binop bop = match bop with
    |S_MUL   -> "    imul %rcx, %rax\n"
    |S_DIV   -> "    cqo\n    idiv %rcx\n"
    |S_MOD   -> "    cqo\n    idiv %rcx\n    mov %rdx, %rax\n"
    |S_ADD   -> "    add %rcx, %rax\n"
    |S_SUB   -> "    sub %rcx, %rax\n"
    |S_INDEX -> "S_INDEX"
  and string_of_cmpop cop = match cop with
    |C_LT -> "    setl %al\n"
    |C_LE -> "    setle %al\n"
    |C_EQ -> "    sete %al\n"
  in
  let str,n,var_list = string_of_dec decl_list 1 [] false in
  let final_str = String.concat "" [".data\n.align 8\n";define_global_var var_list;".global main\n";str] in
  Printf.fprintf out "%s" final_str;;
