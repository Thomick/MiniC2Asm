(*Written by Thomas MICHEL for ProjetCOCass*)

open CAST
open Genlab

let rec print_list l =
  match l with
  |[] -> ()
  |(v,did,is_local)::t -> print_string (String.concat "" [v;", "]);
    print_list t;;

let rec search_var_id s vl = match vl with
  |[] -> failwith (String.concat "" ["Indefined variable "; s])
  |(v,vid,is_local)::t -> if v=s then 
      if is_local then String.concat "" ["-";string_of_int (8*(vid+1)) ;"(%rbp)"]
      else String.concat "" ["global_";v ;"(%rip)"]
    else search_var_id s t


let rec define_global_var vl = match vl with
  |[] -> ""
  |(v,_,_)::t -> String.concat "" ["    global_";v ;": .quad 0\n";define_global_var t]

let rec gather_args arg_list count var_list =
  match arg_list with
  |[] -> "",count,var_list
  |CDECL(_,var)::t -> (let str_next, var_count_next, var_list_next =  gather_args t (count+1) ((var,count,true)::var_list) in
                       match count with
                       |0 -> (String.concat "" ["    push %rdi\n"; str_next]), var_count_next, var_list_next
                       |1 -> (String.concat "" ["    push %rsi\n"; str_next]), var_count_next, var_list_next
                       |2 -> (String.concat "" ["    push %rdx\n"; str_next]), var_count_next, var_list_next
                       |3 -> (String.concat "" ["    push %rcx\n"; str_next]), var_count_next, var_list_next
                       |4 -> (String.concat "" ["    push %r8\n"; str_next]), var_count_next, var_list_next
                       |5 -> (String.concat "" ["    push %r9\n"; str_next]), var_count_next, var_list_next
                       |_ -> (String.concat "" ["    push ";string_of_int (8*(count-4));"(%rbp)\n"; str_next]), var_count_next, var_list_next)

  |CFUN(_,_,_,_)::t -> failwith "Syntax error : can't define a function inside the argument declaration of another function"

let rec global_var_dec dl vl= 
  match dl with
  |[]->vl
  |h::t -> match h with
    |CDECL(_,var)-> global_var_dec t ((var,-1,false)::vl)
    |CFUN(_) -> global_var_dec t vl

let compile out decl_list =
  let strings_list = ref [] and long_functions = ref ["malloc";"fopen"; "atol"; "strtol"; "labs"] in
  let rec string_of_dec l n vl is_local = match l with
    |[] -> "",n,vl
    |h::suite ->
      begin
        match h with
        |CDECL(_,var) ->
          if is_local then
            string_of_dec suite (n+1) ((var,n,is_local)::vl) is_local
          else
            string_of_dec suite n vl is_local
        |CFUN(_,f,args,(_,code)) ->
          if is_local then
            failwith "Error : Functions can only be declared in the global scope"
          else
            let dec_string , f_var_cnt , f_var_list = gather_args args 0 vl in
            let cur_str = String.concat "" ["\n";f;":\n    push %rbp\n    mov %rsp, %rbp\n";
                                            dec_string;
                                            string_of_code code f_var_cnt f_var_list; string_of_code (CRETURN(None)) 0 []]
            in let l,_, _ = string_of_dec suite n vl is_local in
            String.concat "" [cur_str;l] , n, vl
      end
  and string_of_code c var_cnt var_list = match c with
    |CBLOCK(decs,code) ->
      let dec_string, new_var_cnt,new_var_list = string_of_dec decs var_cnt var_list true in
      if new_var_cnt <> 0 then
        String.concat "" [dec_string; "    sub $";string_of_int (8*(new_var_cnt-var_cnt));", %rsp\n";
                          string_of_codelist code new_var_cnt new_var_list; "    add $";string_of_int (8*(new_var_cnt-var_cnt));", %rsp\n"]
      else
        String.concat "" [dec_string;string_of_codelist code new_var_cnt new_var_list]
    |CEXPR((_,e)) ->
      String.concat "" [string_of_expr e var_cnt var_list]
    |CIF((_,e),(_,c1),(_,c2)) ->
      let label_e3 = genlab "else" and label_post = genlab "if_post" in
      String.concat "" [string_of_expr e var_cnt var_list ;"    cmp $0, %rax\n    je ";label_e3;"\n";string_of_code c1 var_cnt var_list ;
                        "    jmp "; label_post;"\n"; label_e3;":\n";string_of_code c2 var_cnt var_list ;label_post;":\n"]
    |CWHILE((_,e),(_,c)) ->
      let label_begin = genlab "while_begin" and label_end = genlab "while_end" in
      String.concat "" [label_begin;":\n";string_of_expr e var_cnt var_list ;"    cmp $0, %rax\n    je ";label_end;"\n";string_of_code c var_cnt var_list ;
                        "    jmp "; label_begin;"\n";label_end;":\n"]
    |CRETURN(Some(_,e)) ->
      String.concat "" [string_of_expr e var_cnt var_list;"    mov %rbp, %rsp\n    pop %rbp\n    ret\n"]
    |CRETURN(None) -> "    mov $0, %rax\n    mov %rbp, %rsp\n    pop %rbp\n    ret\n"
  and string_of_expr e var_cnt var_list = match e with
    |VAR(s) -> if s = "stdin" || s = "stderr" || s = "stdout" then
        String.concat "" ["    mov ";s;"(%rip), %rax\n"]
      else
        String.concat "" ["    mov ";search_var_id s var_list; ", %rax\n"]
    |CST(p) ->
      String.concat "" ["    mov $";string_of_int p;", %rax\n"]
    |STRING(s) -> (let string_name = genlab "string" in
                   strings_list := (string_name, s)::(!strings_list);
                   String.concat "" ["    lea ";string_name;"(%rip), %rax\n"])
    |SET_VAR(s,(_,e1)) ->
      let expr_str = string_of_expr e1 var_cnt var_list in
      String.concat "" [expr_str; "    mov %rax, ";search_var_id s var_list; "\n"]
    |SET_ARRAY(s,(_,e1),(_,e2)) ->
      String.concat "" [string_of_expr e1 var_cnt var_list ;"    push %rax\n";
                        string_of_expr e2 var_cnt var_list ;"    pop %rcx\n";
                        "    mov ";search_var_id s var_list;", %rdi\n";"    mov %rax, (%rdi,%rcx,8)\n"]
    |CALL(s,l) ->
      let list=set_args l var_cnt var_list and nb_args = List.length l and is_long = List.mem s (!long_functions) in
      let is_aligned = (nb_args<7 && (var_cnt mod 2 = 0)) ||(nb_args>=7 && ((var_cnt + nb_args) mod 2 = 0)) in
      let correct_begin = if is_aligned then "" else "    sub $8, %rsp\n"
      and correct_end = if is_aligned then "" else "    add $8, %rsp\n"
      and unstack = if nb_args >= 7 then String.concat "" ["    add $";string_of_int (8*(nb_args-6));", %rsp\n"] else ""
      and convert = if is_long then "" else "    movsx %eax, %rax\n" in
      String.concat "" [correct_begin;list;"    mov $0, %rax\n    call ";s;"\n";convert;unstack;correct_end]
    |OP1(mop,(_,e1)) ->(match mop with
        |M_MINUS    -> String.concat "" [string_of_expr e1 var_cnt var_list ;"    neg %rax\n"]
        |M_NOT      -> String.concat "" [string_of_expr e1 var_cnt var_list ;"    not %rax\n"]
        |M_POST_INC -> (match e1 with |VAR(s) -> String.concat "" [string_of_expr e1 var_cnt var_list ;"    incq ";search_var_id s var_list;"\n"]
                                      |OP2(S_INDEX,a,b) -> String.concat "" [string_of_expr (OP2(S_INDEX,a,b)) var_cnt var_list ;"   incq (%rdi,%rcx,8)\n"]
                                      |_ -> failwith "You can only increment variables")
        |M_POST_DEC -> (match e1 with |VAR(s) -> String.concat "" [string_of_expr e1 var_cnt var_list ;"    decq ";search_var_id s var_list;"\n"]
                                      |OP2(S_INDEX,a,b) -> String.concat "" [string_of_expr (OP2(S_INDEX,a,b)) var_cnt var_list ;"   decq (%rdi,%rcx,8)\n"]
                                      |_ -> failwith "You can only decrement variables")
        |M_PRE_INC  -> (match e1 with |VAR(s) -> String.concat "" ["    incq ";search_var_id s var_list;"\n";string_of_expr e1 var_cnt var_list]
                                      |OP2(S_INDEX,a,b) -> String.concat "" [string_of_expr (OP2(S_INDEX,a,b)) var_cnt var_list ;"   incq (%rdi,%rcx,8)\n";"   incq %rax\n"]
                                      |_ -> failwith "You can only increment variables")
        |M_PRE_DEC  -> (match e1 with |VAR(s) -> String.concat "" ["    decq ";search_var_id s var_list;"\n";string_of_expr e1 var_cnt var_list]
                                      |OP2(S_INDEX,a,b) -> String.concat "" [string_of_expr (OP2(S_INDEX,a,b)) var_cnt var_list ;"   decq (%rdi,%rcx,8)\n";"   decq %rax\n"]
                                      |_ -> failwith "You can only decrement variables"))
    |OP2(bop,(_,e1),(_,e2)) ->
      String.concat "" [string_of_expr e2 var_cnt var_list ;"    push %rax\n";string_of_expr e1 var_cnt var_list ; "    pop %rcx\n";string_of_binop bop]
    |CMP(cop,(_,e1),(_,e2)) ->
      String.concat "" [string_of_expr e2 var_cnt var_list ;"    push %rax\n";string_of_expr e1 var_cnt var_list ; "    pop %rcx\n";
                        "    cmp %rcx, %rax\n    mov $0, %rax\n";string_of_cmpop cop]
    |EIF((_,e1),(_,e2),(_,e3)) ->
      let label_e3 = genlab "if_e3" and label_post = genlab "if_post" in
      String.concat "" [string_of_expr e1 var_cnt var_list ;"    cmp $0, %rax\n    je ";label_e3;"\n";string_of_expr e2 var_cnt var_list ;
                        "    jmp "; label_post;"\n"; label_e3;":\n";string_of_expr e3 var_cnt var_list ;label_post;":\n"]
    |ESEQ(l) -> let rec seq li = 
                  match li with
                  |[] -> ""
                  |h::t -> String.concat "" [string_of_expr (e_of_expr h) var_cnt var_list ;seq t]
      in seq l
  and set_args expr_list var_cnt var_list = 
    let rec push_all el arg_cnt = 
      match el with
      |[] -> "", arg_cnt
      |(_,exp)::t -> let prev_str, nb_arg = push_all t (arg_cnt+1)
        in String.concat "" [prev_str; string_of_expr exp var_cnt var_list; "    push %rax\n"], nb_arg
    and move_to_reg nb_arg n = 
      if n>=min nb_arg 6 then ""
      else
        match n with 
        |0 -> String.concat "" ["    pop %rdi\n";move_to_reg nb_arg (n+1)]
        |1 -> String.concat "" ["    pop %rsi\n";move_to_reg nb_arg (n+1)]
        |2 -> String.concat "" ["    pop %rdx\n";move_to_reg nb_arg (n+1)]
        |3 -> String.concat "" ["    pop %rcx\n";move_to_reg nb_arg (n+1)]
        |4 -> String.concat "" ["    pop %r8\n";move_to_reg nb_arg (n+1)]
        |5 -> String.concat "" ["    pop %r9\n";move_to_reg nb_arg (n+1)]
        |_ -> failwith "This case should never happen"
    in let expr_str, nb_arg = push_all expr_list 0 
    in String.concat "" [expr_str; move_to_reg nb_arg 0]
  and string_of_codelist l var_cnt var_list = match l with
    |[] -> ""
    |(_,code)::r ->
      String.concat "" [string_of_code code var_cnt var_list;string_of_codelist r var_cnt var_list]
  and string_of_binop bop = match bop with
    |S_MUL   -> "    imul %rcx, %rax\n"
    |S_DIV   -> "    cqo\n    idiv %rcx\n"
    |S_MOD   -> "    cqo\n    idiv %rcx\n    mov %rdx, %rax\n"
    |S_ADD   -> "    add %rcx, %rax\n"
    |S_SUB   -> "    sub %rcx, %rax\n"
    |S_INDEX -> "    mov %rax, %rdi\n    mov (%rdi,%rcx,8), %rax\n"
  and string_of_cmpop cop = match cop with
    |C_LT -> "    setl %al\n"
    |C_LE -> "    setle %al\n"
    |C_EQ -> "    sete %al\n"
  in let rec add_user_functions dl =
       match dl with
       |[] -> ()
       |CFUN(_,f,_,_)::t -> (long_functions := f::(!long_functions);
                             add_user_functions t)
       |CDECL(_)::t -> add_user_functions t
  in let rec declare_string sl =
       match sl with
       |[] -> ""
       |(string_name, string_value)::t -> String.concat "" [ declare_string t; string_name; ":\n    .string ";Printf.sprintf "%S" string_value ;"\n" ]
  in (add_user_functions decl_list ;let str,n,var_list = string_of_dec decl_list 0 (global_var_dec decl_list []) false in
      let final_str = String.concat "" [".bss\n.align 8\n.data\n";define_global_var var_list;".global main\n";".text\n"; declare_string (!strings_list);str] in
      Printf.fprintf out "%s" final_str);;
