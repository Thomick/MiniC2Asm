(*Written by Thomas MICHEL for ProjetCOCass*)

open CAST
open Genlab

let compile out decl_list =
  let strings_list = ref [] and long_functions = ref ["malloc";"fopen";"atol";"strtol";"labs"] (* 64 bits functions (ie functions returning a 64 bits value)*)

  in let rec get_var_ref s vl = 
       (* returns a reference (as a string) to the variable named s from the variable list vl *)
       match vl with 
       |[] -> failwith (String.concat "" ["Indefined variable "; s])
       |(v,vid,is_local)::t -> if v=s then 
           if is_local then String.concat "" ["-";string_of_int (8*(vid+1)) ;"(%rbp)"]
           else String.concat "" ["global_";v ;"(%rip)"]
         else get_var_ref s t

  in let rec asm_of_dec l n vl is_local = 
       (* returns asm code from the declaration list l
        * n is the local variable count, vl the current variable list, is_local tells if the declaration is inside a function or not *)
       match l with
       |[] -> "",n,vl
       |h::suite ->
         begin
           match h with
           |CDECL(_,var) ->
             if is_local then
               asm_of_dec suite (n+1) ((var,n,is_local)::vl) is_local
             else
               asm_of_dec suite n vl is_local
           |CFUN(_,f,args,(_,code)) ->
             if is_local then
               failwith "Error : Functions can only be declared in the global scope"
             else
               let dec_string , f_var_cnt , f_var_list = gather_args args 0 vl in
               let cur_str = String.concat "" ["\n";f;":\n";
                                               "    push %rbp\n    mov %rsp, %rbp\n";
                                               dec_string;
                                               asm_of_code code f_var_cnt f_var_list; asm_of_code (CRETURN(None)) 0 []]
               in let l,_, _ = asm_of_dec suite n vl is_local in
               String.concat "" [cur_str;l] , n, vl
         end

  and gather_args arg_list count var_list =
    (* Returns the asm code that push all the arguments on the stack in the correct order when a function begin
     * arg_list is the list of arguments, var_list is a variable list (normally it must only contains global variables) *)
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
    |CFUN(_)::t -> failwith "Syntax error : can't define a function inside the argument declaration of another function"

  and asm_of_code c var_cnt var_list = match c with
    (* Returns asm code from the code c
     * var_cnt is the current number of local variables, var_list is a variable list*)
    |CBLOCK(decs,code) ->
      let dec_string, new_var_cnt,new_var_list = asm_of_dec decs var_cnt var_list true in
      if new_var_cnt <> 0 then
        (* Move the stack pointer just after the last local variable *)
        let allocation_str = if new_var_cnt = var_cnt then "" else String.concat "" ["    sub $"; string_of_int (8*(new_var_cnt-var_cnt)); ", %rsp\n"]
        and deallocation_str = if new_var_cnt = var_cnt then "" else String.concat "" ["    add $"; string_of_int (8*(new_var_cnt-var_cnt)); ", %rsp\n"]
        in String.concat "" [dec_string;
                             allocation_str;
                             asm_of_codelist code new_var_cnt new_var_list;
                             deallocation_str]
      else
        String.concat "" [dec_string; asm_of_codelist code new_var_cnt new_var_list]
    |CEXPR((_,e)) ->
      String.concat "" [asm_of_expr e var_cnt var_list]
    |CIF((_,e),(_,c1),(_,c2)) ->
      let label_e3 = genlab "else" and label_post = genlab "if_post" in
      String.concat "" [asm_of_expr e var_cnt var_list;
                        "    cmp $0, %rax\n    je ";label_e3;"\n";
                        asm_of_code c1 var_cnt var_list ;
                        "    jmp "; label_post;"\n";
                        label_e3;":\n"; asm_of_code c2 var_cnt var_list ;
                        label_post;":\n"]
    |CWHILE((_,e),(_,c)) ->
      let label_begin = genlab "while_begin" and label_end = genlab "while_end" in
      String.concat "" [label_begin;":\n";
                        asm_of_expr e var_cnt var_list;
                        "    cmp $0, %rax\n    je ";label_end;"\n";
                        asm_of_code c var_cnt var_list;
                        "    jmp "; label_begin;"\n";
                        label_end;":\n"]
    |CRETURN(Some(_,e)) ->
      String.concat "" [asm_of_expr e var_cnt var_list;"    leave\n    ret\n"]
    |CRETURN(None) -> "    mov $0, %rax\n    leave\n    ret\n"

  and asm_of_expr e var_cnt var_list = match e with
    (* Returns asm code from the expression e, the results of the expression is stored in the rax register
     * var_cnt is the current number of local variables, var_list is a variable list*)
    |VAR(s) -> if s = "stdin" || s = "stderr" || s = "stdout" then
        String.concat "" ["    mov ";s;"(%rip), %rax\n"]
      else
        String.concat "" ["    mov ";get_var_ref s var_list;", %rax\n"]
    |CST(p) ->
      String.concat "" ["    mov $";string_of_int p;", %rax\n"]
    |STRING(s) -> (let string_name = genlab "string" in
                   strings_list := (string_name, s)::(!strings_list);
                   String.concat "" ["    lea ";string_name;"(%rip), %rax\n"])
    |SET_VAR(s,(_,e1)) ->
      let expr_str = asm_of_expr e1 var_cnt var_list in
      String.concat "" [expr_str; "    mov %rax, ";get_var_ref s var_list;"\n"]
    |SET_ARRAY(s,(_,e1),(_,e2)) ->
      String.concat "" [asm_of_expr e1 var_cnt var_list;"    push %rax\n";
                        asm_of_expr e2 (var_cnt+1) var_list;"    pop %rcx\n";
                        "    mov ";get_var_ref s var_list;", %rdi\n";"    mov %rax, (%rdi,%rcx,8)\n"]
    |CALL(s,l) ->
      let set_args_string=set_args l var_cnt var_list and nb_args = List.length l 
      (* is the caled function a 64 bits function *)
      and is_long = List.mem s (!long_functions) in
      (* is the stack aligned with a multiple of 16 (deduced from the number of local variables)*)
      let is_aligned = (nb_args<7 && (var_cnt mod 2 = 0)) ||(nb_args>=7 && ((var_cnt + nb_args) mod 2 = 0)) in 
      (* code that correct the alignment *)
      let correct_begin = if is_aligned then "" else "    sub $8, %rsp\n"
      and correct_end = if is_aligned then "" else "    add $8, %rsp\n"
      (* code to reposition the stack pointer to where it was before pushing the arguments *)
      and unstack = if nb_args >= 7 then String.concat "" ["    add $";string_of_int (8*(nb_args-6));", %rsp\n"] else ""
      (*code to convert the return value to 64 bits if needed *)
      and convert = if is_long then "" else "    movsx %eax, %rax\n" in
      String.concat "" [correct_begin;set_args_string;
                        "    mov $0, %rax\n    call ";s;"\n";
                        convert;unstack;correct_end]
    |OP1(mop,(_,e1)) ->(match mop with
        |M_MINUS    -> String.concat "" [asm_of_expr e1 var_cnt var_list ;"    neg %rax\n"]
        |M_NOT      -> String.concat "" [asm_of_expr e1 var_cnt var_list ;"    not %rax\n"]
        |M_POST_INC -> (match e1 with |VAR(s) -> String.concat "" [asm_of_expr e1 var_cnt var_list ;
                                                                   "    incq ";get_var_ref s var_list;"\n"]
                                      |OP2(S_INDEX,a,b) -> String.concat "" [asm_of_expr (OP2(S_INDEX,a,b)) var_cnt var_list ;
                                                                             "   incq (%rdi,%rcx,8)\n"]
                                      |_ -> failwith "You can only increment variables")
        |M_POST_DEC -> (match e1 with |VAR(s) -> String.concat "" [asm_of_expr e1 var_cnt var_list ;
                                                                   "    decq ";get_var_ref s var_list;"\n"]
                                      |OP2(S_INDEX,a,b) -> String.concat "" [asm_of_expr (OP2(S_INDEX,a,b)) var_cnt var_list ;
                                                                             "   decq (%rdi,%rcx,8)\n"]
                                      |_ -> failwith "You can only decrement variables")
        |M_PRE_INC  -> (match e1 with |VAR(s) -> String.concat "" ["    incq ";get_var_ref s var_list;"\n";
                                                                   asm_of_expr e1 var_cnt var_list]
                                      |OP2(S_INDEX,a,b) -> String.concat "" [asm_of_expr (OP2(S_INDEX,a,b)) var_cnt var_list ;
                                                                             "   incq (%rdi,%rcx,8)\n";
                                                                             "   incq %rax\n"]
                                      |_ -> failwith "You can only increment variables")
        |M_PRE_DEC  -> (match e1 with |VAR(s) -> String.concat "" ["    decq ";get_var_ref s var_list;"\n";
                                                                   asm_of_expr e1 var_cnt var_list]
                                      |OP2(S_INDEX,a,b) -> String.concat "" [asm_of_expr (OP2(S_INDEX,a,b)) var_cnt var_list ;
                                                                             "   decq (%rdi,%rcx,8)\n";
                                                                             "   decq %rax\n"]
                                      |_ -> failwith "You can only decrement variables"))
    |OP2(bop,(_,e1),(_,e2)) ->
      String.concat "" [asm_of_expr e2 var_cnt var_list ;"    push %rax\n";
                        asm_of_expr e1 (var_cnt+1) var_list;
                        "    pop %rcx\n";asm_of_binop bop]
    |CMP(cop,(_,e1),(_,e2)) ->
      String.concat "" [asm_of_expr e2 var_cnt var_list ;"    push %rax\n";
                        asm_of_expr e1 (var_cnt+1) var_list ;"    pop %rcx\n";
                        "    cmp %rcx, %rax\n    mov $0, %rax\n";asm_of_cmpop cop]
    |EIF((_,e1),(_,e2),(_,e3)) ->
      let label_e3 = genlab "if_e3" and label_post = genlab "if_post" in
      String.concat "" [asm_of_expr e1 var_cnt var_list ;
                        "    cmp $0, %rax\n    je ";label_e3;"\n";
                        asm_of_expr e2 var_cnt var_list;
                        "    jmp "; label_post;"\n";
                        label_e3;":\n";asm_of_expr e3 var_cnt var_list;
                        label_post;":\n"]
    |ESEQ(l) -> let rec seq li = 
                  match li with
                  |[] -> ""
                  |h::t -> String.concat "" [asm_of_expr (e_of_expr h) var_cnt var_list ;seq t]
      in seq l

  and set_args expr_list var_cnt var_list = 
    (* Returns the code to place the arguments in the correct position (according to their order) before calling a function 
     * var_cnt is the current number of local variables, var_list is a variable list*)
    let rec push_all el arg_cnt = (* Evaluates all the expression and push them on the stack *)
      match el with
      |[] -> "", arg_cnt
      |(_,exp)::t -> let prev_str, nb_arg = push_all t (arg_cnt+1)
        in String.concat "" [prev_str; asm_of_expr exp (var_cnt+nb_arg-arg_cnt+1) var_list; "    push %rax\n"], nb_arg
    and move_to_reg nb_arg n = (* Stores the first arguments in the correct registers *)
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

  and asm_of_codelist l var_cnt var_list = (* Returns the concatenation of all the codes in the code list l *)
    match l with
    |[] -> ""
    |(_,code)::r ->
      String.concat "" [asm_of_code code var_cnt var_list;asm_of_codelist r var_cnt var_list]

  and asm_of_binop bop = (* Returns the specific command relative to the binary operation bop (registers must be correctly set beforehand) *)
    match bop with
    |S_MUL   -> "    imul %rcx, %rax\n"
    |S_DIV   -> "    cqo\n    idiv %rcx\n"
    |S_MOD   -> "    cqo\n    idiv %rcx\n    mov %rdx, %rax\n"
    |S_ADD   -> "    add %rcx, %rax\n"
    |S_SUB   -> "    sub %rcx, %rax\n"
    |S_INDEX -> "    mov %rax, %rdi\n    mov (%rdi,%rcx,8), %rax\n"

  and asm_of_cmpop cop = (* Returns the specific command relative to the comparison operation cop (rax must be correctly set beforehand) *)
    match cop with
    |C_LT -> "    setl %al\n"
    |C_LE -> "    setle %al\n"
    |C_EQ -> "    sete %al\n"

  in let rec add_user_functions dl =
       (* Add the function defined in the source file to the list of 64 bits functions *)
       match dl with
       |[] -> ()
       |CFUN(_,f,_,_)::t -> (long_functions := f::(!long_functions);
                             add_user_functions t)
       |CDECL(_)::t -> add_user_functions t

  in let rec declare_string sl =
       (* Returns the asm code for the declaration of constant strings, sl is the string list to declare *)
       match sl with
       |[] -> ""
       |(string_name, string_value)::t -> String.concat "" [declare_string t; 
                                                            string_name; ":    .string ";Printf.sprintf "%S" string_value ;"\n" ]

  in let rec append_global_var dl vl= 
       (* Appends the variables from the declaration list dl to the variable list vl and returns the result
        * it supposes that the variables from dl are in the global scope (which means they are in decl_list (argument of compile)) *)
       match dl with
       |[]->vl
       |h::t -> match h with
         |CDECL(_,var)-> append_global_var t ((var,-1,false)::vl)
         |CFUN(_) -> append_global_var t vl

  in let rec declare_global_var vl = 
       (* Returns the asm code for the declaration of global variables
        * sl is the variable list to declare (assumes that all the variables in the list are global variables) *)
       match vl with
       |[] -> ""
       |(v,_,_)::t -> String.concat "" ["    global_";v ;": .quad 0\n";declare_global_var t]
  in begin 
    add_user_functions decl_list;
    let code,n,var_list = asm_of_dec decl_list 0 (append_global_var decl_list []) false 
    in let final_str = String.concat "" [".bss\n.align 8\n.data\n";
                                         declare_global_var var_list;
                                         ".global main\n";".text\n";
                                         declare_string (!strings_list);code] 
    in Printf.fprintf out "%s" final_str 
  end;;
