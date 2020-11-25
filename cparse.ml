type token =
  | IDENTIFIER of (string)
  | TYPE_NAME of (string)
  | CONSTANT of (int)
  | STRING_LITERAL of (string)
  | SIZEOF
  | PTR_OP
  | INC_OP
  | DEC_OP
  | LEFT_OP
  | RIGHT_OP
  | LE_OP
  | GE_OP
  | EQ_OP
  | NE_OP
  | AND_OP
  | OR_OP
  | MUL_ASSIGN
  | DIV_ASSIGN
  | MOD_ASSIGN
  | ADD_ASSIGN
  | SUB_ASSIGN
  | LEFT_ASSIGN
  | RIGHT_ASSIGN
  | AND_ASSIGN
  | XOR_ASSIGN
  | OR_ASSIGN
  | SEMI_CHR
  | OPEN_BRACE_CHR
  | CLOSE_BRACE_CHR
  | COMMA_CHR
  | COLON_CHR
  | EQ_CHR
  | OPEN_PAREN_CHR
  | CLOSE_PAREN_CHR
  | OPEN_BRACKET_CHR
  | CLOSE_BRACKET_CHR
  | DOT_CHR
  | AND_CHR
  | OR_CHR
  | XOR_CHR
  | BANG_CHR
  | TILDE_CHR
  | ADD_CHR
  | SUB_CHR
  | STAR_CHR
  | DIV_CHR
  | MOD_CHR
  | OPEN_ANGLE_CHR
  | CLOSE_ANGLE_CHR
  | QUES_CHR
  | TYPEDEF
  | EXTERN
  | STATIC
  | AUTO
  | REGISTER
  | CHAR
  | SHORT
  | INTEGER
  | LONG
  | SIGNED
  | UNSIGNED
  | FLOATING
  | DOUBLE
  | CONST
  | VOLATILE
  | VOID
  | STRUCT
  | UNION
  | ENUM
  | ELLIPSIS
  | EOF
  | CASE
  | DEFAULT
  | IF
  | ELSE
  | SWITCH
  | WHILE
  | DO
  | FOR
  | GOTO
  | CONTINUE
  | BREAK
  | RETURN
  | ASM

open Parsing;;
let _ = parse_error;;
# 2 "cparse.mly"

(*
 * Copyright (c) 2005 by Laboratoire Spécification et Vérification
 * (LSV), UMR 8643 CNRS & ENS Cachan.
 * Written by Jean Goubault-Larrecq.  Derived from the csur project.
 *
 * Permission is granted to anyone to use this software for any
 * purpose on any computer system, and to redistribute it freely,
 * subject to the following restrictions:
 *
 * 1. Neither the author nor its employer is responsible for the
 *    consequences of use of this software, no matter how awful, even if
 *    they arise from defects in it.
 *
 * 2. The origin of this software must not be misrepresented, either
 *    by explicit claim or by omission.
 *
 * 3. Altered versions must be plainly marked as such, and must not
 *    be misrepresented as being the original software.
 *
 * 4. This software is restricted to non-commercial use only.  Commercial
 *    use is subject to a specific license, obtainable from LSV.
 * 
 *)

(* Analyse grammaticale d'un sous-ensemble (tres) reduit de C. *)

open CAST
open Error

let parse_error msg =
    fatal (Some (getloc ())) msg

# 124 "cparse.ml"
let yytransl_const = [|
  261 (* SIZEOF *);
  262 (* PTR_OP *);
  263 (* INC_OP *);
  264 (* DEC_OP *);
  265 (* LEFT_OP *);
  266 (* RIGHT_OP *);
  267 (* LE_OP *);
  268 (* GE_OP *);
  269 (* EQ_OP *);
  270 (* NE_OP *);
  271 (* AND_OP *);
  272 (* OR_OP *);
  273 (* MUL_ASSIGN *);
  274 (* DIV_ASSIGN *);
  275 (* MOD_ASSIGN *);
  276 (* ADD_ASSIGN *);
  277 (* SUB_ASSIGN *);
  278 (* LEFT_ASSIGN *);
  279 (* RIGHT_ASSIGN *);
  280 (* AND_ASSIGN *);
  281 (* XOR_ASSIGN *);
  282 (* OR_ASSIGN *);
  283 (* SEMI_CHR *);
  284 (* OPEN_BRACE_CHR *);
  285 (* CLOSE_BRACE_CHR *);
  286 (* COMMA_CHR *);
  287 (* COLON_CHR *);
  288 (* EQ_CHR *);
  289 (* OPEN_PAREN_CHR *);
  290 (* CLOSE_PAREN_CHR *);
  291 (* OPEN_BRACKET_CHR *);
  292 (* CLOSE_BRACKET_CHR *);
  293 (* DOT_CHR *);
  294 (* AND_CHR *);
  295 (* OR_CHR *);
  296 (* XOR_CHR *);
  297 (* BANG_CHR *);
  298 (* TILDE_CHR *);
  299 (* ADD_CHR *);
  300 (* SUB_CHR *);
  301 (* STAR_CHR *);
  302 (* DIV_CHR *);
  303 (* MOD_CHR *);
  304 (* OPEN_ANGLE_CHR *);
  305 (* CLOSE_ANGLE_CHR *);
  306 (* QUES_CHR *);
  307 (* TYPEDEF *);
  308 (* EXTERN *);
  309 (* STATIC *);
  310 (* AUTO *);
  311 (* REGISTER *);
  312 (* CHAR *);
  313 (* SHORT *);
  314 (* INTEGER *);
  315 (* LONG *);
  316 (* SIGNED *);
  317 (* UNSIGNED *);
  318 (* FLOATING *);
  319 (* DOUBLE *);
  320 (* CONST *);
  321 (* VOLATILE *);
  322 (* VOID *);
  323 (* STRUCT *);
  324 (* UNION *);
  325 (* ENUM *);
  326 (* ELLIPSIS *);
    0 (* EOF *);
  327 (* CASE *);
  328 (* DEFAULT *);
  329 (* IF *);
  330 (* ELSE *);
  331 (* SWITCH *);
  332 (* WHILE *);
  333 (* DO *);
  334 (* FOR *);
  335 (* GOTO *);
  336 (* CONTINUE *);
  337 (* BREAK *);
  338 (* RETURN *);
  339 (* ASM *);
    0|]

let yytransl_block = [|
  257 (* IDENTIFIER *);
  258 (* TYPE_NAME *);
  259 (* CONSTANT *);
  260 (* STRING_LITERAL *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\002\000\004\000\003\000\007\000\008\000\
\005\000\005\000\009\000\010\000\011\000\011\000\011\000\011\000\
\011\000\011\000\014\000\014\000\016\000\016\000\016\000\016\000\
\017\000\017\000\017\000\017\000\019\000\020\000\021\000\022\000\
\013\000\018\000\023\000\023\000\023\000\023\000\024\000\024\000\
\024\000\025\000\026\000\026\000\026\000\026\000\026\000\027\000\
\027\000\027\000\028\000\029\000\030\000\031\000\031\000\032\000\
\032\000\033\000\033\000\015\000\015\000\006\000\006\000\034\000\
\036\000\036\000\037\000\037\000\038\000\039\000\035\000\035\000\
\035\000\012\000\040\000\040\000\040\000\040\000\040\000\046\000\
\047\000\041\000\041\000\041\000\041\000\049\000\049\000\048\000\
\048\000\042\000\042\000\050\000\051\000\043\000\043\000\052\000\
\053\000\044\000\044\000\044\000\054\000\045\000\045\000\001\000\
\001\000\001\000\055\000\055\000\057\000\058\000\058\000\059\000\
\059\000\060\000\060\000\061\000\056\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\003\000\001\000\001\000\001\000\001\000\
\001\000\002\000\001\000\001\000\001\000\004\000\003\000\004\000\
\002\000\002\000\001\000\003\000\001\000\002\000\002\000\002\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\003\000\003\000\003\000\001\000\003\000\
\003\000\001\000\001\000\003\000\003\000\003\000\003\000\001\000\
\003\000\003\000\001\000\001\000\001\000\001\000\003\000\001\000\
\003\000\001\000\005\000\001\000\003\000\001\000\003\000\003\000\
\000\000\001\000\001\000\003\000\001\000\001\000\001\000\002\000\
\002\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\002\000\003\000\003\000\004\000\001\000\002\000\001\000\
\002\000\001\000\002\000\001\000\001\000\005\000\007\000\001\000\
\001\000\005\000\006\000\007\000\001\000\002\000\003\000\001\000\
\002\000\001\000\001\000\001\000\002\000\001\000\003\000\001\000\
\003\000\002\000\003\000\003\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\071\000\106\000\000\000\108\000\000\000\
\104\000\107\000\000\000\072\000\105\000\006\000\073\000\000\000\
\000\000\000\000\067\000\069\000\007\000\080\000\117\000\000\000\
\000\000\116\000\064\000\000\000\005\000\000\000\011\000\012\000\
\092\000\008\000\000\000\031\000\032\000\029\000\030\000\093\000\
\096\000\097\000\101\000\013\000\000\000\002\000\003\000\000\000\
\081\000\000\000\000\000\000\000\062\000\000\000\000\000\035\000\
\025\000\026\000\027\000\028\000\000\000\000\000\043\000\000\000\
\000\000\052\000\053\000\054\000\000\000\000\000\060\000\086\000\
\000\000\088\000\075\000\076\000\077\000\078\000\079\000\082\000\
\000\000\000\000\090\000\000\000\000\000\000\000\000\000\114\000\
\000\000\110\000\000\000\000\000\070\000\068\000\010\000\000\000\
\000\000\091\000\000\000\022\000\023\000\000\000\017\000\018\000\
\000\000\034\000\024\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\089\000\083\000\087\000\084\000\000\000\000\000\000\000\
\000\000\102\000\000\000\109\000\000\000\115\000\004\000\033\000\
\015\000\000\000\019\000\063\000\000\000\061\000\036\000\037\000\
\038\000\000\000\000\000\046\000\047\000\044\000\045\000\000\000\
\000\000\055\000\000\000\000\000\085\000\000\000\000\000\000\000\
\103\000\113\000\111\000\000\000\016\000\074\000\014\000\000\000\
\000\000\000\000\000\000\020\000\059\000\000\000\098\000\000\000\
\000\000\000\000\000\000\099\000\095\000\100\000"

let yydgoto = "\002\000\
\006\000\044\000\045\000\046\000\047\000\048\000\022\000\049\000\
\050\000\051\000\052\000\167\000\137\000\138\000\053\000\054\000\
\055\000\056\000\057\000\058\000\059\000\060\000\061\000\062\000\
\063\000\064\000\065\000\066\000\067\000\068\000\069\000\070\000\
\071\000\007\000\008\000\017\000\018\000\019\000\020\000\074\000\
\075\000\076\000\077\000\078\000\079\000\024\000\080\000\081\000\
\082\000\083\000\084\000\085\000\086\000\087\000\009\000\010\000\
\090\000\091\000\092\000\026\000\011\000"

let yysindex = "\011\000\
\001\000\000\000\249\254\000\000\000\000\232\254\000\000\004\255\
\000\000\000\000\012\255\000\000\000\000\000\000\000\000\015\255\
\023\255\028\255\000\000\000\000\000\000\000\000\000\000\081\255\
\057\255\000\000\000\000\089\255\000\000\079\255\000\000\000\000\
\000\000\000\000\038\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\063\255\000\000\000\000\243\254\
\000\000\038\000\038\000\011\255\000\000\069\255\038\000\000\000\
\000\000\000\000\000\000\000\000\073\255\104\255\000\000\094\255\
\138\255\000\000\000\000\000\000\092\255\247\254\000\000\000\000\
\004\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\137\255\081\255\000\000\123\255\125\255\129\255\249\255\000\000\
\004\255\000\000\097\255\143\255\000\000\000\000\000\000\009\255\
\022\255\000\000\038\000\000\000\000\000\038\000\000\000\000\000\
\038\000\000\000\000\000\038\000\038\000\038\000\038\000\038\000\
\038\000\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
\038\000\000\000\000\000\000\000\000\000\137\255\038\000\038\000\
\111\000\000\000\253\254\000\000\233\254\000\000\000\000\000\000\
\000\000\027\255\000\000\000\000\001\255\000\000\000\000\000\000\
\000\000\073\255\073\255\000\000\000\000\000\000\000\000\094\255\
\094\255\000\000\092\255\130\255\000\000\082\255\087\255\111\000\
\000\000\000\000\000\000\038\000\000\000\000\000\000\000\038\000\
\201\255\201\255\022\255\000\000\000\000\113\255\000\000\087\255\
\201\255\201\255\201\255\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\188\000\000\000\167\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\099\255\
\000\000\168\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\017\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\061\000\000\000\000\000\000\000\
\000\000\000\000\000\000\115\000\000\000\155\000\000\000\000\000\
\000\000\000\000\000\000\000\000\181\000\119\255\000\000\086\000\
\033\001\000\000\000\000\000\000\046\001\155\255\000\000\000\000\
\167\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\164\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\207\000\233\000\000\000\000\000\000\000\000\000\001\001\
\025\001\000\000\054\001\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\189\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\008\000\000\000\169\000\221\255\000\000\000\000\
\148\000\149\000\000\000\000\000\139\255\000\000\179\255\216\255\
\000\000\246\255\000\000\000\000\000\000\000\000\064\000\000\000\
\058\000\066\000\000\000\000\000\000\000\084\000\087\000\000\000\
\043\000\236\255\234\255\000\000\000\000\178\000\123\000\181\255\
\203\000\140\255\000\000\000\000\000\000\000\000\183\255\138\000\
\000\000\000\000\000\000\000\000\000\000\000\000\215\000\000\000\
\090\000\000\000\000\000\000\000\000\000"

let yytablesize = 616
let yytable = "\096\000\
\005\000\073\000\089\000\072\000\014\000\122\000\120\000\123\000\
\125\000\100\000\101\000\001\000\160\000\098\000\106\000\016\000\
\099\000\031\000\032\000\139\000\165\000\140\000\014\000\161\000\
\029\000\030\000\099\000\142\000\031\000\032\000\099\000\003\000\
\003\000\004\000\004\000\093\000\166\000\012\000\099\000\021\000\
\121\000\170\000\135\000\171\000\107\000\102\000\162\000\025\000\
\015\000\027\000\122\000\131\000\157\000\177\000\035\000\136\000\
\164\000\028\000\179\000\073\000\136\000\124\000\036\000\037\000\
\038\000\039\000\141\000\106\000\106\000\106\000\106\000\106\000\
\106\000\106\000\106\000\106\000\106\000\106\000\106\000\106\000\
\093\000\014\000\030\000\029\000\030\000\156\000\172\000\031\000\
\032\000\014\000\088\000\158\000\159\000\174\000\175\000\097\000\
\093\000\143\000\144\000\145\000\105\000\180\000\181\000\182\000\
\113\000\114\000\119\000\033\000\021\000\034\000\089\000\099\000\
\003\000\035\000\004\000\169\000\099\000\108\000\109\000\110\000\
\136\000\036\000\037\000\038\000\039\000\070\000\133\000\106\000\
\070\000\042\000\042\000\042\000\042\000\042\000\042\000\176\000\
\003\000\014\000\004\000\029\000\030\000\115\000\116\000\031\000\
\032\000\042\000\111\000\112\000\042\000\042\000\117\000\118\000\
\042\000\040\000\042\000\127\000\041\000\128\000\042\000\099\000\
\168\000\129\000\043\000\033\000\021\000\034\000\042\000\042\000\
\042\000\035\000\148\000\149\000\150\000\151\000\146\000\147\000\
\134\000\036\000\037\000\038\000\039\000\058\000\152\000\153\000\
\058\000\058\000\178\000\118\000\058\000\094\000\058\000\094\000\
\094\000\065\000\066\000\094\000\094\000\112\000\095\000\103\000\
\104\000\014\000\154\000\029\000\030\000\094\000\155\000\031\000\
\032\000\040\000\173\000\132\000\041\000\023\000\042\000\094\000\
\094\000\094\000\043\000\126\000\013\000\094\000\163\000\000\000\
\000\000\000\000\000\000\033\000\021\000\094\000\094\000\094\000\
\094\000\035\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\036\000\037\000\038\000\039\000\000\000\000\000\000\000\
\000\000\014\000\000\000\029\000\030\000\000\000\000\000\031\000\
\032\000\000\000\000\000\000\000\000\000\094\000\000\000\000\000\
\094\000\000\000\094\000\000\000\000\000\000\000\094\000\000\000\
\000\000\040\000\000\000\130\000\041\000\000\000\042\000\009\000\
\009\000\035\000\043\000\009\000\009\000\009\000\009\000\009\000\
\009\000\036\000\037\000\038\000\039\000\000\000\014\000\000\000\
\029\000\030\000\000\000\009\000\031\000\032\000\009\000\009\000\
\009\000\000\000\009\000\009\000\009\000\000\000\000\000\000\000\
\003\000\000\000\004\000\009\000\009\000\009\000\009\000\009\000\
\009\000\009\000\009\000\001\000\001\000\000\000\035\000\001\000\
\001\000\001\000\001\000\001\000\001\000\000\000\036\000\037\000\
\038\000\039\000\000\000\000\000\000\000\000\000\000\000\001\000\
\000\000\000\000\001\000\001\000\001\000\000\000\001\000\001\000\
\001\000\000\000\048\000\048\000\048\000\048\000\000\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\014\000\
\048\000\029\000\030\000\048\000\048\000\031\000\032\000\048\000\
\000\000\048\000\000\000\000\000\000\000\021\000\021\000\021\000\
\021\000\021\000\021\000\000\000\000\000\000\000\000\000\048\000\
\000\000\033\000\000\000\000\000\000\000\021\000\000\000\035\000\
\021\000\021\000\021\000\000\000\021\000\000\000\021\000\036\000\
\037\000\038\000\039\000\000\000\000\000\021\000\021\000\021\000\
\021\000\021\000\021\000\021\000\021\000\034\000\034\000\034\000\
\034\000\034\000\034\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\034\000\000\000\000\000\
\034\000\034\000\000\000\000\000\034\000\000\000\034\000\039\000\
\039\000\039\000\039\000\039\000\039\000\034\000\034\000\034\000\
\034\000\034\000\034\000\034\000\034\000\000\000\000\000\039\000\
\000\000\000\000\039\000\039\000\000\000\000\000\039\000\000\000\
\039\000\040\000\040\000\040\000\040\000\040\000\040\000\039\000\
\039\000\000\000\000\000\000\000\039\000\039\000\039\000\000\000\
\000\000\040\000\000\000\000\000\040\000\040\000\000\000\000\000\
\040\000\000\000\040\000\041\000\041\000\041\000\041\000\041\000\
\041\000\040\000\040\000\000\000\000\000\000\000\040\000\040\000\
\040\000\000\000\000\000\041\000\000\000\000\000\041\000\041\000\
\000\000\000\000\041\000\000\000\041\000\049\000\049\000\049\000\
\049\000\000\000\000\000\041\000\041\000\000\000\000\000\000\000\
\041\000\041\000\041\000\049\000\000\000\000\000\049\000\049\000\
\000\000\000\000\049\000\000\000\049\000\050\000\050\000\050\000\
\050\000\000\000\000\000\000\000\000\000\000\000\000\000\051\000\
\051\000\000\000\049\000\050\000\000\000\000\000\050\000\050\000\
\000\000\000\000\050\000\051\000\050\000\056\000\051\000\051\000\
\000\000\000\000\051\000\000\000\051\000\057\000\000\000\000\000\
\056\000\000\000\050\000\056\000\056\000\000\000\000\000\056\000\
\057\000\056\000\051\000\057\000\057\000\000\000\000\000\057\000\
\000\000\057\000\000\000\000\000\000\000\000\000\000\000\056\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\057\000"

let yycheck = "\035\000\
\000\000\024\000\025\000\024\000\001\001\081\000\016\001\081\000\
\082\000\050\000\051\000\001\000\129\000\027\001\055\000\008\000\
\030\001\007\001\008\001\097\000\138\000\099\000\001\001\027\001\
\003\001\004\001\030\001\105\000\007\001\008\001\030\001\056\001\
\056\001\058\001\058\001\028\000\036\001\045\001\030\001\028\001\
\050\001\159\000\034\001\160\000\055\000\035\001\070\001\033\001\
\045\001\027\001\126\000\087\000\126\000\171\000\033\001\034\001\
\030\001\030\001\176\000\082\000\034\001\082\000\041\001\042\001\
\043\001\044\001\102\000\108\000\109\000\110\000\111\000\112\000\
\113\000\114\000\115\000\116\000\117\000\118\000\119\000\120\000\
\073\000\001\001\004\001\003\001\004\001\121\000\164\000\007\001\
\008\001\001\001\034\001\127\000\128\000\169\000\170\000\033\001\
\089\000\108\000\109\000\110\000\032\001\177\000\178\000\179\000\
\011\001\012\001\015\001\027\001\028\001\029\001\133\000\030\001\
\056\001\033\001\058\001\034\001\030\001\045\001\046\001\047\001\
\034\001\041\001\042\001\043\001\044\001\027\001\030\001\168\000\
\030\001\011\001\012\001\013\001\014\001\015\001\016\001\171\000\
\056\001\001\001\058\001\003\001\004\001\048\001\049\001\007\001\
\008\001\027\001\043\001\044\001\030\001\031\001\013\001\014\001\
\034\001\073\001\036\001\033\001\076\001\033\001\078\001\030\001\
\031\001\033\001\082\001\027\001\028\001\029\001\048\001\049\001\
\050\001\033\001\113\000\114\000\115\000\116\000\111\000\112\000\
\034\001\041\001\042\001\043\001\044\001\027\001\117\000\118\000\
\030\001\031\001\074\001\000\000\034\001\001\001\036\001\003\001\
\004\001\027\001\027\001\007\001\008\001\034\001\030\000\052\000\
\052\000\001\001\119\000\003\001\004\001\028\000\120\000\007\001\
\008\001\073\001\168\000\089\000\076\001\011\000\078\001\027\001\
\028\001\029\001\082\001\082\000\006\000\033\001\133\000\255\255\
\255\255\255\255\255\255\027\001\028\001\041\001\042\001\043\001\
\044\001\033\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\041\001\042\001\043\001\044\001\255\255\255\255\255\255\
\255\255\001\001\255\255\003\001\004\001\255\255\255\255\007\001\
\008\001\255\255\255\255\255\255\255\255\073\001\255\255\255\255\
\076\001\255\255\078\001\255\255\255\255\255\255\082\001\255\255\
\255\255\073\001\255\255\027\001\076\001\255\255\078\001\007\001\
\008\001\033\001\082\001\011\001\012\001\013\001\014\001\015\001\
\016\001\041\001\042\001\043\001\044\001\255\255\001\001\255\255\
\003\001\004\001\255\255\027\001\007\001\008\001\030\001\031\001\
\032\001\255\255\034\001\035\001\036\001\255\255\255\255\255\255\
\056\001\255\255\058\001\043\001\044\001\045\001\046\001\047\001\
\048\001\049\001\050\001\007\001\008\001\255\255\033\001\011\001\
\012\001\013\001\014\001\015\001\016\001\255\255\041\001\042\001\
\043\001\044\001\255\255\255\255\255\255\255\255\255\255\027\001\
\255\255\255\255\030\001\031\001\032\001\255\255\034\001\035\001\
\036\001\255\255\013\001\014\001\015\001\016\001\255\255\043\001\
\044\001\045\001\046\001\047\001\048\001\049\001\050\001\001\001\
\027\001\003\001\004\001\030\001\031\001\007\001\008\001\034\001\
\255\255\036\001\255\255\255\255\255\255\011\001\012\001\013\001\
\014\001\015\001\016\001\255\255\255\255\255\255\255\255\050\001\
\255\255\027\001\255\255\255\255\255\255\027\001\255\255\033\001\
\030\001\031\001\032\001\255\255\034\001\255\255\036\001\041\001\
\042\001\043\001\044\001\255\255\255\255\043\001\044\001\045\001\
\046\001\047\001\048\001\049\001\050\001\011\001\012\001\013\001\
\014\001\015\001\016\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\027\001\255\255\255\255\
\030\001\031\001\255\255\255\255\034\001\255\255\036\001\011\001\
\012\001\013\001\014\001\015\001\016\001\043\001\044\001\045\001\
\046\001\047\001\048\001\049\001\050\001\255\255\255\255\027\001\
\255\255\255\255\030\001\031\001\255\255\255\255\034\001\255\255\
\036\001\011\001\012\001\013\001\014\001\015\001\016\001\043\001\
\044\001\255\255\255\255\255\255\048\001\049\001\050\001\255\255\
\255\255\027\001\255\255\255\255\030\001\031\001\255\255\255\255\
\034\001\255\255\036\001\011\001\012\001\013\001\014\001\015\001\
\016\001\043\001\044\001\255\255\255\255\255\255\048\001\049\001\
\050\001\255\255\255\255\027\001\255\255\255\255\030\001\031\001\
\255\255\255\255\034\001\255\255\036\001\013\001\014\001\015\001\
\016\001\255\255\255\255\043\001\044\001\255\255\255\255\255\255\
\048\001\049\001\050\001\027\001\255\255\255\255\030\001\031\001\
\255\255\255\255\034\001\255\255\036\001\013\001\014\001\015\001\
\016\001\255\255\255\255\255\255\255\255\255\255\255\255\015\001\
\016\001\255\255\050\001\027\001\255\255\255\255\030\001\031\001\
\255\255\255\255\034\001\027\001\036\001\016\001\030\001\031\001\
\255\255\255\255\034\001\255\255\036\001\016\001\255\255\255\255\
\027\001\255\255\050\001\030\001\031\001\255\255\255\255\034\001\
\027\001\036\001\050\001\030\001\031\001\255\255\255\255\034\001\
\255\255\036\001\255\255\255\255\255\255\255\255\255\255\050\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\050\001"

let yynames_const = "\
  SIZEOF\000\
  PTR_OP\000\
  INC_OP\000\
  DEC_OP\000\
  LEFT_OP\000\
  RIGHT_OP\000\
  LE_OP\000\
  GE_OP\000\
  EQ_OP\000\
  NE_OP\000\
  AND_OP\000\
  OR_OP\000\
  MUL_ASSIGN\000\
  DIV_ASSIGN\000\
  MOD_ASSIGN\000\
  ADD_ASSIGN\000\
  SUB_ASSIGN\000\
  LEFT_ASSIGN\000\
  RIGHT_ASSIGN\000\
  AND_ASSIGN\000\
  XOR_ASSIGN\000\
  OR_ASSIGN\000\
  SEMI_CHR\000\
  OPEN_BRACE_CHR\000\
  CLOSE_BRACE_CHR\000\
  COMMA_CHR\000\
  COLON_CHR\000\
  EQ_CHR\000\
  OPEN_PAREN_CHR\000\
  CLOSE_PAREN_CHR\000\
  OPEN_BRACKET_CHR\000\
  CLOSE_BRACKET_CHR\000\
  DOT_CHR\000\
  AND_CHR\000\
  OR_CHR\000\
  XOR_CHR\000\
  BANG_CHR\000\
  TILDE_CHR\000\
  ADD_CHR\000\
  SUB_CHR\000\
  STAR_CHR\000\
  DIV_CHR\000\
  MOD_CHR\000\
  OPEN_ANGLE_CHR\000\
  CLOSE_ANGLE_CHR\000\
  QUES_CHR\000\
  TYPEDEF\000\
  EXTERN\000\
  STATIC\000\
  AUTO\000\
  REGISTER\000\
  CHAR\000\
  SHORT\000\
  INTEGER\000\
  LONG\000\
  SIGNED\000\
  UNSIGNED\000\
  FLOATING\000\
  DOUBLE\000\
  CONST\000\
  VOLATILE\000\
  VOID\000\
  STRUCT\000\
  UNION\000\
  ENUM\000\
  ELLIPSIS\000\
  EOF\000\
  CASE\000\
  DEFAULT\000\
  IF\000\
  ELSE\000\
  SWITCH\000\
  WHILE\000\
  DO\000\
  FOR\000\
  GOTO\000\
  CONTINUE\000\
  BREAK\000\
  RETURN\000\
  ASM\000\
  "

let yynames_block = "\
  IDENTIFIER\000\
  TYPE_NAME\000\
  CONSTANT\000\
  STRING_LITERAL\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 62 "cparse.mly"
                     ( let loc, var = _1 in loc, VAR var )
# 600 "cparse.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'constant) in
    Obj.repr(
# 63 "cparse.mly"
                   ( let loc, cst = _1 in loc, CST cst )
# 607 "cparse.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'string_literal) in
    Obj.repr(
# 64 "cparse.mly"
                         ( let loc, s = _1 in loc, STRING s )
# 614 "cparse.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 65 "cparse.mly"
                                                    ( _2 )
# 621 "cparse.ml"
               : 'primary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 68 "cparse.mly"
                    ( getloc (), _1 )
# 628 "cparse.ml"
               : 'constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 70 "cparse.mly"
                              ( getloc (), _1 )
# 635 "cparse.ml"
               : 'identifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 71 "cparse.mly"
                              ( getloc () )
# 641 "cparse.ml"
               : 'open_brace))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "cparse.mly"
                              ( getloc () )
# 647 "cparse.ml"
               : 'close_brace))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 75 "cparse.mly"
                         ( getloc (), _1 )
# 654 "cparse.ml"
               : 'string_literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'string_literal) in
    Obj.repr(
# 77 "cparse.mly"
            ( 
              let l, s = _2 in
              let s2 = _1 in
              (getloc (), s2^s)
            )
# 666 "cparse.ml"
               : 'string_literal))
; (fun __caml_parser_env ->
    Obj.repr(
# 83 "cparse.mly"
                ( getloc () )
# 672 "cparse.ml"
               : 'inc_op))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "cparse.mly"
                ( getloc () )
# 678 "cparse.ml"
               : 'dec_op))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'primary_expression) in
    Obj.repr(
# 87 "cparse.mly"
                             ( _1 )
# 685 "cparse.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'postfix_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'close_bracket) in
    Obj.repr(
# 89 "cparse.mly"
 ( sup_locator (loc_of_expr _1) _4, OP2 (S_INDEX, _1, _3) )
# 694 "cparse.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'close_paren) in
    Obj.repr(
# 91 "cparse.mly"
 ( let loc, var = _1 in
	  let loc1 = sup_locator loc _3 in
	    loc1, CALL (var, [])
	)
# 705 "cparse.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'argument_expression_list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'close_paren) in
    Obj.repr(
# 96 "cparse.mly"
 ( let loc, var = _1 in
	  let loc1 = sup_locator loc _4 in
	    loc1, CALL (var, List.rev _3)
	)
# 717 "cparse.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'postfix_expression) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'inc_op) in
    Obj.repr(
# 101 "cparse.mly"
 ( sup_locator (loc_of_expr _1) _2, OP1 (M_POST_INC, _1) )
# 725 "cparse.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'postfix_expression) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec_op) in
    Obj.repr(
# 103 "cparse.mly"
 ( sup_locator (loc_of_expr _1) _2, OP1 (M_POST_DEC, _1) )
# 733 "cparse.ml"
               : 'postfix_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 109 "cparse.mly"
                                ( [_1] )
# 740 "cparse.ml"
               : 'argument_expression_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'argument_expression_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 110 "cparse.mly"
                                                                   ( 
          _3 :: _1 )
# 749 "cparse.ml"
               : 'argument_expression_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'postfix_expression) in
    Obj.repr(
# 115 "cparse.mly"
                             ( _1 )
# 756 "cparse.ml"
               : 'unary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'inc_op) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expression) in
    Obj.repr(
# 117 "cparse.mly"
 ( sup_locator _1 (loc_of_expr _2), OP1 (M_PRE_INC, _2) )
# 764 "cparse.ml"
               : 'unary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'dec_op) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expression) in
    Obj.repr(
# 119 "cparse.mly"
 ( sup_locator _1 (loc_of_expr _2), OP1 (M_PRE_DEC, _2) )
# 772 "cparse.ml"
               : 'unary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'unary_operator) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 121 "cparse.mly"
 ( 
          let loc, c = _1 in
          let loc' = sup_locator loc (loc_of_expr _2) in
	  match c with
	      ADD_CHR -> _2
	    | SUB_CHR -> loc', OP1 (M_MINUS, _2)
	    | BANG_CHR -> loc', EIF (_2, (loc', CST 0), (loc', CST 1))
            | TILDE_CHR -> loc', OP1 (M_NOT, _2)
	    | _ -> (Error.error (Some loc) "unknown unary operator";
		     loc, CST 0) )
# 789 "cparse.ml"
               : 'unary_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'add_chr) in
    Obj.repr(
# 134 "cparse.mly"
                    ( _1 )
# 796 "cparse.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sub_chr) in
    Obj.repr(
# 135 "cparse.mly"
                    ( _1 )
# 803 "cparse.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bang_chr) in
    Obj.repr(
# 136 "cparse.mly"
                    ( _1 )
# 810 "cparse.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tilde_chr) in
    Obj.repr(
# 137 "cparse.mly"
                    ( _1 )
# 817 "cparse.ml"
               : 'unary_operator))
; (fun __caml_parser_env ->
    Obj.repr(
# 140 "cparse.mly"
                        ( getloc (), ADD_CHR   )
# 823 "cparse.ml"
               : 'add_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 141 "cparse.mly"
                        ( getloc (), SUB_CHR   )
# 829 "cparse.ml"
               : 'sub_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 142 "cparse.mly"
                        ( getloc (), BANG_CHR  )
# 835 "cparse.ml"
               : 'bang_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 143 "cparse.mly"
                        ( getloc (), TILDE_CHR )
# 841 "cparse.ml"
               : 'tilde_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 145 "cparse.mly"
                              ( getloc () )
# 847 "cparse.ml"
               : 'close_paren))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expression) in
    Obj.repr(
# 148 "cparse.mly"
                           ( _1 )
# 854 "cparse.ml"
               : 'cast_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 152 "cparse.mly"
                          ( _1 )
# 861 "cparse.ml"
               : 'multiplicative_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'multiplicative_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 154 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  OP2 (S_MUL, _1, _3)
	)
# 871 "cparse.ml"
               : 'multiplicative_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'multiplicative_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 158 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  OP2 (S_DIV, _1, _3)
	)
# 881 "cparse.ml"
               : 'multiplicative_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'multiplicative_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cast_expression) in
    Obj.repr(
# 162 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  OP2 (S_MOD, _1, _3)
	)
# 891 "cparse.ml"
               : 'multiplicative_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'multiplicative_expression) in
    Obj.repr(
# 169 "cparse.mly"
            ( _1 )
# 898 "cparse.ml"
               : 'additive_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'additive_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'multiplicative_expression) in
    Obj.repr(
# 171 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  OP2 (S_ADD, _1, _3)
	)
# 908 "cparse.ml"
               : 'additive_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'additive_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'multiplicative_expression) in
    Obj.repr(
# 175 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  OP2 (S_SUB, _1, _3)
	)
# 918 "cparse.ml"
               : 'additive_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'additive_expression) in
    Obj.repr(
# 181 "cparse.mly"
                              ( _1 )
# 925 "cparse.ml"
               : 'shift_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 185 "cparse.mly"
                           ( _1 )
# 932 "cparse.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relational_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 187 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  CMP (C_LT, _1, _3)
	)
# 942 "cparse.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relational_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 191 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  CMP (C_LT, _3, _1)
	)
# 952 "cparse.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relational_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 195 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  CMP (C_LE, _1, _3)
	)
# 962 "cparse.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relational_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'shift_expression) in
    Obj.repr(
# 199 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  CMP (C_LE, _3, _1)
	)
# 972 "cparse.ml"
               : 'relational_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'relational_expression) in
    Obj.repr(
# 205 "cparse.mly"
                                ( _1 )
# 979 "cparse.ml"
               : 'equality_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'equality_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'relational_expression) in
    Obj.repr(
# 207 "cparse.mly"
 ( sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  CMP (C_EQ, _1, _3)
	)
# 989 "cparse.ml"
               : 'equality_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'equality_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'relational_expression) in
    Obj.repr(
# 211 "cparse.mly"
 ( 
          let loc = sup_locator (loc_of_expr _1) (loc_of_expr _3) in
	  loc, EIF ((loc, CMP (C_EQ, _1, _3)),
		    (loc, CST 0),
		    (loc, CST 1))
	)
# 1002 "cparse.ml"
               : 'equality_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'equality_expression) in
    Obj.repr(
# 220 "cparse.mly"
                              ( _1 )
# 1009 "cparse.ml"
               : 'and_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'and_expression) in
    Obj.repr(
# 224 "cparse.mly"
                         ( _1 )
# 1016 "cparse.ml"
               : 'exclusive_or_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'exclusive_or_expression) in
    Obj.repr(
# 228 "cparse.mly"
                                  ( _1 )
# 1023 "cparse.ml"
               : 'inclusive_or_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'inclusive_or_expression) in
    Obj.repr(
# 232 "cparse.mly"
                                  ( _1 )
# 1030 "cparse.ml"
               : 'logical_and_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'logical_and_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'inclusive_or_expression) in
    Obj.repr(
# 234 "cparse.mly"
 ( let loc = sup_locator (loc_of_expr _1) (loc_of_expr _3) in
	  loc, EIF (_1, _3, (loc, CST 0))
	)
# 1040 "cparse.ml"
               : 'logical_and_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'logical_and_expression) in
    Obj.repr(
# 240 "cparse.mly"
                                 ( _1 )
# 1047 "cparse.ml"
               : 'logical_or_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'logical_or_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'logical_and_expression) in
    Obj.repr(
# 242 "cparse.mly"
 ( let loc = sup_locator (loc_of_expr _1) (loc_of_expr _3) in
	  loc, EIF (_1, (loc, CST 1), _3)
	)
# 1057 "cparse.ml"
               : 'logical_or_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'logical_or_expression) in
    Obj.repr(
# 248 "cparse.mly"
                                ( _1 )
# 1064 "cparse.ml"
               : 'conditional_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'logical_or_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'conditional_expression) in
    Obj.repr(
# 250 "cparse.mly"
 ( 
	  sup_locator (loc_of_expr _1) (loc_of_expr _5),
	  EIF (_1, _3, _5)
	)
# 1076 "cparse.ml"
               : 'conditional_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'conditional_expression) in
    Obj.repr(
# 257 "cparse.mly"
                                 ( _1 )
# 1083 "cparse.ml"
               : 'assignment_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'unary_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 259 "cparse.mly"
     (
	     let locvar, left = _1 in
	     let loc = sup_locator locvar (loc_of_expr _3) in
	     match left with
	       VAR x -> loc, SET_VAR (x, _3)
	     | OP2 (S_INDEX, (_, VAR x), i) -> loc, SET_ARRAY (x, i, _3)
	     | _ ->
		 begin
		   Error.error (Some loc)
		     "Can only write assignments of the form x=e or x[e]=e'.\n";
		   _3
		 end
	   )
# 1103 "cparse.ml"
               : 'assignment_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 275 "cparse.mly"
                                ( _1 )
# 1110 "cparse.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'assignment_expression) in
    Obj.repr(
# 277 "cparse.mly"
 ( 
	  sup_locator (loc_of_expr _1) (loc_of_expr _3),
	  ESEQ [_1; _3]
	)
# 1121 "cparse.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'optional_init_declarator_list) in
    Obj.repr(
# 285 "cparse.mly"
 ( List.rev _2 )
# 1129 "cparse.ml"
               : 'declaration))
; (fun __caml_parser_env ->
    Obj.repr(
# 289 "cparse.mly"
          ( [] )
# 1135 "cparse.ml"
               : 'optional_init_declarator_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'init_declarator_list) in
    Obj.repr(
# 290 "cparse.mly"
                        ( _1 )
# 1142 "cparse.ml"
               : 'optional_init_declarator_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'init_declarator) in
    Obj.repr(
# 296 "cparse.mly"
            ( [_1] )
# 1149 "cparse.ml"
               : 'init_declarator_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'init_declarator_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'init_declarator) in
    Obj.repr(
# 298 "cparse.mly"
            ( _3 :: _1 )
# 1157 "cparse.ml"
               : 'init_declarator_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'declarator) in
    Obj.repr(
# 301 "cparse.mly"
                            ( _1 )
# 1164 "cparse.ml"
               : 'init_declarator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 304 "cparse.mly"
                     ( let loc, x = _1 in CDECL (loc, x) )
# 1171 "cparse.ml"
               : 'declarator))
; (fun __caml_parser_env ->
    Obj.repr(
# 307 "cparse.mly"
                        ( () )
# 1177 "cparse.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 308 "cparse.mly"
                 ( () )
# 1183 "cparse.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'type_specifier) in
    Obj.repr(
# 309 "cparse.mly"
                           ( () )
# 1190 "cparse.ml"
               : 'type_specifier))
; (fun __caml_parser_env ->
    Obj.repr(
# 311 "cparse.mly"
                                  ( getloc () )
# 1196 "cparse.ml"
               : 'close_bracket))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'compound_statement) in
    Obj.repr(
# 314 "cparse.mly"
            ( _1 )
# 1203 "cparse.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expression_statement) in
    Obj.repr(
# 316 "cparse.mly"
            ( loc_of_expr _1, CEXPR _1 )
# 1210 "cparse.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'selection_statement) in
    Obj.repr(
# 318 "cparse.mly"
            ( _1 )
# 1217 "cparse.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'iteration_statement) in
    Obj.repr(
# 320 "cparse.mly"
            ( _1 )
# 1224 "cparse.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'jump_statement) in
    Obj.repr(
# 322 "cparse.mly"
            ( _1 )
# 1231 "cparse.ml"
               : 'statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'open_brace) in
    Obj.repr(
# 325 "cparse.mly"
                        ( _1 )
# 1238 "cparse.ml"
               : 'open_block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'close_brace) in
    Obj.repr(
# 326 "cparse.mly"
                          ( _1 )
# 1245 "cparse.ml"
               : 'close_block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'open_block) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'close_block) in
    Obj.repr(
# 330 "cparse.mly"
        ( sup_locator _1 _2, CBLOCK ([], []) )
# 1253 "cparse.ml"
               : 'compound_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'open_block) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'close_block) in
    Obj.repr(
# 332 "cparse.mly"
 ( sup_locator _1 _3, CBLOCK ([], List.rev _2) )
# 1262 "cparse.ml"
               : 'compound_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'open_block) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'declaration_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'close_block) in
    Obj.repr(
# 334 "cparse.mly"
 ( sup_locator _1 _3, CBLOCK (_2, []) )
# 1271 "cparse.ml"
               : 'compound_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'open_block) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'declaration_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'close_block) in
    Obj.repr(
# 336 "cparse.mly"
 ( sup_locator _1 _4, CBLOCK (_2, List.rev _3) )
# 1281 "cparse.ml"
               : 'compound_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'declaration) in
    Obj.repr(
# 342 "cparse.mly"
          ( _1 )
# 1288 "cparse.ml"
               : 'declaration_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'declaration_list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'declaration) in
    Obj.repr(
# 344 "cparse.mly"
          ( _1 @ _2 )
# 1296 "cparse.ml"
               : 'declaration_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 350 "cparse.mly"
          ( [_1] )
# 1303 "cparse.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'statement_list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 352 "cparse.mly"
          ( _2 :: _1 )
# 1311 "cparse.ml"
               : 'statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'semi_chr) in
    Obj.repr(
# 357 "cparse.mly"
            ( _1, ESEQ [] )
# 1318 "cparse.ml"
               : 'expression_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 359 "cparse.mly"
            ( _1 )
# 1325 "cparse.ml"
               : 'expression_statement))
; (fun __caml_parser_env ->
    Obj.repr(
# 362 "cparse.mly"
                    ( getloc () )
# 1331 "cparse.ml"
               : 'semi_chr))
; (fun __caml_parser_env ->
    Obj.repr(
# 364 "cparse.mly"
          ( getloc () )
# 1337 "cparse.ml"
               : 'ifkw))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'ifkw) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 368 "cparse.mly"
 ( 
          sup_locator _1 (fst _5), CIF (_3, _5,
					(getloc (), CBLOCK ([], [])))
	)
# 1349 "cparse.ml"
               : 'selection_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'ifkw) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expression) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'statement) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 373 "cparse.mly"
 ( 
          sup_locator _1 (fst _7), CIF (_3, _5, _7)
	)
# 1361 "cparse.ml"
               : 'selection_statement))
; (fun __caml_parser_env ->
    Obj.repr(
# 378 "cparse.mly"
                ( getloc () )
# 1367 "cparse.ml"
               : 'whilekw))
; (fun __caml_parser_env ->
    Obj.repr(
# 379 "cparse.mly"
            ( getloc () )
# 1373 "cparse.ml"
               : 'forkw))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'whilekw) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'close_paren) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 382 "cparse.mly"
    (
	    let loc = sup_locator _1 (fst _5) in
	    loc, CWHILE (_3, _5)
	   )
# 1386 "cparse.ml"
               : 'iteration_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'forkw) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'expression_statement) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expression_statement) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'close_paren) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 388 "cparse.mly"
 ( 
          let loc = sup_locator _1 (fst _6) in
	  loc, CBLOCK ([], [(loc_of_expr _3, CEXPR _3);
			    loc, CWHILE (_4, _6)])
	)
# 1401 "cparse.ml"
               : 'iteration_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'forkw) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expression_statement) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'expression_statement) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'close_paren) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'statement) in
    Obj.repr(
# 395 "cparse.mly"
 ( 
          let loc = sup_locator _1 (fst _7) in
	  loc, CBLOCK ([], [(loc_of_expr _3, CEXPR _3);
			    loc, CWHILE (_4,
					 (sup_locator (loc_of_expr _5) (loc_of_expr _7),
					  CBLOCK ([], [_7; (loc_of_expr _5,
							    CEXPR _5)])))])
	)
# 1420 "cparse.ml"
               : 'iteration_statement))
; (fun __caml_parser_env ->
    Obj.repr(
# 405 "cparse.mly"
                ( getloc () )
# 1426 "cparse.ml"
               : 'return))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'return) in
    Obj.repr(
# 409 "cparse.mly"
            ( _1, CRETURN None )
# 1433 "cparse.ml"
               : 'jump_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'return) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 411 "cparse.mly"
            ( sup_locator _1 (loc_of_expr _2), CRETURN (Some _2) )
# 1441 "cparse.ml"
               : 'jump_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'external_declaration) in
    Obj.repr(
# 416 "cparse.mly"
          ( _1 )
# 1448 "cparse.ml"
               : (CAST.var_declaration list)))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : (CAST.var_declaration list)) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'external_declaration) in
    Obj.repr(
# 418 "cparse.mly"
          ( _1 @ _2 )
# 1456 "cparse.ml"
               : (CAST.var_declaration list)))
; (fun __caml_parser_env ->
    Obj.repr(
# 420 "cparse.mly"
          ( [] )
# 1462 "cparse.ml"
               : (CAST.var_declaration list)))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'function_definition) in
    Obj.repr(
# 425 "cparse.mly"
            ( [_1] )
# 1469 "cparse.ml"
               : 'external_declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'declaration) in
    Obj.repr(
# 427 "cparse.mly"
            ( _1 )
# 1476 "cparse.ml"
               : 'external_declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'declarator) in
    Obj.repr(
# 430 "cparse.mly"
                                                 ( _2 )
# 1484 "cparse.ml"
               : 'parameter_declaration))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_declaration) in
    Obj.repr(
# 435 "cparse.mly"
          ( [_1] )
# 1491 "cparse.ml"
               : 'parameter_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parameter_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_declaration) in
    Obj.repr(
# 437 "cparse.mly"
          ( _3 :: _1 )
# 1499 "cparse.ml"
               : 'parameter_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_list) in
    Obj.repr(
# 441 "cparse.mly"
                         ( List.rev _1)
# 1506 "cparse.ml"
               : 'parameter_type_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parameter_list) in
    Obj.repr(
# 442 "cparse.mly"
                                            ( List.rev _1 )
# 1513 "cparse.ml"
               : 'parameter_type_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 446 "cparse.mly"
                                  ( [] )
# 1519 "cparse.ml"
               : 'parameter_declarator))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'parameter_type_list) in
    Obj.repr(
# 447 "cparse.mly"
                                                      ( _2 )
# 1526 "cparse.ml"
               : 'parameter_declarator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_specifier) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parameter_declarator) in
    Obj.repr(
# 451 "cparse.mly"
 ( _2, _3 )
# 1535 "cparse.ml"
               : 'function_declarator))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'function_declarator) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'compound_statement) in
    Obj.repr(
# 456 "cparse.mly"
 ( 
          let (loc, var), decls = _1 in
	  CFUN (loc, var, decls, _2)
	)
# 1546 "cparse.ml"
               : 'function_definition))
(* Entry translation_unit *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let translation_unit (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : (CAST.var_declaration list))
;;
