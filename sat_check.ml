(* ���̃v���O������Str���W���[�����g���Ă��� *)
(* �R���p�C����OCaml����ꂽ��Ԃ� ocamlopt str.cmxa sat_check.ml -o sat_check.exe *)
(* ocamlopt�ł̓��W���[���ɖ�肪����ꍇ ocamlc str.cma sat_check.ml -o sat_check.exe *)
(* �C���^�[�v���^�̏ꍇ�A#load "str.cma"�����s���邱�� *)
(* ������Ȃ��l��OCaml���C���X�g�[���������Ƃ�ocamlc�̕��������s����̂��ǂ��i�኱�x�����ʓ|�͋N���Â炢�j *)

(* environment *)
(* run on windows (mingw ocaml) *)
(* in this program, cygwin is not "windows" *)
let is_windows = true
(* minisat is on "PATH" or not *)
let is_command = false

(* on windows, we can admit ".exe" and "./" *)
let minisat_command = if is_windows || is_command then "minisat" else "./minisat"
let cnf_filename = "temp_cnf.txt"
let output_filename = "temp_out.txt"
let null_output = if is_windows then "nul" else "/dev/null"

let result_mapsfilename = "result_maps.txt"
let result_ambiguous_prefix = "ambiguous"

let prolog_rule_output = "input.txt"
let prolog_expect_output_prefix = "expect"

let property_prefix = "p_"
let category_prefix = "c_"


open List


let divide_list l n =
  let rec get_n r m = function
    | a :: rest when m > 0 -> get_n (a :: r) (m - 1) rest
    | t -> (rev r, t) in
  get_n [] n l


let string_splitter = Str.split (Str.regexp "[ \t\n]+")



(********************************************************)
type rule_atom = string


(* �����^��`/�����^��`�̃��X�g *)
type def_constrs = rule_atom list list


let rec def_to_restriction = function
  | [] -> []
  | a :: l ->
    (a, l) :: map (fun (p, nl) -> (p, a :: nl)) (def_to_restriction l)

let defs_to_restriction = map def_to_restriction


(* test data of definitions of properites/categories *)
let test_properties = [["home"; "restaurant"; "experiment"]; ["paper"; "gum"; "bottle"]; ["large"; "small"]]
(*let test_categories = [["���"; "�Y��"]; ["�R"; "�s�R"]]*)
let test_categories = [["general"; "industry"]; ["burnable"; "non-burnable"; "etc"]]


let test_properties_restriction = defs_to_restriction test_properties
let test_categories_restriction = defs_to_restriction test_categories


let defs_to_variable_map defs =
  let rec iter n = function
    | [] -> []
    | p :: l -> (p, n) :: iter (n+1) l in
    iter 1 (concat defs)


let make_vmap defs =
  let rec iter x = function
    | [] -> 0
    | (p, n) :: l -> if x = p then n else iter x l in
    fun x -> iter x (defs_to_variable_map defs)



let test_vmap = make_vmap (test_properties @ test_categories)


(* properties/categories definitions to patterns *)
let rec listtuple_to_tuplelist = function
  | [] -> [[]]
  | pl :: l ->
      let pl' = listtuple_to_tuplelist l in
      let rec cons_constr = function
        | [] -> []
        | p :: l' -> map (fun x -> p :: x) pl' @ cons_constr l' in
        cons_constr pl

(* Check whether input is in avoid list *)


(***************************************************************************)

(*
type patom =
  | Pvar (* ���ʂ̕ϐ����ďo�Ă��Ȃ����炱��ŏ\�� *)
  | Patom of rule_atom
(* �}�W���ɂ�����Ȃ炢����ł�����ł��邯��� *)

(* ���[���̋L�q�A�w�b�h�܂��̓{�f�B�� *)
type rule_tuple = patom list
(* �w�b�h�ƃ{�f�B�ꗗ�i�J�e�S�����琫���̂��߂Ƀ{�f�B�͕����� *)
type rules = rule_tuple * rule_tuple list


(* �\���̂��鐫���v�f�̃��X�g��Ԃ� *)
let patom_to_constrs p l =
  match p with
    | Pvar -> l
    | Patom p -> [ p ]

(* �����v�f�̃��X�g�̃��X�g����A��蓾�鐫���̃��X�g�𐶐�����   Haskell�Ȃ炠��͂������� *)
let rec constrs_to_products = function
  | [] -> [[]]
  | pl :: l ->
      let pl' = constrs_to_products l in
      let rec cons_constr = function
        | [] -> []
        | p :: l' -> map (fun x -> p :: x) pl' @ cons_constr l' in
        cons_constr pl

let rule_to_constrrule defsl defsr (lh, rhs) =
  (constrs_to_products (map2 patom_to_constrs lh defsl),
   concat (map (fun rh -> constrs_to_products (map2 patom_to_constrs rh defsr)) rhs))
(* Haskell��$��.�ق����� *)

let rules_to_constrrules defsl defsr l =
  map (rule_to_constrrule defsl defsr) l



(* test data of rules *)
(* forward means "Properties" to "Categories" *)
let test_rule_forward =
  [([Patom "home"      ; Patom "paper" ; Pvar], [ [ Patom "general" ; Patom "burnable" ] ]);
   ([Patom "home"      ; Pvar          ; Pvar], [ [ Patom "general" ; Pvar ] ]);
   ([Pvar              ; Patom "bottle"; Pvar], [ [ Patom "general" ; Patom "non-burnable" ] ]);
   ([Patom "experiment"; Pvar          ; Pvar], [ [ Patom "industry"; Pvar ] ])
  ]
(* backward means "Categories" to "Properties" *)
let test_rule_backward =
  [([Patom "general" ; Pvar], [ [ Patom "home"; Pvar; Pvar ];
                                [ Patom "restaurant"; Patom "paper"; Pvar] ]);
   ([Pvar; Patom "burnable"], [ [ Pvar; Patom "paper"; Pvar];
                                [ Pvar; Patom "gum"  ; Pvar] ])
  ]




(* test data of rules in rule_atoms *)
let test_forward_atoms  = rules_to_constrrules test_properties test_categories test_rule_forward
let test_backward_atoms = rules_to_constrrules test_categories test_properties test_rule_backward
(* ����ȓW�J����K�v�Ȃ��ˁH *)

(* �����f�[�^ *)
type avoids = patom list
*)

type rule_description = (rule_atom list list * rule_atom list list)


let test_rule_forward =
  [([ [ "home"; "paper" ] ], [ [ "general"; "burnable" ] ]);
   ([ [ "home"          ] ], [ [ "general" ] ]);
   ([ [ "bottle"        ] ], [ [ "general"; "non-burnable" ] ]);
   ([ [ "experiment"    ] ], [ [ "industry" ] ])
  ]
(* backward means "Categories" to "Properties" *)
let test_rule_backward =
  [([ [ "general"  ] ], [ [ "home" ];
                          [ "restaurant"; "paper" ] ]);
   ([ [ "burnable" ] ], [ [ "paper" ];
                          [ "gum" ] ])
  ]


(* test data of avoiding tuples *)
let test_avoids_properties = []
let test_avoids_categories = []








(***************************************************************************)

(* Propositional formulae *)
type prop_atom = int

(* �����W�J���@�ŕʂ̒�`���ǂ��ꍇ�͂����ɕύX���� *)
type pexp =
  | Plit of prop_atom
  | Pand of pexp * pexp
  | Por of pexp * pexp
(*  | Pimp of pexp * pexp *) (* ���p���������ɏ��Ȃ��̂ł��̏��not or�ɕϊ� *)
  | Pnot of pexp



(* f �͗Ⴆ��Plit (vmap x)�݂����ɒ�`   g ��fold���̓��e *)
let pexp_foldl g f = function
  | [] -> assert false
  | a :: l -> fold_left (fun p x -> g p (f x)) (f a) l

let pexp_andfold f = pexp_foldl (fun x y -> Pand (x, y)) f

let pexp_orfold f = pexp_foldl (fun x y -> Por (x, y)) f


let vmap_to_lit_fun vmap x = Plit (vmap x)


let constrs_to_pexp vmap = pexp_andfold (vmap_to_lit_fun vmap)

(* rule(s) to formula *)
let rule_to_pexp vmap (heads, bodies) =
  Por (Pnot (pexp_orfold (constrs_to_pexp vmap) heads),
       pexp_orfold (constrs_to_pexp vmap) bodies)

let rules_to_pexp vmap =
  pexp_andfold (rule_to_pexp vmap)




(* test rule data in pexp *)
let test_forward_pexp  = rules_to_pexp test_vmap test_rule_forward
let test_backward_pexp = rules_to_pexp test_vmap test_rule_backward





(* restriction(s) to formula *)
(* restriction means exclusiveness of some parameters *)
let one_restriction_to_pexp vmap (pos, negs) =
  Pand (Plit (vmap pos), pexp_andfold (fun x -> Pnot (Plit (vmap x))) negs)

let restriction_to_pexp vmap =
  pexp_orfold (one_restriction_to_pexp vmap)

let restrictions_to_pexp vmap =
  pexp_andfold (restriction_to_pexp vmap)



(* test restrictions in pexp *)
let test_properties_pexp = restrictions_to_pexp test_vmap test_properties_restriction
let test_categories_pexp = restrictions_to_pexp test_vmap test_categories_restriction




let avoids_pexp vmap = function
  | [] -> None
  | l  -> Some (pexp_andfold (fun nt -> Pnot (pexp_andfold (vmap_to_lit_fun vmap) nt)) l)



let test_avoids_properties_opt = avoids_pexp test_vmap test_avoids_properties
let test_avoids_categories_opt = avoids_pexp test_vmap test_avoids_categories



let and_option p = function
  | None -> p
  | Some x -> Pand (p, x)



(*********************************************************************)
let defs_to_pexp vmap defs = restrictions_to_pexp vmap (defs_to_restriction defs)

let rules_to_pexp vmap rules = rules_to_pexp vmap rules


let fold_system_pexp pdefs cdefs prules crules pav cav =
  let p =
    Pand (pdefs,
          Pand (cdefs,
                Pand (prules, crules))) in
  and_option (and_option p pav) cav





let test_pexp_delta_gamma =
  fold_system_pexp
    test_properties_pexp
    test_categories_pexp
    test_forward_pexp
    test_backward_pexp
    test_avoids_properties_opt
    test_avoids_categories_opt




let make_system_pexp pdefs cdefs prules crules pav cav =
  let vmap = make_vmap (pdefs @ cdefs) in
  let pdefs_pexp = defs_to_pexp vmap pdefs in
  let cdefs_pexp = defs_to_pexp vmap cdefs in
  let prules_pexp = rules_to_pexp vmap prules in
  let crules_pexp = rules_to_pexp vmap crules in
  let pav_opt = avoids_pexp vmap pav in
  let cav_opt = avoids_pexp vmap cav in
  fold_system_pexp pdefs_pexp cdefs_pexp prules_pexp crules_pexp pav_opt cav_opt



(**********************************************************************)
(* pexp normalization *)


let rec not_internalization = function
  | Plit x -> Plit x
  | Pand (p1, p2) -> Pand (not_internalization p1, not_internalization p2)
  | Por  (p1, p2) -> Por  (not_internalization p1, not_internalization p2)
  | Pnot p -> not_internalization_neg p
and not_internalization_neg = function
  | Plit x -> Pnot (Plit x)
  | Pand (p1, p2) -> Por  (not_internalization_neg p1, not_internalization_neg p2)
  | Por  (p1, p2) -> Pand (not_internalization_neg p1, not_internalization_neg p2)
  | Pnot p -> not_internalization p



let test_pexp_delta_not = not_internalization test_pexp_delta_gamma

type lit =
  | Lpos of prop_atom (* P *)
  | Lneg of prop_atom (* ~P *)

type cnf = lit list list (* ����͂ǂ��l���Ă����������y *)



(***********************************************************)
(* formula simplification *)

exception TautoClause

let rec simplify_clause = function
  | [] -> []
  | p :: rest ->
    let p' = match p with
      | Lpos x -> Lneg x
      | Lneg x -> Lpos x in
    let rec filter_p = function
      | [] -> []
      | x :: r -> if x = p then filter_p r else
                  if x = p' then raise TautoClause else x :: filter_p r in
    let filtered = filter_p rest in
    p :: simplify_clause filtered


(* �Ƃ肠�����P�^�߂̍폜�A�����ϐ��̍폜�͂����Ȃ��� *)
(* �߂ɂ܂�����œK���͂܂����Ă��Ȃ� *)
let rec simplify = function
  | [] -> []
  | clause :: rest ->
    let rest' = simplify rest in
    try
      (simplify_clause clause) :: rest'
    with
      TautoClause -> rest'

(* ����Ƃ�����\�[�g�A�T�u���X�g�̏ꍇ�̍폜�A���炢�H *)
(* �ϊ����ɂ�����ق����S�̂Ƃ��Ă͌����I�����H *)
(* append�̑����merge������B�\�[�g�͒����D��̏����Bpos/neg�͖��֌W�Ɋm�F�H *)

(* distribution�̎��ɂ��܂��H *)
let rec simplify_clause_app left right = match left with
  | [] -> right
  | p :: rest ->
    let p' = match p with
      | Lpos x -> Lneg x
      | Lneg x -> Lpos x in
    let rec exist_p = function
      | [] -> false
      | x :: r -> if x = p then true
                  else if x = p' then raise TautoClause
                  else exist_p r in
    if exist_p right then simplify_clause_app rest right
    else p :: simplify_clause_app rest right



(** normalization and transformation **)
(* simple version (it's slow and generates big formulae) *)
let rec distribution cnf1 cnf2 =
  match cnf1 with
  | [] -> []
  | clause :: rest ->
    fold_right
      (fun x r ->
        try
          simplify_clause_app clause x :: r
        with
          TautoClause -> r)
      cnf2 [] @ distribution rest cnf2


let rec simple_transform = function
  | Pand (p1, p2) -> simple_transform p1 @ simple_transform p2
  | Por  (p1, p2) -> distribution (simple_transform p1) (simple_transform p2)
  | Plit x -> [ [ Lpos x ] ]
  | Pnot (Plit x) -> [ [ Lneg x ] ]
  | _ -> assert false


(*
TODO �g�������Ȃ炢�����
let rec tseitin_transform n = function
  | Pand p1 p2 ->
    let (p1', m) = tseitin_transform n p1 in
    let (p2', l) = tseitin_transform m p2 in
    (Pand p1' p2', l)
  | Por p1 p2 -> ?
  | p -> (p, n)
*)

let test_cnf = simple_transform test_pexp_delta_not

let cnf_transform p = simple_transform (not_internalization p)


let avoids_input vmap avoids =
  map (map (fun x -> [ Lpos (vmap x) ])) avoids


let simplified_cnf_transform p = simplify (cnf_transform p) (* �������ʂ��Ǝv������ *)



(*************************************************************)
(* output dimacs format *)

let string_of_literal = function
  | Lpos x -> string_of_int x
  | Lneg x -> "-" ^ string_of_int x

let rec string_of_clause = function
  | [] -> "0\n"
  | a :: l -> string_of_literal a ^ (" " ^ string_of_clause l)

let output_cnf out =
  iter (fun l -> output_string out (string_of_clause l))

let output_dimacs out cnf num_var =
  output_string out
    ("p cnf " ^ string_of_int num_var ^ " " ^ string_of_int (length cnf) ^ "\n");
  output_cnf out cnf



(***************************************************************)
(* execute minisat *)


let com_string = minisat_command ^ " " ^ cnf_filename ^ " " ^ output_filename ^ " > " ^ null_output

let satisfiable res = (res = 10)
(* note : when unsatisfiable, minisat returns 20 *)

let call_minisat cnf num_var =
  let out = open_out cnf_filename in
  output_dimacs out cnf num_var;
  flush out; close_out out;
  let result = Sys.command com_string in
  satisfiable result

(* #load "str.cma" is necessary if you run on ocaml *)
(* str.sc(x)a is necessary if you compile *)
let get_valuation () =
  let inc = open_in output_filename in
  let _ = input_line inc in
  let valuation_str = input_line inc in
  close_in inc;
  rev (tl (rev_map int_of_string (string_splitter valuation_str)))

let get_valuation_inv values =
  map (fun n -> if n > 0 then Lneg n else Lpos (-n)) values




let test_concatdefs = concat (test_properties @ test_categories)

let test_varlength = length test_concatdefs




(***************************************************************)
(* some functions for searching unsatisfiable tuples *)


let input_list defs vmap =
  map (map (fun x -> [ Lpos (vmap x) ])) (listtuple_to_tuplelist defs)



let test_inputs = input_list test_properties test_vmap


let num_to_name concatdefs n =
  nth concatdefs (n-1)

let lit_num = function
  | Lpos n | Lneg n -> n



let positive_valuation valuation = filter (fun n -> n > 0) valuation

let split_valuation valuation input_num =
  divide_list (positive_valuation valuation) input_num



(***************************************************************)
(* print result *)


let output_tuple out input str_fun =
  output_string out "(";
  (match input with
   | [] -> ()
   | i :: rest ->
     (output_string out (str_fun i); iter (fun t -> output_string out ", "; output_string out (str_fun t)) rest));
  output_string out ")"

(* input�̏����ɍ��킹�����́B�ėp���͂��܂�Ȃ� *)
let output_one_lit_list concatdefs = function
  | [ t ] -> num_to_name concatdefs (lit_num t)
  | _ -> assert false

let output_input out input concatdefs =
  output_tuple out input (output_one_lit_list concatdefs)


(*
let output_valuation_property out valuation concatdefs input_num =
  output_tuple out (fst (split_valuation valuation input_num) (num_to_name concatdefs)

let output_valuation_category out valuation concatdefs input_num =
  output_tuple out (snd (split_valuation valuation input_num) (num_to_name concatdefs)
  output_tuple out output (num_to_name concatdefs)
*)


let output_valuation out valuation concatdefs input_num =
  let (input , output) = split_valuation valuation input_num in
  output_tuple out input (num_to_name concatdefs);
  output_string out " -> ";
  output_tuple out output (num_to_name concatdefs)






(***************************************************************)
(* print some data for prolog *)

let search defs v =
  let rec iter n = function
    | [] -> raise Not_found
    | vl :: l -> if mem v vl then n else iter (n+1) l in
  iter 0 defs

let predicate_string_of_variable pdefs cdefs v =
  let param =
    try
      property_prefix ^ string_of_int (search pdefs v)
    with
        Not_found ->
          category_prefix ^ string_of_int (search cdefs v) in
    "f(" ^ v ^ ", " ^ param ^ ")"


let list_string_of_termlist str_of_term l =
  "[ " ^ String.concat ", " (map str_of_term l) ^ " ]"


(* �{���͂Ȃ��Ă����̂����ǁA�R�����g�̂��� *)
let output_def out name defs =
  let num = ref 0 in
  iter (fun def ->
          let n = !num in
          num := n + 1;
          output_string out "% ";
          iter (fun x -> output_string out ("\tf(" ^ x ^ ", " ^ name ^ string_of_int n ^ ")")) def;
          output_string out "\n") defs;
  output_string out "\n"


let output_comment = output_string


let output_head out pred_str_of_var heads =
  let len = length heads in
  if len = 0 then () else
    if len > 1 then (print_string "CAUTION : a head part of each rule should not be disjunction of props; generated prolog script must be meaningless"; print_newline ())
    else (let head = hd heads in
            output_string out "imp( ";
            output_string out (list_string_of_termlist pred_str_of_var head);
            output_string out ", ")


let output_body out pred_str_of_var bodies =
  output_string out (list_string_of_termlist (list_string_of_termlist pred_str_of_var) bodies);
  output_string out " ).\n"


(* avoid list�͗v��Ȃ��Ǝv���B����Ȃ珑���B *)
let output_avoid out prefix = ignore


(* mapi��4.00�ȍ~�Ȃ̂� *)
let mapi f l =
  let rec iter n = function
    | [] -> []
    | x :: l -> f n x :: iter (n+1) l in
  iter 0 l

let write_expect n input pdefs cdefs output =
  let out = open_out (prolog_expect_output_prefix ^ string_of_int n ^ ".txt") in
  output_string out "start_set( ";
  output_string out (list_string_of_termlist (predicate_string_of_variable pdefs cdefs) input);
  output_string out " ).\nneed( ";
(* output�̃p�^�[���}�b�` *)
  (match output with
     | Some output ->
         output_string out (list_string_of_termlist (predicate_string_of_variable pdefs cdefs) output)
     | None ->
         output_string out (String.concat ", " (mapi (fun i _ -> "f(C" ^ string_of_int i ^ ", " ^ category_prefix ^ string_of_int i ^ ")") cdefs)));
  output_string out " ).\n";
  flush out; close_out out




(***************************************************************)
(* functions reading definition from stdin *)
let get_blocks out_block out_com =
  let rec make_list l =
    let line = read_line () in
    let inputs = string_splitter line in
    if inputs = [] then
      let result = rev l in (out_block result; result)
    else
      let head = hd inputs in
      if head = "//" then make_list l else
      if head = "%" then (out_com (line ^ "\n"); make_list l) else make_list (inputs :: l) in
  make_list []



let get_defs = get_blocks

let get_rule out_head out_body out_com =
  let head = get_blocks out_head out_com in
  if head = [] then None else
    let body = get_blocks out_body out_com in
    Some (head, body)

let get_rules out_head out_body out_com =
  let rec get_list l =
    match get_rule out_head out_body out_com with
    | None -> rev l
    | Some r -> get_list (r :: l) in
  get_list []


let get_avoids = get_blocks

let get_cases () =
 let rec get_list l =
    match get_blocks ignore ignore with
    | [] -> rev l
    | [x;y] -> get_list ((x,y) :: l)
    | _ -> (print_string "Some test cases are not valid format"; print_newline (); assert false) in
  get_list []



type def_data = { pdefs : def_constrs; cdefs : def_constrs;
                  rules : rule_description list;
                  pavoids : rule_atom list list; cavoids : rule_atom list list;
                  cases : (rule_atom list * rule_atom list) list
                }


let get_data () =
  let out = open_out prolog_rule_output in
  output_string out "% Exclusive relations--------------------------------\n";
  let out_com = output_comment out in
  let out_def = output_def out in
  let pdefs = get_defs (out_def property_prefix) out_com in
  let cdefs = get_defs (out_def category_prefix) out_com in
  output_string out "\n% Input rules--------------------------------\n";
  let pred_str_of_var = predicate_string_of_variable pdefs cdefs in
  let out_head = output_head out pred_str_of_var in
  let out_body = output_body out pred_str_of_var in
  let rules = get_rules out_head out_body out_com in
  let out_avoid = output_avoid out in
  let pavoids = get_avoids (out_avoid "property") out_com in
  let cavoids = get_avoids (out_avoid "category") out_com in
  let cases = get_cases () in
  flush out; close_out out;
  { pdefs = pdefs; cdefs = cdefs;
    rules = rules;
    pavoids = pavoids; cavoids = cavoids;
    cases = cases
  }




(***************************************************************)
(* some misc. functions for ambiguity *)
let determined_list output values =
  let len = length output in
  let rec iter i det =
    if i < len then
      let t = nth output i in
        if for_all (fun x -> t = nth x i) values then
          iter (i+1) (t :: det)
        else iter (i+1) det
    else rev det in
    iter 0 []





(***************************************************************)
(* search unsatisfiable tuples *)

let check_consistency cnf inputs avoids pdefs cdefs concatdefs num_var cases =
  let inconsistent_num = ref 0 in
  iter (fun input ->
    if mem input avoids then ()
    else try
      let output = map (fun v -> [ Lpos v ]) (snd (find (fun v -> fst v = input) cases)) in
        if not (call_minisat (output @ input @ cnf) num_var) then
          (print_string "Inconsistent input (with test case) : ";
           output_input stdout input concatdefs;
           print_newline ();
           let input = map (fun l -> (num_to_name concatdefs (lit_num (hd l)))) input in
           let output = map (fun l -> (num_to_name concatdefs (lit_num (hd l)))) output in
             write_expect !inconsistent_num input pdefs cdefs (Some output);
             inconsistent_num := !inconsistent_num + 1)
    with  Not_found ->
      if not (call_minisat (input @ cnf) num_var) then
        (print_string "Inconsistent input : ";
         output_input stdout input concatdefs;
         (* print_string " (please write a test-case for this input and re-run)"; *)
         print_newline ();
         write_expect !inconsistent_num (map (fun l -> (num_to_name concatdefs (lit_num (hd l)))) input) pdefs cdefs None;
         inconsistent_num := !inconsistent_num + 1))
    inputs;
  (!inconsistent_num = 0)


(* Not yet to use cases *)
let check_ambiguity cnf inputs avoids pdefs cdefs concatdefs num_var cases =
  let ambiguous_num = ref 0 in
  let result_file = open_out result_mapsfilename in
  let rec all_sats cnf values =
    if call_minisat cnf num_var then
      (let value = get_valuation () in
         all_sats (get_valuation_inv value :: cnf) (value :: values))
    else rev values in
  output_string result_file "% Already determined input-output\n";
  iter (fun input ->
    if mem input avoids then ()
    else try
      let output = snd (find (fun v -> fst v = input) cases) in
      let value1 = map (fun v -> Lneg v) output in
      let cur_cnf = value1 :: input @ cnf in
        (* �e�X�g�P�[�X�Œʂ邱�Ƃ͂����������Ă���̂Ŋm���߂Ȃ� *)
      let values = all_sats cur_cnf [] in
        if values <> [] then
          let pnum = length pdefs in
          let num = !ambiguous_num in
          let amb_filename = result_ambiguous_prefix ^ string_of_int num ^ ".txt" in
          let amb_file = open_out amb_filename in
          let outputs = map (fun x -> snd (split_valuation x pnum)) values in
            (print_string "Input with output differing from test-case : ";
             output_input stdout input concatdefs;
             print_string (" -- see " ^ amb_filename);
             print_newline ();
             output_string amb_file "% Properties\n";
             output_input amb_file input concatdefs; (* input p([..., ..., ... ])  *)
             output_string amb_file "\n% Categories (the first is expected output)\n";
             output_tuple amb_file output (num_to_name concatdefs); (* output c([..., ..., ... ])�ɕύX *)
             output_string amb_file "\n";
             iter (fun x -> output_tuple amb_file x (num_to_name concatdefs); output_string amb_file "\n") outputs; (* ���� *)
             output_string amb_file "% Determined categorical values :";
             iter (fun x -> output_string amb_file (" " ^ num_to_name concatdefs x)) (determined_list output outputs);
             output_string amb_file "\n";
             flush amb_file; close_out amb_file;
             ambiguous_num := num+1)
        else
          (output_input result_file input concatdefs;
           output_string result_file " -> *";
           output_tuple result_file output (num_to_name concatdefs);
           output_string result_file "\n")
    with  Not_found ->
      let cur_cnf = input @ cnf in
        if call_minisat cur_cnf num_var then
          let value1 = get_valuation () in
          let values = all_sats (get_valuation_inv value1 :: cur_cnf) [] in
          if values <> [] then
            (let pnum = length pdefs in
             let num = !ambiguous_num in
             let amb_filename = result_ambiguous_prefix ^ string_of_int num ^ ".txt" in
             let amb_file = open_out amb_filename in
             let (_, output) = split_valuation value1 pnum in
             let outputs = map (fun x -> snd (split_valuation x pnum)) values in
               print_string "Input with ambiguous outputs : ";
               output_input stdout input concatdefs;
               print_string (" -- see " ^ amb_filename);
               print_newline ();
               output_string amb_file "% Properties\n";
               output_input amb_file input concatdefs; (* input p([..., ..., ... ]  *)
               output_string amb_file "\n% Categories\n";
               iter (fun x -> output_tuple amb_file x (num_to_name concatdefs); output_string amb_file "\n") (output :: outputs); (* c([..., ..., ... ]) *)
               output_string amb_file "% Determined categorical values :";
               iter (fun x -> output_string amb_file (" " ^ num_to_name concatdefs x)) (determined_list output outputs);
               output_string amb_file "\n";
               flush amb_file; close_out amb_file;
               ambiguous_num := num+1)
          else
            (output_valuation result_file value1 concatdefs (length pdefs);
             output_string result_file "\n")
        else () (* �������ĂȂ��Ȃ�K����x�͐�������͂������A�ςȎg����������Ƃ����ɗ���\�������� *) ) inputs;
    flush result_file; close_out result_file;
    !ambiguous_num = 0







(**********************************************************)
(* �������� *)

let check_rule_cnf rule_cnf inputs avoids_input pdefs cdefs concatdefs num_var cases =
  print_string ("Consistency of the rules checking :"); print_newline ();
  if not (call_minisat rule_cnf num_var)
  then (print_string ("NG - the rules themselves are unsatisfiable"); print_newline (); false)
  else (print_string "OK - the rules have one or more satisfiable valuations"; print_newline (); print_newline ();
        print_string ("Consistency with each input checking : ");
        print_newline ();
        if check_consistency rule_cnf inputs avoids_input pdefs cdefs concatdefs num_var cases
        then (print_string "OK - the rules are consistent"; print_newline (); print_newline (); true)
        else (print_string "NG - the rules are unsatsifiable with some inputs or not satisfying some test cases"; print_newline (); print_newline(); false))


let execute def =
  let concatdefs = def.pdefs @ def.cdefs in
  let vmap = make_vmap (def.pdefs @ def.cdefs) in
  let concatdefs = concat concatdefs in
  let num_var = length concatdefs in
  let pr_pexp = defs_to_pexp vmap def.pdefs in
  let cr_pexp = defs_to_pexp vmap def.cdefs in
  let rule_pexp = rules_to_pexp vmap def.rules in
  let pr_pexp_avoids = and_option pr_pexp (avoids_pexp vmap def.pavoids) in
  let cr_pexp_avoids = and_option cr_pexp (avoids_pexp vmap def.cavoids) in
  let pr_cnf = cnf_transform pr_pexp_avoids in
  let cr_cnf = cnf_transform cr_pexp_avoids in
  let rule_cnf = cnf_transform rule_pexp in
  let inputs = input_list def.pdefs vmap in
  let rule_all_cnf = rule_cnf @ pr_cnf @ cr_cnf in
  let avoids_input = avoids_input vmap def.pavoids in
  let cases = map (fun (p, c) -> (map (fun x -> [ Lpos (vmap x) ]) p, map (fun x -> vmap x) c)) def.cases in
  check_rule_cnf rule_all_cnf inputs avoids_input def.pdefs def.cdefs concatdefs num_var cases
  &&
  check_ambiguity rule_all_cnf inputs avoids_input def.pdefs def.cdefs concatdefs num_var cases
;;


execute (get_data ())
