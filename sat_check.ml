(* このプログラムはStrモジュールを使っている *)
(* コンパイルはOCamlを入れた状態で ocamlopt str.cmxa sat_check.ml -o sat_check.exe *)
(* ocamloptではモジュールに問題がある場合 ocamlc str.cma sat_check.ml -o sat_check.exe *)
(* インタープリタの場合、#load "str.cma"を実行すること *)

(* environment *)
(* run on windows (mingw ocaml) *)
(* in this program, cygwin is not "windows" *)
let is_windows = false
(* minisat is on "PATH" *)
let is_command = true

(* on windows, we can admit ".exe" *)
let minisat_command = if is_windows || is_command then "minisat" else "./minisat"
let cnf_filename = "temp_cnf.txt"
let output_filename = "temp_out.txt"
let null_output = if is_windows then "nul" else "/dev/null"

let result_filename = "result_sat.txt"

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


(* 性質型定義/分解型定義のリスト *)
type def_constrs = rule_atom list list


let rec def_to_restriction = function
  | [] -> []
  | a :: l ->
    (a, l) :: map (fun (p, nl) -> (p, a :: nl)) (def_to_restriction l)

let defs_to_restriction = map def_to_restriction


(* test data of definitions of properites/categories *)
let test_properties = [["home"; "restaurant"; "experiment"]; ["paper"; "gum"; "bottle"]; ["large"; "small"]]
(*let test_categories = [["一般"; "産業"]; ["可燃"; "不燃"]]*)
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
  | Pvar (* 共通の変数って出てこないからこれで十分 *)
  | Patom of rule_atom
(* マジメにいじるならいくらでも難しくできるけれど *)

(* ルールの記述、ヘッドまたはボディ部 *)
type rule_tuple = patom list
(* ヘッドとボディ一覧（カテゴリから性質のためにボディは複数可 *)
type rules = rule_tuple * rule_tuple list


(* 可能性のある性質要素のリストを返す *)
let patom_to_constrs p l =
  match p with
    | Pvar -> l
    | Patom p -> [ p ]

(* 性質要素のリストのリストから、取り得る性質のリストを生成する   Haskellならあるはずだけど *)
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
(* Haskellの$か.ほしいね *)

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
(* こんな展開する必要なくね？ *)

(* 無視データ *)
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

(* もし展開方法で別の定義が良い場合はすぐに変更する *)
type pexp =
  | Plit of prop_atom
  | Pand of pexp * pexp
  | Por of pexp * pexp
(*  | Pimp of pexp * pexp *) (* 利用部分が非常に少ないのでその場でnot orに変換 *)
  | Pnot of pexp



(* f は例えばPlit (vmap x)みたいに定義   g はfold時の内容 *)
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

type cnf = lit list list (* これはどう考えてもこっちが楽 *)



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


(* とりあえず恒真節の削除、同じ変数の削除はおこなった *)
(* 節にまたがる最適化はまだしていない *)
let rec simplify = function
  | [] -> []
  | clause :: rest ->
    let rest' = simplify rest in
    try
      (simplify_clause clause) :: rest'
    with
      TautoClause -> rest'

(* するとしたらソート、サブリストの場合の削除、くらい？ *)
(* 変換時にやったほうが全体としては効率的かも？ *)
(* appendの代わりにmergeをする。ソートは長さ優先の順序。pos/negは無関係に確認？ *)

(* distributionの時にうまい？ *)
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
TODO 使えそうならいつかやる
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


let simplified_cnf_transform p = simplify (cnf_transform p) (* もう無駄だと思うけど *)



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





(***************************************************************)
(* print result *)


let print_tuple input str_fun =
  print_string "(";
  (match input with
   | [] -> ()
   | i :: rest ->
     (print_string (str_fun i); iter (fun t -> print_string ", "; print_string (str_fun t)) rest));
  print_string ")"

(* inputの書式に合わせたもの。汎用性はあまりない *)
let print_one_lit_list concatdefs = function
  | [ t ] -> num_to_name concatdefs (lit_num t)
  | _ -> assert false

let print_input input concatdefs =
  print_tuple input (print_one_lit_list concatdefs)


let print_valuation_property valuation concatdefs input_num =
  let positive_valuation = filter (fun n -> n > 0) valuation in
  let (input, _) = divide_list positive_valuation input_num in
  print_tuple input (num_to_name concatdefs)

let print_valuation_category valuation concatdefs input_num =
  let positive_valuation = filter (fun n -> n > 0) valuation in
  let (_, output) = divide_list positive_valuation input_num in
  print_tuple output (num_to_name concatdefs)

let print_valuation valuation concatdefs input_num =
  let positive_valuation = filter (fun n -> n > 0) valuation in
  let (input , output) = divide_list positive_valuation input_num in
  print_tuple input (num_to_name concatdefs);
  print_string " -> ";
  print_tuple output (num_to_name concatdefs)






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


(* 本当はなくていいのだけど、コメントのため *)
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


(* avoid listは要らないと思う。いるなら書く。 *)
let output_avoid out prefix = ignore


(* mapiは4.00以降なので *)
let mapi f l =
  let rec iter n = function
    | [] -> []
    | x :: l -> f n x :: iter (n+1) l in
  iter 0 l

let write_expect n input pdefs cdefs =
  let out = open_out (prolog_expect_output_prefix ^ string_of_int n ^ ".txt") in
  output_string out "start_set( ";
  output_string out (list_string_of_termlist (predicate_string_of_variable pdefs cdefs) input);
  output_string out " ).\nneed( [ ";
  output_string out (String.concat ", " (mapi (fun i _ -> "f(C" ^ string_of_int i ^ ", " ^ category_prefix ^ string_of_int i ^ ")") cdefs));
  output_string out " ] ).\n";
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




type def_data = { pdefs : def_constrs; cdefs : def_constrs;
                  rules : rule_description list;
                  pavoids : rule_atom list list; cavoids : rule_atom list list
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
  output_string out "\n";
  flush out; close_out out;
  { pdefs = pdefs; cdefs = cdefs;
    rules = rules;
    pavoids = pavoids; cavoids = cavoids
  }







(***************************************************************)
(* search unsatisfiable tuples *)

let check_consistency cnf inputs avoids pdefs cdefs concatdefs num_var =
  let inconsistent_num = ref 0 in
  iter (fun input ->
    if mem input avoids then () else
      if not (call_minisat (input @ cnf) num_var) then
        (print_string "Inconsistent input : ";
         print_input input concatdefs;
         print_newline (); write_expect !inconsistent_num (map (fun l -> (num_to_name concatdefs (lit_num (hd l)))) input) pdefs cdefs; inconsistent_num := !inconsistent_num + 1)) inputs;
  (!inconsistent_num = 0)


let check_ambiguity cnf inputs avoids pdefs cdefs concatdefs num_var =
  let unitary = ref true in
  iter (fun input ->
    if mem input avoids then () else
      let cur_cnf = input @ cnf in
      if call_minisat cur_cnf num_var then
        let values1 = get_valuation () in
        if call_minisat (get_valuation_inv values1 :: cur_cnf) num_var then
          (let values2 = get_valuation () in
           let pnum = length pdefs in
           print_string "Input with ambiguous outputs : ";
           print_input input concatdefs;
           print_string " -> ";
           print_valuation_category values1 concatdefs pnum;
           print_string " and ";
           print_valuation_category values2 concatdefs pnum;
           print_newline (); unitary := false)) inputs;
  !unitary
(* 今は２つしか見せていないが、必要ならすべて見つけることは可能 *)







(**********************************************************)
(* 処理順序 *)

let check_rule_cnf rule_cnf inputs avoids_input pdefs cdefs concatdefs num_var =
  print_string ("Consistency of the rules checking :"); print_newline ();
  if not (call_minisat rule_cnf num_var)
  then (print_string ("NG - the rules themselves are unsatisfiable"); print_newline (); false)
  else (print_string "OK - the rules have one or more satisfiable valuations"; print_newline (); print_newline ();
        print_string ("Consistency with every input checking : ");
        print_newline ();
        if check_consistency rule_cnf inputs avoids_input pdefs cdefs concatdefs num_var
        then (print_string "OK - the rules are consistent"; print_newline (); true)
        else (print_string "NG - the rules are unsatsifiable with some inputs"; print_newline (); false))


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
  check_rule_cnf rule_all_cnf inputs avoids_input def.pdefs def.cdefs concatdefs num_var
  &&
  check_ambiguity rule_all_cnf inputs avoids_input def.pdefs def.cdefs concatdefs num_var
;;


execute (get_data ())
