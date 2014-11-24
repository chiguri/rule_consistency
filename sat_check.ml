(* このプログラムはStrモジュールを使っている *)
(* コンパイルはOCamlを入れた状態で ocamlopt str.cmxa sat_check.ml -o sat_check.exe *)
(* ocamloptではモジュールに問題がある場合 ocamlc str.cma sat_check.ml -o sat_check.exe *)
(* インタープリタ(ocaml)の場合、#load "str.cma"を実行すること *)
(* 分からない人はOCamlをインストールしたあとでocamlcの部分を実行するのが良い（若干遅いが面倒は起きづらい） *)


(*** 最初のルール単体の検証はやめた。その方法で矛盾してもそもそも情報がなさ過ぎるため、どう直して良いか分からない。それだとあまりやる意味もない。 ***)


open List
open Str


(**************************************************************************************************)
(* 環境変数 *)
(* Windows上、cmd.exeかどうか(特にmingw ocaml) *)
(* cygwinはここでいう "windows" では*ない* *)
let is_windows = true
(* minisatがpath上にあり、ディレクトリを指定する必要がない（パス上にない場合はカレントディレクトリに置くこと） *)
let is_command = false

(* on windows, we can admit ".exe" and "./" *)
let minisat_command = if is_windows || is_command then "minisat" else "./minisat"

(* ファイル名 *)
(* minisat用 *)
let cnf_filename = "temp_cnf.txt"
let output_filename = "temp_out.txt"
let null_output = if is_windows then "nul" else "/dev/null"


(* 結果として出力を向けるファイル *)
let result_mapsfilename = "result_maps.txt"
let result_ambiguous_prefix = "ambiguous"
let result_ignoredfilename = "ignored.txt"

(* Prologのチェック用に用いるファイル *)
let prolog_rule_output = "input.txt"
let prolog_expect_output_prefix = "expect"

let property_prefix = "p_"
let category_prefix = "c_"


(* Prologにおける原子論理式のための関数記号 *)
let atomic_predicate = "f"

let consistent_property = "start_set"
let consistent_category = "need"
let ambiguous_property = "p"
let ambiguous_category = "c"
let fixed_ambiguous_category = "fixed"


let output_string_line out str =
  output_string out str; output_string out "\n"



(**************************************************************************************************)
(* リスト処理 *)


let rec remove_values from vals =
  match from with
    | p :: pl ->
        if mem p vals then remove_values pl vals
        else p :: remove_values pl vals
    | [] -> []




let divide_list l n =
  let rec get_n r m = function
    | a :: rest when m > 0 -> get_n (a :: r) (m - 1) rest
    | t -> (rev r, t) in
  get_n [] n l




let search defs v =
  let rec iter n = function
    | [] -> raise Not_found
    | vl :: l -> if mem v vl then n else iter (n+1) l in
  iter 0 defs



(* mapiは4.00以降なので *)
let mapi f l =
  let rec iter n = function
    | [] -> []
    | x :: l -> f n x :: iter (n+1) l in
  iter 0 l



let lift = map (fun x -> [x])



(**************************************************************************************************)
(* 入力データの定義 *)


type ident = string

(* 入力に相当する論理式:implicationは最外にしか存在しないので特殊形式 *)
type pexp =
  | Plit of ident
  | Pand of pexp list
  | Por  of pexp list
  | Pnot of pexp



type lit =
  | Lpos of ident
  | Lneg of ident


(* literal-CNF：変数と正負のみ *)
type lit_cnf = lit list list
(* minisat用のdimacs-CNF：正負を用いた整数 *)
type dimacs_cnf = int list list


(* 入力に対する保持するデータ：割と渡しまくる *)
type defs_data =
  {
    pdefs : ident list list;
    cdefs : ident list list;
    vmap : ident -> int;
    nmap : int -> ident;
    pred : ident -> string;
    var_num : int;
    p_kind_num : int;
    p_var_num : int;
    inputlist : int list list;
    restrictions : dimacs_cnf
  }





(* literal-CNFからdimacs-CNFへの変換 *)
let literal_to_dimacs_literal vmap = function
  | Lpos x -> vmap x
  | Lneg x -> - (vmap x)

let clause_to_dimacs_clause vmap = map (literal_to_dimacs_literal vmap)

let cnf_to_dimacs_cnf vmap = map (clause_to_dimacs_clause vmap)


(* dimacs-CNFからliteral-CNFへの変換 *)
let dimacs_literal_to_literal nmap n =
  if n < 0 then nmap (-n) else nmap n

let dimacs_clause_to_clause nmap = map (dimacs_literal_to_literal nmap)

let dimacs_cnf_to_cnf nmap = map (dimacs_clause_to_clause nmap)





(**************************************************************************************************)
(* Prolog出力（データをそのまま出す） *)


let predicate_string_of_variable pdefs cdefs v =
  let param =
    try
      property_prefix ^ string_of_int (search pdefs v)
    with
        Not_found ->
          category_prefix ^ string_of_int (search cdefs v) in
    atomic_predicate ^ "(" ^ v ^ ", " ^ param ^ ")"



let rec predicate_string_of_pexp pred = function
  | Plit x  -> pred x
  | Pand pl -> "and([ " ^ String.concat ", " (map (predicate_string_of_pexp pred) pl) ^ " ])"
  | Por  pl -> "or([ "  ^ String.concat ", " (map (predicate_string_of_pexp pred) pl) ^ " ])"
  | Pnot p  -> "neg( " ^ predicate_string_of_pexp pred p ^ " )"


let predicate_string_of_rule pred (head, body) =
  "imp( " ^ predicate_string_of_pexp pred head ^ ", " ^ predicate_string_of_pexp pred body ^ " )."



let list_string_of_termlist str_of_term l =
  "[ " ^ String.concat ", " (map str_of_term l) ^ " ]"


let string_of_def pred def =
  "\t" ^ String.concat ",\t" (map pred def)


let output_defs out pred pdefs cdefs =
  output_string out "all_pc([\n%%[property]\n";
  iter (fun i -> output_string out i; output_string out ",\n") (map (string_of_def pred) pdefs);
  output_string out "\n\n%%[category]\n";
  let (last :: cbody_r) = rev cdefs in
  let cbody = rev cbody_r in
  iter (fun i -> output_string out i; output_string out ",\n") (map (string_of_def pred) cbody);
  output_string out (string_of_def pred last);
  output_string out "\n ]).\n\n"



let write_expect n input defs output =
  let out = open_out (prolog_expect_output_prefix ^ string_of_int n ^ ".txt") in
  output_string out (consistent_property ^ "( ");
  output_string out (list_string_of_termlist defs.pred input);
  output_string out (" ).\n" ^ consistent_category ^ "( ");
(* outputの有無で出力を変更 *)
  (match output with
     | Some output ->
         output_string out (list_string_of_termlist defs.pred output)
     | None ->
         begin
           output_string out "[ ";
           output_string out (String.concat ", " (mapi (fun i _ -> atomic_predicate ^ "(C" ^ string_of_int i ^ ", " ^ category_prefix ^ string_of_int i ^ ")") defs.cdefs));
           output_string out " ]";
         end
  );
  output_string out " ).\n";
  flush out; close_out out







(**************************************************************************************************)
(* dimacs出力（dimacs-CNFの出力） *)

let rec string_of_clause = function
  | [] -> "0\n"
  | a :: l -> string_of_int a ^ (" " ^ string_of_clause l)

let output_cnf out =
  iter (fun l -> output_string out (string_of_clause l))

let output_dimacs out cnf num_var =
  output_string out
    ("p cnf " ^ string_of_int num_var ^ " " ^ string_of_int (length cnf) ^ "\n");
  output_cnf out cnf





(**************************************************************************************************)
(* 結果出力関数 *)

(* 単純出力用 *)
let output_tuple out tuple =
  output_string out "and( ";
  output_string out (String.concat " " tuple);
  output_string out " )"


(* 入力と出力の分離 ただしdimacs-cnf形式 *)
let split_inout l p_var_num =
  partition (fun n -> n <= p_var_num) (filter (fun n -> n > 0) l)


(* dimacs形式の出力 *)
let output_num_tuple out nmap tuple =
  output_tuple out (map nmap tuple)



let rec output_pexp out = function
  | Plit x  -> output_string out x
  | Pand pl -> output_string out "and( "; iter (fun p -> output_pexp out p; output_string out " ") pl; output_string out ")"
  | Por  pl -> output_string out "or( " ; iter (output_pexp out) pl; output_string out " )"
  | Pnot p  -> output_string out "-"; output_pexp out p




(**************************************************************************************************)
(* 入力処理 *)

exception SyntaxException of string


(* コメント判定 *)
let com_reg = regexp "//"
let is_comment s = string_match com_reg s 0

(* Prologコメント判定 *)
let prolog_com_reg = regexp "%"
let is_prolog_comment s = string_match prolog_com_reg s 0

(* Prologではコメントだが読ませるもの:最初二文字を除いて入力と思うことにする *)
let prolog_dcom_reg = regexp "%%"
let is_prolog_dcomment s = string_match prolog_dcom_reg s 0


let splitter = regexp "-->\\| \\|\r\\|\t\\|\n\\|(\\|)\\|\\[\\|\\]\\|-\\|,\\|\\.\\|\\*" (* アホみたいだが、区切り文字、特殊文字を別要素として記述している。\\|が区切り。 *)

let whitespace_delims = [ Delim " "; Delim "\t"; Delim "\n"; Delim "\r"; Delim ","; Delim "."; Delim "*"]
(* カンマやピリオドは本来読めないが、Prologスタイルの記述サポートのために可能に。*はこちらの都合。 *)

let rec remove_spaces sl = remove_values sl whitespace_delims


let get_lexed s = remove_spaces (full_split splitter s)



(* illegal text (for Prolog)を排除する方が良いと思うので、splitterとremoverはもう少しマジメにしても良いと思う *)


(* パーザーコンビネータにしようと思ったが、思い出せないのでやめた *)

let no_param_exception = SyntaxException "no parameter found"
let var_del_exception = SyntaxException "expected variables, but found delimiter"


let get_name = function
  | Text f :: Delim "(" :: Text t :: Text n :: Delim ")" :: sl when f = atomic_predicate -> (t, sl) (* nの内容までは確認しない *)
  | Text x :: sl -> (x, sl)
  | [] -> raise no_param_exception
  | sl -> raise var_del_exception


(* 実際のところoptionにする意味があるかは不明（終了は外側で判定するので） *)
let get_def =
  let rec iter xl = function
    | [] -> rev xl
    | orig ->
        let (x, sl) = get_name orig in iter (x :: xl) sl in
  iter []


let rec get_fml orig =
  let rec fml_list fl = function
    | Delim ")" :: sl -> (rev fl, sl)
    | sl ->
        let (f, rest) = get_fml sl in
          fml_list (f :: fl) rest in
  match orig with
    | Text "and" :: Delim "(" :: sl ->
        (*fml_list [] sl <=< (fun (fl,rest) -> (Some (Pand fl), rest)), orig) *)
        let (fl, rest) = fml_list [] sl in
          (Pand fl, rest)
    | Text "or" :: Delim "(" :: sl  ->
        let (fl, rest) = fml_list [] sl in
          (Por fl, rest)
    | Delim "-" :: sl  | Text "neg" :: sl ->
        let (f, rest) = get_fml sl in
          (Pnot f, rest)
    | Delim "(" :: sl ->
        begin match get_fml sl with
          | (f, Delim ")" :: rest) -> (f, rest)
          | _ -> raise (SyntaxException "expected right parenthesis, but found different")
        end
    | _ ->
        let (x, sl) = get_name orig in
          (Plit x, sl)


let get_rule orig =
  if hd orig = Text "imp" then
    let (head, sl) = get_fml (tl (tl orig)) in (* ここには決して突っ込まないこと。変なものを入れたらエラーになる。 *)
      (head, fst (get_fml sl))
  else match get_fml orig with
    | (head, Delim "-->" :: sl) ->
        let (tail, rest) = get_fml sl in
          (head, tail)
    | _ -> raise (SyntaxException "expected -->, but found different")




(* Prolog用のコメントを出力する関数が prolog_com_output *)
let rec get_next prolog_com_output =
  let line_process = function
    | s when is_comment s -> get_next prolog_com_output
    | s when is_prolog_comment s -> prolog_com_output s; get_next prolog_com_output
    | s ->
        match get_lexed s with
          | [] -> get_next prolog_com_output
          | x :: xl -> x :: (remove_values xl [Delim "["; Delim "]"]) (* 先頭以外の[]は無視する（Prologスタイルの読み込みのため） *) in
  match read_line () with
    | s when is_prolog_dcomment s -> line_process (String.sub s 2 (String.length s - 2))
    | s -> line_process s





let get_block get_elem prolog_out prolog_com_out =
  let rec iter bl =
    match get_next prolog_com_out with
      | Delim "[" :: _  | Delim "]" :: _ -> rev bl
      | sl ->
          let elem = get_elem sl in
          (prolog_out elem; iter (elem :: bl)) in
  iter []




let init_block out =
  get_block ignore ignore (output_string_line out) (* 入力を全て無視する *)


let get_defs out =
  get_block get_def ignore (output_string_line out) (* 定義記述に関しては全体が終わってからファイルに出す *)


let get_rules pred out =
  get_block get_rule (fun r -> output_string_line out (predicate_string_of_rule pred r)) (output_string_line out)


let get_no_p out =
  get_block
    get_def
    (fun l -> output_string out "%% ";
              output_tuple out l;
              output_string out "\n")
    (output_string_line out)


let get_p_rules out =
  get_block
    get_rule
    (fun (head, tail) -> output_string out "%% ";
                         output_pexp out head;
                         output_string out " --> ";
                         output_pexp out tail;
                         output_string out "\n")
    (output_string_line out)


let get_case orig =
  let unwrap_lit = function
    | Plit x -> x
    | _ -> raise (SyntaxException "expected literal, but found different") in
  let unwrap_and = function
    | Pand pl -> map unwrap_lit pl
    | _ -> raise (SyntaxException "expected and clause, but found different") in
  let (head, tail) = get_rule orig in
  (unwrap_and head, unwrap_and tail)


let get_cases out =
  get_block
    get_case
    (fun r -> output_string out "%% "; output_tuple out (fst r); output_string out " --> "; output_tuple out (snd r); output_string out "\n")
    (output_string_line out)





(**************************************************************************************************)
(* minisatの実行 *)


let string_splitter = Str.split (Str.regexp "[ \t\n]+")

let com_string = minisat_command ^ " " ^ cnf_filename ^ " " ^ output_filename ^ " > " ^ null_output

let satisfiable res = (res = 10)
(* note : when unsatisfiable, minisat returns 20 *)


let call_minisat cnf num_var =
  let out = open_out cnf_filename in
  output_dimacs out cnf num_var;
  flush out; close_out out;
  let result = Sys.command com_string in
  satisfiable result



let get_valuation () =
  let inc = open_in output_filename in
  let _ = input_line inc in
  let valuation_str = input_line inc in
  close_in inc;
  rev (tl (rev_map int_of_string (string_splitter valuation_str))) (* 末尾の0を除去するためにrev_mapを使用 *)


(* 次の解を見つけるために解の否定の追加に使用 *)
let get_valuation_inv values =
  map (fun n -> -n) values





(**************************************************************************************************)
(* 論理式のCNFへの変換 *)

type nexp = (* not-internalized fml *)
  | Npos of ident
  | Nneg of ident
  | Nand of nexp list
  | Nor  of nexp list


let rec not_internalization = function
  | Plit x  -> Npos x
  | Pand pl -> Nand (map not_internalization pl)
  | Por  pl -> Nor  (map not_internalization pl)
  | Pnot p  -> not_internalization_neg p
and not_internalization_neg = function
  | Plit x  -> Nneg x
  | Pand pl -> Nor  (map not_internalization_neg pl)
  | Por  pl -> Nand (map not_internalization_neg pl)
  | Pnot p  -> not_internalization p




exception TautoClause


(* 二つのor clauseを合成する、ただし恒真の場合は例外、無駄な変数はスキップ *)
let rec simplify_clause_app left right =
  match left with
    | [] -> right
    | p :: rest ->
        let p' = match p with
          | Lpos x -> Lneg x
          | Lneg x -> Lpos x in
        let rec exist_p = function
          | [] -> false
          | x :: r ->
              if x = p then true
              else if x = p' then raise TautoClause
              else exist_p r in
        if exist_p right then simplify_clause_app rest right
        else p :: simplify_clause_app rest right



let rec distribute nexpl =
  let rec append_clause cnf1 cnf2 =
    match cnf1 with
      | [] -> []
      | clause :: rest ->
          fold_right
            (fun x r ->
               try
                 simplify_clause_app clause x :: r
               with
                   TautoClause -> r)
            cnf2 [] @ append_clause rest cnf2 in
  let rec distribute_rec cnf rest =
    match rest with
      | [] -> cnf
      | cnf1 :: rest1 ->
          append_clause cnf (distribute_rec cnf1 rest1) in
  match nexpl with
    | [] -> []
    | cnf :: rest -> distribute_rec cnf rest



let rec nexp_to_cnf = function
  | Npos x  -> [[ Lpos x ]]
  | Nneg x  -> [[ Lneg x ]]
  | Nand pl -> concat (map nexp_to_cnf pl)
  | Nor  pl -> distribute (map nexp_to_cnf pl)





let pexp_to_cnf p = nexp_to_cnf (not_internalization p)

let rule_to_cnf (head, body) = pexp_to_cnf (Por [Pnot head; body])

let cnf_list_to_dimacs_cnf vmap cl = concat (map (cnf_to_dimacs_cnf vmap) cl)

let input_to_dimacs_cnf vmap = map (fun p -> [ vmap p ])



(**************************************************************************************************)
(* 性質・分類によるデータの生成と変換 *)


let make_vmap defs =
  let rec iter x n = function
    | [] -> 0
    | p :: l -> if x = p then n else iter x (n+1) l in
  fun x -> iter x 1 defs


let make_nmap defs n = nth defs (n-1)


let rec make_inputlist = function
  | [] -> [[]]
  | pl :: l ->
      let pl' = make_inputlist l in
      let rec cons_constr = function
        | [] -> []
        | p :: l' -> map (fun x -> p :: x) pl' @ cons_constr l' in
        cons_constr pl




let rec def_to_restriction = function
  | [] -> []
  | a :: l ->
    (a, l) :: map (fun (p, nl) -> (p, a :: nl)) (def_to_restriction l)


let restrict_to_cnf (a, l) =
  ([Lpos a] :: map (fun x -> [Lneg x]) l)

let defs_to_cnf_restriction defs = concat (map (fun def -> distribute (map restrict_to_cnf (def_to_restriction def))) defs)




let remove_ignored out inputlist no_p =
  output_string out "// ignored by declarations for no-P tuples\n";
  iter (fun p -> output_tuple out p; output_string out "\n") no_p;
  remove_values inputlist no_p


let refine_input out inputlist p_rules vmap =
  let p_rules = cnf_list_to_dimacs_cnf vmap (map rule_to_cnf p_rules) in
  let inputlist = map (map vmap) inputlist in
  output_string out "// ignored by property rules (not satisfying the rules)\n";
  inputlist (* p_rulesとinputをsatソルバにかける。場合によっては充足・非充足を逆にする *)




(* no_pは他に使わず、また制約にも入れないものとする。そもそも入力を与えるので不要であるため。 *)
let make_defs_data pdefs cdefs no_p p_rules =
  let p_kind_num = length pdefs in
  let pdefs_concat = concat pdefs in
  let p_var_num = length pdefs_concat in
  let concatdefs = pdefs_concat @ (concat cdefs) in
  let var_num = length concatdefs in
  let vmap = make_vmap concatdefs in
  let nmap = make_nmap concatdefs in
  let out = open_out result_ignoredfilename in
  let inputlist = remove_ignored out (make_inputlist pdefs) no_p in
  let inputlist = refine_input out inputlist p_rules vmap in
  flush out; close_out out;
  let restrictions = cnf_to_dimacs_cnf vmap (defs_to_cnf_restriction (pdefs @ cdefs)) in
  {
    pdefs = pdefs;
    cdefs = cdefs;
    vmap = vmap;
    nmap = nmap;
    pred = predicate_string_of_variable pdefs cdefs;
    var_num = var_num;
    p_kind_num = p_kind_num;
    p_var_num = p_var_num;
    inputlist = inputlist;
    restrictions = restrictions
  }




(**************************************************************************************************)
(* 確定した変数のリスト作成関数 *)

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




(**************************************************************************************************)
(* 実際に行われる入力処理 *)

type rules =
  {
    defs : defs_data;
    rules : dimacs_cnf;
    cases : (int list * int list) list
  }



let get_data () =
  let out = open_out prolog_rule_output in
  let _ = init_block out in
  output_string out "%%// All properties/categories--------------------------------\n";
  let pdefs = get_defs out in
  let cdefs = get_defs out in
  let pred = predicate_string_of_variable pdefs cdefs in
  output_defs out pred pdefs cdefs;
  output_string out "%%// Input rules--------------------------------\n";
(*  output_string out "%%[rules]\n"; *)(* そういえばall_pcの末尾で終了だった *)
  let rules = get_rules pred out in
  output_string out "\n\n%%[noP section]\n";
  let no_p = get_no_p out in
  output_string out "\n\n%%[property rules section]\n";
  let p_rules = get_p_rules out in
  output_string out "\n\n%%[case rules section]\n";
  let cases = get_cases out in
  output_string out "\n\n%%[end inputs]\n";
  flush out; close_out out;
  let defs = make_defs_data pdefs cdefs no_p p_rules in
  {
    defs = defs;
    rules = cnf_list_to_dimacs_cnf defs.vmap (map rule_to_cnf rules);
    cases = map (fun (head,body) -> (map defs.vmap head, map defs.vmap body)) cases
  }



(**************************************************************************************************)
(* 総当たり検査 *)


let check_consistency cnf defs cases =
  let inputs = defs.inputlist in
  let inconsistent_num = ref 0 in
  print_string ("Consistency for each input checking :");
  print_newline ();
  iter (fun input ->
    try
      let output = snd (find (fun v -> fst v = input) cases) in
        if not (call_minisat (lift output @ lift input @ cnf) defs.var_num) then
          (print_string "Inconsistent input (with test case) : ";
           let input = map defs.nmap input in
           let output = map defs.nmap output in
           output_tuple stdout input;
           print_newline ();
           write_expect !inconsistent_num input defs (Some output);
           inconsistent_num := !inconsistent_num + 1)
    with  Not_found ->
      if not (call_minisat (lift input @ cnf) defs.var_num) then
        (print_string "Inconsistent input : ";
         let input = map defs.nmap input in
         output_tuple stdout input;
         (* print_string " (please write a test-case for this input and re-run)"; *)
         print_newline ();
         write_expect !inconsistent_num input defs None;
         inconsistent_num := !inconsistent_num + 1))
    inputs;
  if !inconsistent_num = 0
  then (print_string "OK - the rules are consistent"; print_newline (); print_newline (); true)
  else (print_string "NG - the rules are unsatsifiable with some inputs or some test cases"; print_newline (); print_newline(); false)



let check_ambiguity cnf defs cases =
  let inputs = defs.inputlist in
  let ambiguous_num = ref 0 in
  print_string ("Ambiguity for each input checking :");
  print_newline ();
  let result_file = open_out result_mapsfilename in
  let rec all_sats cnf values =
    if call_minisat cnf defs.var_num then
      (let value = get_valuation () in
         all_sats (get_valuation_inv value :: cnf) (value :: values))
    else rev values in
  output_string result_file "%%// Determined input-output (you can use this part as testcases)\n";
  iter (fun input ->
    try
      let output = snd (find (fun v -> fst v = input) cases) in
      let cur_cnf = get_valuation_inv output :: lift input @ cnf in
        (* テストケースで通ることはもう分かっているので確かめない *)
      let values = all_sats cur_cnf [] in
        if values <> [] then
          let num = !ambiguous_num in
          let amb_filename = result_ambiguous_prefix ^ string_of_int num ^ ".txt" in
          let amb_file = open_out amb_filename in
          let values = map (fun x -> snd (split_inout x defs.p_var_num)) values in
          let determined_values = determined_list output values in
          let outputs = map (map defs.nmap) (output :: values) in
          let input = map defs.nmap input in
            (print_string "Input with output differing from test-case : ";
             output_tuple stdout input;
             print_string (" -- see " ^ amb_filename);
             print_newline ();
             output_string amb_file ("% Properties\n" ^ ambiguous_property ^ "(");
             output_string amb_file (list_string_of_termlist defs.pred input);
             output_string amb_file ").\n% Categories (the first is expected output)\n";
             iter (fun x -> output_string amb_file (ambiguous_category ^ "(");
                            output_string amb_file (list_string_of_termlist defs.pred x);
                            output_string amb_file ").\n") outputs;
             output_string amb_file ("\n% Determined categorical values :\n" ^ fixed_ambiguous_category ^ "(");
             output_string amb_file (list_string_of_termlist defs.pred (map defs.nmap determined_values));
             output_string amb_file ").\n";
             flush amb_file; close_out amb_file;
             ambiguous_num := num+1)
        else
          (output_num_tuple result_file defs.nmap input;
           output_string result_file " --> *";
           output_num_tuple result_file defs.nmap output;
           output_string result_file "\n")
    with  Not_found ->
      let cur_cnf = lift input @ cnf in
        if call_minisat cur_cnf defs.var_num then
          let output = snd (split_inout (get_valuation ()) defs.p_var_num) in
          let values = all_sats (get_valuation_inv output :: cur_cnf) [] in
          if values <> [] then
            let num = !ambiguous_num in
            let amb_filename = result_ambiguous_prefix ^ string_of_int num ^ ".txt" in
            let amb_file = open_out amb_filename in
            let values = map (fun x -> snd (split_inout x defs.p_var_num)) values in
            let determined_values = determined_list output values in
            let outputs = map (map defs.nmap) (output :: values) in
            let input = map defs.nmap input in
              (print_string "Input with ambiguous outputs : ";
               output_tuple stdout input;
               print_string (" -- see " ^ amb_filename);
               print_newline ();
               output_string amb_file ("% Properties\n" ^ ambiguous_property ^ "(");
               output_string amb_file (list_string_of_termlist defs.pred input);
               output_string amb_file ").\n% Categories\n";
               iter (fun x -> output_string amb_file (ambiguous_category ^ "(");
                              output_string amb_file (list_string_of_termlist defs.pred x);
                              output_string amb_file ").\n") outputs;
               output_string amb_file ("\n% Determined categorical values :\n" ^ fixed_ambiguous_category ^ "(");
               output_string amb_file (list_string_of_termlist defs.pred (map defs.nmap determined_values));
               output_string amb_file ").\n";
               flush amb_file; close_out amb_file;
               ambiguous_num := num+1)
          else
            (output_num_tuple result_file defs.nmap input;
             output_string result_file " --> ";
             output_num_tuple result_file defs.nmap output;
             output_string result_file "\n")
        else () (* 矛盾してないなら必ず一度は成功するはずだが、変な使い方をするとここに来る可能性もある *)
       ) inputs;
  flush result_file; close_out result_file;
  if !ambiguous_num = 0
  then (print_string "OK - the rules are deterministic"; print_newline (); print_newline (); true)
  else (print_string "NG - the rules are ambiguous with some inputs"; print_newline (); print_newline(); false)





(**************************************************************************************************)
(* 処理 *)

let execute def =
  let cnf = def.rules @ def.defs.restrictions in
  check_consistency cnf def.defs def.cases
  &&
  check_ambiguity cnf def.defs def.cases
;;

execute (get_data ())
