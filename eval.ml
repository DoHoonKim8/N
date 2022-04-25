open Tml
open Map
exception NotImplemented
exception Stuck
exception NotConvertible

type stoval = 
  Computed of value
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = (index * Heap.loc) list

 and value =
   Closure of env * exp
   | Pair_Val of env * exp * exp
   | Unit_Val
   | Inl_Val of env * exp
   | Inr_Val of env * exp
   | Fun_Val of env * exp
   | True_Val
   | False_Val
   | Num_Val of int
   | Plus_Val
   | Minus_Val
   | Eq_Val

 and frame =
   Loc_frame of Heap.loc
   | App_frame of env * exp
   | Fst_frame of env
   | Snd_frame of env
   | Case_frame of env * exp * exp
   | Ifthenelse_frame of env * exp * exp
   | Plus_frame1 of env
   | Plus_frame2 of env * exp
   | Plus_frame3 of value * env
   | Minus_frame1 of env
   | Minus_frame2 of env * exp
   | Minus_frame3 of value * env
   | Eq_frame1 of env
   | Eq_frame2 of env * exp
   | Eq_frame3 of value * env

(* Define your own empty environment *)
let emptyEnv = []

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp v =
  match v with
    Unit_Val -> Eunit
  | True_Val -> True
  | False_Val -> False
  | Num_Val n -> Num n
  | _ -> raise NotConvertible

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
module IndexTbl = Map.Make(String)

module NamingContext =
  struct
    let indexTbl = ref IndexTbl.empty

    let add v index =
      indexTbl := IndexTbl.add v index !indexTbl

    let find v = IndexTbl.find v !indexTbl

    let freeIndex = ref 0

    let initFreeIndex () =
      let _ = freeIndex := 0 in
      !freeIndex

    let getFreshFreeIndex () =
      let _ = freeIndex := !freeIndex + 1 in
      !freeIndex

    let flush () =
      let _ = indexTbl := IndexTbl.empty in
      let _ = initFreeIndex () in
      ()

    let rec build boundVars texpr =
      match texpr with
        Tvar v when not (List.mem v boundVars) ->
          if IndexTbl.is_empty !indexTbl then
            let index = initFreeIndex () in
            add v index
          else
            (match IndexTbl.find_opt v !indexTbl with
              Some index -> ()
            | None -> add v (getFreshFreeIndex ()))
      | Tlam (v, _, body) -> build (v::boundVars) body
      | Tapp (te, te') | Tpair (te, te') ->
        build boundVars te';
        build boundVars te
      | Tfst te | Tsnd te -> build boundVars te
      | Tinl (te, _) | Tinr (te, _) -> build boundVars te
      | Tcase (te, v', te', v'', te'') ->
        build (v''::boundVars) te'';
        build (v'::boundVars) te';
        build boundVars te
      | Tfix (v, _, te) -> build (v::boundVars) te
      | Tifthenelse (te, te', te'') ->
        build boundVars te'';
        build boundVars te';
        build boundVars te
      | _ -> ()
  end

type lambdaBinders = var list

let tryGetBoundedIndex lambdaBinders v =
  let rec search lambdaBinders index =
    match lambdaBinders with
      [] -> None
    | hd::tl when hd = v -> Some index
    | hd::tl -> search tl (index + 1)
  in
  search lambdaBinders 0

let findIndex lambdaBinders v =
  match tryGetBoundedIndex lambdaBinders v with
    Some index -> Ind index
  | None -> Ind (NamingContext.find v + List.length lambdaBinders)

let texp2exp texpr =
  let rec walkTexp lambdaBinders texpr =
    match texpr with
      Tvar v -> findIndex lambdaBinders v
    | Tlam (v, _, body) -> Lam (walkTexp (v::lambdaBinders) body)
    | Tapp (te, te') ->
      App (walkTexp lambdaBinders te, walkTexp lambdaBinders te')
    | Tpair (te, te') ->
      Pair (walkTexp lambdaBinders te, walkTexp lambdaBinders te')
    | Tfst te -> Fst (walkTexp lambdaBinders te)
    | Tsnd te -> Snd (walkTexp lambdaBinders te)
    | Teunit -> Eunit
    | Tinl (te, _) -> Inl (walkTexp lambdaBinders te)
    | Tinr (te, _) -> Inr (walkTexp lambdaBinders te)
    | Tcase (te, v', te', v'', te'') ->
      Case (walkTexp lambdaBinders te,
            walkTexp (v'::lambdaBinders) te',
            walkTexp (v''::lambdaBinders) te'')
    | Tfix (v, _, te) -> Fix (walkTexp (v::lambdaBinders) te)
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse (cond, te, te') ->
      Ifthenelse (walkTexp lambdaBinders cond,
                  walkTexp lambdaBinders te,
                  walkTexp lambdaBinders te')
    | Tnum n -> Num n
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
  in
  NamingContext.flush ();
  NamingContext.build [] texpr;
  walkTexp [] texpr

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)

(* shift the free variable of e by n *)
let rec shift i n e =
  match e with
    Ind m -> if m >= i then Ind (m + n) else Ind m
  | Lam e -> Lam (shift (i + 1) n e)
  | App (e, e') -> App (shift i n e, shift i n e')
  | Pair (e, e') -> Pair (shift i n e, shift i n e')
  | Fst e -> Fst (shift i n e)
  | Snd e -> Snd (shift i n e)
  | Inl e -> Inl (shift i n e)
  | Inr e -> Inr (shift i n e)
  | Case (e, e', e'') ->
    Case (shift i n e, shift (i + 1) n e', shift (i + 1) n e'')
  | Fix e -> Fix (shift (i + 1) n e)
  | Ifthenelse (cond, e, e') ->
    Ifthenelse (shift i n cond, shift i n e, shift i n e')
  | _ -> e

(* substitute de Bruijn index n in e with a value v *)
let rec substitute n e v =
  match e with
    Ind m ->
      if m < n then Ind m
      else if m = n then shift 0 n v
      else Ind (m - 1)
  | Lam e -> Lam (substitute (n + 1) e v)
  | App (e, e') -> App (substitute n e v, substitute n e' v)
  | Pair (e, e') -> Pair (substitute n e v, substitute n e' v)
  | Fst e -> Fst (substitute n e v)
  | Snd e -> Snd (substitute n e v)
  | Inl e -> Inl (substitute n e v)
  | Inr e -> Inr (substitute n e v)
  | Case (e, e', e'') ->
    Case (substitute n e v, substitute (n + 1) e' v, substitute (n + 1) e'' v)
  | Fix e -> Fix (substitute (n + 1) e v)
  | Ifthenelse (cond, e, e') ->
    Ifthenelse (substitute n cond v, substitute n e v, substitute n e' v)
  | _ -> e

let rec isValue expr =
  match expr with
    Lam _
  | Eunit
  | True
  | False
  | Num _
  | Plus
  | Minus
  | Eq -> true
  | Pair (e, e') -> isValue e && isValue e'
  | Inl e
  | Inr e -> isValue e
  | _ -> false

let rec step1 expr =
  match expr with
    Ind _
  | Lam _
  | Eunit
  | True
  | False
  | Num _
  | Plus
  | Minus
  | Eq -> raise Stuck
  | Pair (v, v') when isValue v && isValue v' -> raise Stuck
  | Inl v when isValue v -> raise Stuck
  | Inr v when isValue v -> raise Stuck
  | App (Plus, Pair (Num n1, Num n2)) -> Num (n1 + n2)
  | App (Plus, e) -> App (Plus, step1 e)
  | App (Minus, Pair (Num n1, Num n2)) -> Num (n1 - n2)
  | App (Minus, e) -> App (Minus, step1 e)
  | App (Eq, Pair (Num n1, Num n2)) ->
    if n1 = n2 then True else False
  | App (Eq, e) -> App (Eq, step1 e)
  | App (Lam e, v) when isValue v -> substitute 0 e v
  | App (Lam _ as la, e) -> App (la, step1 e)
  | App (e, e') -> App (step1 e, e')
  | Pair (v, e) when isValue v -> Pair (v, step1 e)
  | Pair (e, e') -> Pair (step1 e, e')
  | Fst (Pair (v, v')) when isValue v && isValue v' -> v
  | Fst e -> Fst (step1 e)
  | Snd (Pair (v, v')) when isValue v && isValue v' -> v'
  | Snd e -> Snd (step1 e)
  | Inl e -> Inl (step1 e)
  | Inr e -> Inr (step1 e)
  | Case (Inl v, e, _) when isValue v -> substitute 0 e v
  | Case (Inr v, _, e) when isValue v -> substitute 0 e v
  | Case (e, e', e'') -> Case (step1 e, e', e'')
  | Fix e -> substitute 0 e (Fix e)
  | Ifthenelse (True, e, _)
  | Ifthenelse (False, _, e) -> step1 e
  | Ifthenelse (cond, e, e') -> Ifthenelse (step1 cond, e, e')

(* Problem 3. 
 * step2 : state -> state *)
let incr_env env = List.map (fun (n, l) -> (n + 1, l)) env

let find_loc env n =
  try
    match List.find (fun (m, _) -> m = n) env with
      (_, l) -> l
  with Not_found -> raise Stuck

let step2 s =
  match s with
    Anal_ST (h, stack, Ind n, env) ->
      let l = find_loc env n in
      (match Heap.deref h l with
         Computed v -> Return_ST (h, stack, v)
       | Delayed (expr, env') -> Anal_ST (h, Frame_SK (stack, Loc_frame l), expr, env'))
  | Anal_ST (h, stack, Lam e, env) ->
    Return_ST (h, stack, Closure (env, Lam e))
  | Anal_ST (h, stack, App (e, e'), env) ->
    Anal_ST (h, Frame_SK (stack, App_frame (env, e')), e, env)
  | Anal_ST (h, stack, Pair (e, e'), env) -> Return_ST (h, stack, Pair_Val (env, e, e'))
  | Anal_ST (h, stack, Fst (Pair (e, e')), env) -> Anal_ST (h, stack, e, env)
  | Anal_ST (h, stack, Fst e, env) ->
    Anal_ST (h, Frame_SK (stack, Fst_frame env), e, env)
  | Anal_ST (h, stack, Snd (Pair (e, e')), env) -> Anal_ST (h, stack, e', env)
  | Anal_ST (h, stack, Snd e, env) ->
    Anal_ST (h, Frame_SK (stack, Snd_frame env), e, env)
  | Anal_ST (h, stack, Eunit, env) -> Return_ST (h, stack, Unit_Val)
  | Anal_ST (h, stack, Inl e, env) -> Return_ST (h, stack, Inl_Val (env, e))
  | Anal_ST (h, stack, Inr e, env) -> Return_ST (h, stack, Inr_Val (env, e))
  | Anal_ST (h, stack, Case (Inl e, e', _), env)
  | Anal_ST (h, stack, Case (Inr e, _, e'), env) ->
    let (h', l) = Heap.allocate h (Delayed (e, env)) in
    let env' = incr_env env in
    let env' = (0, l) :: env' in
    Anal_ST (h', stack, e', env')
  | Anal_ST (h, stack, Case (e, e', e''), env) ->
    Anal_ST (h, Frame_SK (stack, Case_frame (env, e', e'')), e, env)
  | Anal_ST (h, stack, Fix (Lam e), env) -> Return_ST (h, stack, Fun_Val (env, Fix (Lam e)))
  | Anal_ST (h, stack, True, env) -> Return_ST (h, stack, True_Val)
  | Anal_ST (h, stack, False, env) -> Return_ST (h, stack, False_Val)
  | Anal_ST (h, stack, Ifthenelse (True, e, _), env)
  | Anal_ST (h, stack, Ifthenelse (False, _, e), env) -> Anal_ST (h, stack, e, env)
  | Anal_ST (h, stack, Ifthenelse (cond, e, e'), env) ->
    Anal_ST (h, Frame_SK (stack, Ifthenelse_frame (env, e, e')), cond, env)
  | Anal_ST (h, stack, Num n, env) -> Return_ST (h, stack, Num_Val n)
  | Anal_ST (h, stack, Plus, env) -> Return_ST (h, stack, Plus_Val)
  | Anal_ST (h, stack, Minus, env) -> Return_ST (h, stack, Minus_Val)
  | Anal_ST (h, stack, Eq, env) -> Return_ST (h, stack, Eq_Val)
  | Return_ST (h, Frame_SK (stack, App_frame (env, e')), Closure (env', Lam e)) ->
    let (h', l) = Heap.allocate h (Delayed (e', env)) in
    let env'' = incr_env env' in
    let env'' = (0, l) :: env'' in
    Anal_ST (h', stack, e, env'')
  | Return_ST (h, Frame_SK (stack, App_frame (env, e')), Fun_Val (env', Fix (Lam e))) ->
    let (h', l) = Heap.allocate h (Computed (Fun_Val (env', Fix (Lam e)))) in
    let (h', l') = Heap.allocate h' (Delayed (e', env)) in
    let env'' = incr_env env' in
    let env'' = (0, l) :: (1, l') :: env'' in
    Anal_ST (h', stack, e, env'')
  | Return_ST (h, Frame_SK (stack, App_frame (env, e')), Plus_Val) ->
    Anal_ST (h, Frame_SK (stack, Plus_frame1 env), e', env)
  | Return_ST (h, Frame_SK (stack, App_frame (env, e')), Minus_Val) ->
    Anal_ST (h, Frame_SK (stack, Minus_frame1 env), e', env)
  | Return_ST (h, Frame_SK (stack, App_frame (env, e')), Eq_Val) ->
    Anal_ST (h, Frame_SK (stack, Eq_frame1 env), e', env)
  | Return_ST (h, Hole_SK, v) -> raise Stuck
  | Return_ST (h, Frame_SK (stack, Loc_frame l), v) ->
    (match Heap.deref h l with
     | Computed _ -> Return_ST (h, stack, v)
     | Delayed (expr, env) ->
       let h' = Heap.update h l (Computed v) in
       Return_ST (h', stack, v))
  | Return_ST (h, Frame_SK (stack, Fst_frame _), Pair_Val (env, e, _))
  | Return_ST (h, Frame_SK (stack, Snd_frame _), Pair_Val (env, _, e)) ->
    Anal_ST (h, stack, e, env)
  | Return_ST (h, Frame_SK (stack, Case_frame (env, e', _)), Inl_Val (env', e))
  | Return_ST (h, Frame_SK (stack, Case_frame (env, _, e')), Inr_Val (env', e)) ->
    let (h', l) = Heap.allocate h (Delayed (e, env')) in
    let env'' = incr_env env in
    let env'' = (0, l) :: env'' in
    Anal_ST (h', stack, e', env'')
  | Return_ST (h, Frame_SK (stack, Ifthenelse_frame (env, e, _)), True_Val)
  | Return_ST (h, Frame_SK (stack, Ifthenelse_frame (env, _, e)), False_Val) ->
    Anal_ST (h, stack, e, env)
  | Return_ST (h, Frame_SK (stack, Plus_frame1 _), Pair_Val (env', e, e')) ->
    Anal_ST (h, Frame_SK (stack, Plus_frame2 (env', e')), e, env')
  | Return_ST (h, Frame_SK (stack, Plus_frame2 (env, e)), Num_Val n) ->
    Anal_ST (h, Frame_SK (stack, Plus_frame3 (Num_Val n, env)), e, env)
  | Return_ST (h, Frame_SK (stack, Plus_frame3 (Num_Val n1, env)), Num_Val n2) ->
    Return_ST (h, stack, Num_Val (n1 + n2))
  | Return_ST (h, Frame_SK (stack, Minus_frame1 _), Pair_Val (env', e, e')) ->
    Anal_ST (h, Frame_SK (stack, Minus_frame2 (env', e')), e, env')
  | Return_ST (h, Frame_SK (stack, Minus_frame2 (env, e)), Num_Val n) ->
    Anal_ST (h, Frame_SK (stack, Minus_frame3 (Num_Val n, env)), e, env)
  | Return_ST (h, Frame_SK (stack, Minus_frame3 (Num_Val n1, env)), Num_Val n2) ->
    Return_ST (h, stack, Num_Val (n1 - n2))
  | Return_ST (h, Frame_SK (stack, Eq_frame1 _), Pair_Val (env', e, e')) ->
    Anal_ST (h, Frame_SK (stack, Eq_frame2 (env', e')), e, env')
  | Return_ST (h, Frame_SK (stack, Eq_frame2 (env, e)), Num_Val n) ->
    Anal_ST (h, Frame_SK (stack, Eq_frame3 (Num_Val n, env)), e, env)
  | Return_ST (h, Frame_SK (stack, Eq_frame3 (Num_Val n1, env)), Num_Val n2) ->
    if n1 = n2 then Return_ST (h, stack, True_Val) else Return_ST (h, stack, False_Val)
  | _ -> raise Stuck

(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let rec env2string env = match env with
    [] -> "η0"
  | (n, l) :: tl -> env2string tl ^ ", " ^ (string_of_int n) ^ " -> " ^ (string_of_int l)

let frame2string f = match f with
     Loc_frame l -> "[" ^ (string_of_int l) ^ "]"
   | App_frame (env, exp) -> "□_{" ^ (env2string env) ^ "} " ^ (exp2string exp) 
   | Fst_frame env -> "fst " ^ (env2string env)
   | Snd_frame env -> "snd " ^ (env2string env)
   | Case_frame (env, exp, exp') -> 
     "Case □_{" ^ (env2string env) ^ "} | Inl " ^ (exp2string exp) ^ " | Inr " ^ (exp2string exp')
   | Ifthenelse_frame (env, exp, exp') -> 
     "if □_{" ^ (env2string env) ^ "} then " ^ (exp2string exp) ^ " else " ^ (exp2string exp')
   | Plus_frame1 env -> "+ □_{" ^ (env2string env) ^ "}" 
   | Plus_frame2 (env, exp) -> ""
   | Plus_frame3 (value, env) -> ""
   | Minus_frame1 env -> "- □_{" ^ (env2string env) ^ "}"
   | Minus_frame2 (env, exp) -> ""
   | Minus_frame3 (value, env) -> ""
   | Eq_frame1 env -> "= □_{" ^ (env2string env) ^ "}"
   | Eq_frame2 (env, exp) -> ""
   | Eq_frame3 (value, env) -> ""

let rec stack2string s = match s with
    Hole_SK -> "□"
  | Frame_SK (stack, frame) -> stack2string stack ^ ", " ^ (frame2string frame)

let val2string v = match v with
    Closure (env, exp) -> "[ " ^ (env2string env) ^ ", " ^ exp2string exp ^ " ]"
  | Fun_Val (env, Fix (Lam exp)) -> "[ " ^ (env2string env) ^ ", fun f x:A." ^ exp2string exp ^ " ]"
  | Pair_Val (env, exp, exp') -> "(" ^ (exp2string exp) ^ ", " ^ (exp2string exp') ^ ")"
  | Unit_Val -> "()"
  | Inl_Val (env, e) -> "Inl " ^ (exp2string e)
  | Inr_Val (env, e) -> "Inr " ^ (exp2string e)
  | True_Val -> "True"
  | False_Val -> "False"
  | Num_Val n -> "n"
  | Plus_Val -> "+"
  | Minus_Val -> "-"
  | Eq_Val -> "="

let state2string st = match st with
    Anal_ST(h,stack,exp,env) -> 
    "Analysis : " ^ (stack2string stack) ^ " |> " ^ exp2string exp ^ " @ " ^ env2string env
  | Return_ST(_,stack,v) -> "Return : " ^ (stack2string stack) ^ " <| " ^ (val2string v)

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
