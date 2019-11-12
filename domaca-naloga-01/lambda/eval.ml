module S = Syntax


let rec is_value = function
  | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _  |  S.Nil -> true
  | S.Var _ | S.Plus _ | S.Minus _ | S.Times _ | S.Equal _ | S.Less _ | S.Greater _
  | S.IfThenElse _ | S.Apply _ | S.Fst _ | S.Snd _ | S.Match _ -> false
  | S.Cons (car, cdr) -> if (is_value car && is_value cdr) then true else false
  | S.Pair (x, y) -> if (is_value x && is_value y) then true else false


let rec eval_exp = function
  | S.Var x -> failwith "Expected a closed term"
  | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ as e -> e
  | S.Pair (e1, e2) when not (is_value e1 && is_value e2) ->
    let xe1 = eval_exp e1
    and xe2 = eval_exp e2
    in S.Pair(xe1, xe2)
  | S.Cons (e1, e2) when not (is_value e1 && is_value e2) ->
    let xe1 = eval_exp e1
    and xe2 = eval_exp e2
    in S.Cons(xe1, xe2)
  | S.Pair _ as e -> e
  | S.Cons _ as e -> e
  | S.Plus (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Int (n1 + n2)
  | S.Minus (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Int (n1 - n2)
  | S.Times (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Int (n1 * n2)
  | S.Equal (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Bool (n1 = n2)
  | S.Less (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Bool (n1 < n2)
  | S.Greater (e1, e2) ->
      let n1 = eval_int e1
      and n2 = eval_int e2
      in S.Bool (n1 > n2)
  | S.IfThenElse (e, e1, e2) ->
      begin match eval_exp e with
      | S.Bool true -> eval_exp e1
      | S.Bool false -> eval_exp e2
      | _ -> failwith "Boolean expected"
      end
  | S.Apply (e1, e2) ->
      let f = eval_exp e1
      and v = eval_exp e2
      in
      begin match f with
      | S.Lambda (x, e) -> eval_exp (S.subst [(x, v)] e)
      | S.RecLambda (f, x, e) as rec_f -> eval_exp (S.subst [(f, rec_f); (x, v)] e)
      | _ -> failwith "Function expected"
      end
  | S.Nil -> Nil
  | S.Fst (S.Cons (x, y)) -> eval_exp x
  | S.Fst (S.Pair (x, y)) -> eval_exp x
  | S.Snd (S.Cons (x, y)) -> eval_exp y
  | S.Snd (S.Pair (x, y)) -> eval_exp y
  | S.Fst _ -> failwith "expected list or pair for Fst"
  | S.Snd _ -> failwith  "expected list or pair for Snd"
  | S.Match (e, e1, x, xs, e2) ->
    begin match eval_exp e with
      | S.Nil -> e1
      | S.Cons (car, cdr) ->
        let newcont = S.subst [(x, car)] e2
        in eval_exp (S.subst [(xs, cdr)] newcont)
      | _ -> failwith "list expected"
    end
  (* for lazy evaluation
  | S.Pair (e1, e2) ->
    let n1 = eval_int e1
    and n2 = eval_int e2
        in S.Pair(n1, n2) *)


and eval_int e =
  match eval_exp e with
  | S.Int n -> n
  | _ -> failwith "Integer expected"


let rec step = function
  | S.Var _ | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ | S.Nil -> failwith "Expected a non-terminal expression"
  | S.Pair (x, y) when (is_value x && is_value y) -> failwith "Expected non-terminal expression"
  | S.Cons _ as x when is_value x -> failwith "Expected non-terminal expression"
  | S.Pair _ as x when is_value x -> failwith "Expected non-terminal expression"
  | S.Plus (S.Int n1, S.Int n2) -> S.Int (n1 + n2)
  | S.Plus (S.Int n1, e2) -> S.Plus (S.Int n1, step e2)
  | S.Plus (e1, e2) -> S.Plus (step e1, e2)
  | S.Minus (S.Int n1, S.Int n2) -> S.Int (n1 - n2)
  | S.Minus (S.Int n1, e2) -> S.Minus (S.Int n1, step e2)
  | S.Minus (e1, e2) -> S.Minus (step e1, e2)
  | S.Times (S.Int n1, S.Int n2) -> S.Int (n1 * n2)
  | S.Times (S.Int n1, e2) -> S.Times (S.Int n1, step e2)
  | S.Times (e1, e2) -> S.Times (step e1, e2)
  | S.Equal (S.Int n1, S.Int n2) -> S.Bool (n1 = n2)
  | S.Equal (S.Int n1, e2) -> S.Equal (S.Int n1, step e2)
  | S.Equal (e1, e2) -> S.Equal (step e1, e2)
  | S.Less (S.Int n1, S.Int n2) -> S.Bool (n1 < n2)
  | S.Less (S.Int n1, e2) -> S.Less (S.Int n1, step e2)
  | S.Less (e1, e2) -> S.Less (step e1, e2)
  | S.Greater (S.Int n1, S.Int n2) -> S.Bool (n1 > n2)
  | S.Greater (S.Int n1, e2) -> S.Greater (S.Int n1, step e2)
  | S.Greater (e1, e2) -> S.Greater (step e1, e2)
  | S.IfThenElse (S.Bool b, e1, e2) -> if b then e1 else e2
  | S.IfThenElse (e, e1, e2) -> S.IfThenElse (step e, e1, e2)
  | S.Apply (S.Lambda (x, e), v) when is_value v -> S.subst [(x, v)] e
  | S.Apply (S.RecLambda (f, x, e) as rec_f, v) when is_value v -> S.subst [(f, rec_f); (x, v)] e
  | S.Apply ((S.Lambda _ | S.RecLambda _) as f, e) -> S.Apply (f, step e)
  | S.Apply (e1, e2) -> S.Apply (step e1, e2)
  | S.Pair (first, second) ->
    if is_value first then
      S.Pair (first, step second)
    else
      S.Pair (step first, second)
  | S.Cons (car, cdr) ->
    if is_value car then
      S.Cons (car, step cdr)
    else
      S.Cons (step car, cdr)
  | S.Fst (S.Pair (x, y)) -> x
  | S.Fst (S.Cons (car, cdr)) -> step car (* why not *)
  | S.Fst _ -> failwith "expected list or pair for Fst"
  | S.Snd (S.Pair (x, y)) -> y
  | S.Snd (S.Cons (car, cdr)) -> step cdr (* acts as tail *)
  | S.Snd _ -> failwith "expected list or pair for Snd"
  | S.Match (e, e1, x, xs, e2) ->
    begin match e with
      | S.Nil -> step e1
      | S.Cons (car, cdr) ->
        let newcont = S.subst [(x, car)] e2
        in step (S.subst [(xs, cdr)] newcont)
      | _ -> failwith "list expected"
    end

let big_step e =
  let v = eval_exp e in
  print_endline (S.string_of_exp v)

let rec small_step e =
  print_endline (S.string_of_exp e);
  if not (is_value e) then
    (print_endline "  ~>";
    small_step (step e))