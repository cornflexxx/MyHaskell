exception NotEvaluable of string
exception TypeError
exception NotComparable
exception InvalidOperandType of string
(* TODO: Manage exception*)
(* Types *)

datatype Ordering =
  LT
| EQ
| GT
datatype HaskellType =
  HsInt_t
| HsInteger_t
| HsFloat_t
| HsChar_t
| HsBool_t
| HsList_t of HaskellType
| HsTuple_t of HaskellType
| HsUnit_t
| HsArrow_t of HaskellType * HaskellType
| HsAbstract_t

(* Default typeclass *)
datatype TypeClass =
  Num of HaskellType
| Ord of HaskellType
| Eq of HaskellType
| Fractional of HaskellType
| Read of HaskellType
| Show of HaskellType
| Integral of HaskellType
(* Custom TypeClasses*)
(* signature CUSTOMTYPECLASS
TODO: Functor to create Custom TypeClasses *)

(* Working types *)
datatype HaskellValue =
  HsInt_v of int
| HsInteger_v of LargeInt.int
| HsFloat_v of real
| HsChar_v of char
| HsBool_v of bool
| HsOrdering_v of Ordering
| HsList_v of HaskellValue list
| HsTuple_v of HaskellValue list
| HsUnit_v of unit
| INF
(*Lazy list, methods and list comprehension *)

(* MyHaskell expressions *)
and HaskellFun =
  K of HaskellValue
| Var of string
| Plus of HaskellFun * HaskellFun
| Minus of HaskellFun * HaskellFun
| Mul of HaskellFun * HaskellFun
| Equal of HaskellFun * HaskellFun
| Lt of HaskellFun * HaskellFun
| Le of HaskellFun * HaskellFun
| Gt of HaskellFun * HaskellFun
| Ge of HaskellFun * HaskellFun
| Bind of HaskellFun * HaskellFun
| Function of HaskellFun * HaskellFun list * HaskellFun
| Guard of HaskellFun * ((HaskellFun * HaskellFun) list)
| Call of (HaskellFun * HaskellFun list)
| If of HaskellFun * HaskellFun * HaskellFun
| Let of HaskellFun * HaskellFun
| Lambda of HaskellFun * HaskellFun
| Closure of HaskellFun list * HaskellFun

(* Enviroment *)
signature ENV =
sig
  exception RefNotFound
  datatype HsEnv =
    Empty_hs
  | Cons_hs of (HaskellFun * HaskellFun * HsEnv) * HsEnv
  val binding: HaskellFun * HaskellFun * HsEnv * HsEnv -> HsEnv
  val solve_ref: HaskellFun * HsEnv -> HaskellFun * HsEnv
  val clean: HsEnv -> HsEnv
  val bind_list: HaskellFun list * HaskellFun list * HsEnv * HsEnv -> HsEnv
  val bind_curried: HaskellFun * HaskellFun list * HsEnv * HaskellFun * HsEnv
                    -> HsEnv * HaskellFun
end

structure Env :> ENV =
struct

  exception RefNotFound
  exception CantBind

  datatype HsEnv =
    Empty_hs
  | Cons_hs of (HaskellFun * HaskellFun * HsEnv) * HsEnv
  fun binding (Var x, exp, env, env') =
        Cons_hs ((Var x, exp, env), env')
    | binding (_, _, _, _) = raise CantBind
  fun solve_ref (Var x, Cons_hs ((Var y, exp, env'), env)) =
        (if x = y then (exp, env') else solve_ref (Var x, env))
    | solve_ref (_, _) = raise RefNotFound
  fun clean (Cons_hs ((_, _, _), env)) = env
    | clean _ = raise RefNotFound
  fun bind_list (_, [], _, env') = env'
    | bind_list (Var p :: params, expr :: exprs, env, env') =
        Cons_hs ((Var p, expr, env), bind_list (params, exprs, env, env'))
    | bind_list _ = raise CantBind
  fun bind_curried (Var par, arg :: args, env, Lambda (Var par', body'), env'') =
        let
          val (env', lambda) = bind_curried (Var par', args, env, body', env'')
        in
          (Cons_hs ((Var par, arg, env), env'), lambda)
        end
    | bind_curried (Var par, arg :: [], env, body, env'') =
        (Cons_hs ((Var par, arg, env), env''), body)
    | bind_curried (_, [], _, body, env'') = (env'', body)
    | bind_curried _ = raise CantBind


end


(* Context for type inference *)
signature CONTEXT =
sig
  exception TypeNotFound
  datatype HsContext =
    Empty_hs
  | Cons_hs of (HaskellFun * HaskellType) * HsContext
  val cntxt_search: HaskellFun * HsContext -> HaskellType

end

structure Context :> CONTEXT =
struct
  exception TypeNotFound
  datatype HsContext =
    Empty_hs
  | Cons_hs of (HaskellFun * HaskellType) * HsContext
  fun cntxt_search (Var x, Cons_hs ((Var y, typ), cntxt)) =
        if x = y then typ else cntxt_search (Var x, cntxt)
    | cntxt_search (_, _) = HsAbstract_t
end

signature TYPEOP =
sig
  val compare: HaskellType * HaskellType -> HaskellType
end

structure TypeOp :> TYPEOP =
struct
  fun compare (HsFloat_t, HsInt_t) = HsFloat_t
    | compare (HsInt_t, HsFloat_t) = HsFloat_t
    | compare (HsFloat_t, HsInteger_t) = HsFloat_t
    | compare (HsInteger_t, HsFloat_t) = HsFloat_t
    | compare (HsInt_t, HsInteger_t) = HsInteger_t
    | compare (HsInteger_t, HsInt_t) = HsInteger_t
    | compare (HsInt_t, HsInt_t) = HsInt_t
    | compare (HsFloat_t, HsFloat_t) = HsFloat_t
    | compare (HsInteger_t, HsInteger_t) = HsInteger_t
    | compare (HsBool_t, HsBool_t) = HsBool_t
    | compare (HsList_t typ, HsList_t typ') = compare (typ, typ')
    | compare (HsTuple_t typ, HsTuple_t typ') = compare (typ, typ')
    | compare (HsChar_t, HsChar_t) = HsChar_t
    | compare _ = raise NotComparable


end


signature BOOLOP =
sig
  val and_hs: HaskellValue * HaskellValue -> HaskellValue
  val or_hs: HaskellValue * HaskellValue -> HaskellValue
  val not_hs: HaskellValue -> HaskellValue
end

structure BoolOp :> BOOLOP =
struct
  fun and_hs (HsBool_v a, HsBool_v b) =
        HsBool_v (a andalso b)
    | and_hs (_, _) = raise InvalidOperandType "Invalid operand type"
  fun or_hs (HsBool_v a, HsBool_v b) =
        HsBool_v (a orelse b)
    | or_hs (_, _) = raise InvalidOperandType "Invalid operand type"
  fun not_hs (HsBool_v a) =
        HsBool_v (not a)
    | not_hs _ = raise InvalidOperandType "Invalid operand type"
end


signature EQ =
sig
  val eq: HaskellValue * HaskellValue -> HaskellValue
end

structure Eq :> EQ =
struct
  fun eq (HsInt_v a, HsInt_v b) =
        HsBool_v (a = b)
    | eq (HsInteger_v a, HsInteger_v b) =
        HsBool_v
          (case LargeInt.compare (a, b) of
             EQUAL => true
           | _ => false)
    | eq (HsFloat_v a, HsFloat_v b) =
        HsBool_v
          (case Real.compare (a, b) of
             EQUAL => true
           | _ => false)
    | eq (HsChar_v a, HsChar_v b) =
        HsBool_v (a = b)
    | eq (HsList_v (a :: l), HsList_v (b :: l')) =
        BoolOp.and_hs (eq (a, b), eq (HsList_v l, HsList_v l'))
    | eq (HsBool_v a, HsBool_v b) =
        HsBool_v (a = b)
    | eq (HsUnit_v a, HsUnit_v b) =
        HsBool_v (a = b)
    | eq (HsTuple_v (a :: l), HsTuple_v (b :: l')) =
        BoolOp.and_hs (eq (a, b), eq (HsTuple_v l, HsTuple_v l'))
    | eq (INF, INF) = HsBool_v true
    | eq (HsInt_v _, INF) = HsBool_v false
    | eq (HsInteger_v _, INF) = HsBool_v false
    | eq (HsFloat_v _, INF) = HsBool_v false
    | eq (HsBool_v _, INF) = HsBool_v false
    | eq (_, _) = raise NotComparable
end
(* Some numerical operation *)
signature NUM =
sig
  val plus: HaskellValue * HaskellValue -> HaskellValue
  val mul: HaskellValue * HaskellValue -> HaskellValue
  val minus: HaskellValue * HaskellValue -> HaskellValue
(*val sign: num * num -> num
val abs: num * num -> num
val negate: num * num -> num*)
end

structure Num :> NUM =
struct

  fun plus (HsInt_v a, HsInt_v b) =
        HsInt_v (a + b)
    | plus (HsInteger_v a, HsInteger_v b) =
        HsInteger_v (LargeInt.+ (a, b))
    | plus (HsFloat_v a, HsFloat_v b) =
        HsFloat_v (Real.+ (a, b))
    | plus (HsInt_v i, HsFloat_v f) =
        HsFloat_v (Real.+ ((Real.fromInt i), f))
    | plus (HsFloat_v f, HsInt_v i) =
        HsFloat_v (Real.+ (f, (Real.fromInt i)))
    | plus (_, _) = raise InvalidOperandType "Invalid operand type"
  fun mul (HsInt_v a, HsInt_v b) =
        HsInt_v (a * b)
    | mul (HsInteger_v a, HsInteger_v b) =
        HsInteger_v (LargeInt.* (a, b))
    | mul (HsFloat_v a, HsFloat_v b) =
        HsFloat_v (Real.* (a, b))
    | mul (HsInt_v i, HsFloat_v f) =
        HsFloat_v (Real.* ((Real.fromInt i), f))
    | mul (HsFloat_v f, HsInt_v i) =
        HsFloat_v (Real.* (f, (Real.fromInt i)))
    | mul (_, _) = raise InvalidOperandType "Invalid operand type"
  fun minus (HsInt_v a, HsInt_v b) =
        HsInt_v (a - b)
    | minus (HsInteger_v a, HsInteger_v b) =
        HsInteger_v (LargeInt.- (a, b))
    | minus (HsFloat_v a, HsFloat_v b) =
        HsFloat_v (Real.- (a, b))
    | minus (HsInt_v i, HsFloat_v f) =
        HsFloat_v (Real.- ((Real.fromInt i), f))
    | minus (HsFloat_v f, HsInt_v i) =
        HsFloat_v (Real.- (f, (Real.fromInt i)))
    | minus (_, _) = raise InvalidOperandType "Invalid operand type"
end
(* Other typeclasses  Show, Read, Functor *)
signature ORD =
sig
  val lt: HaskellValue * HaskellValue -> HaskellValue
  val le: HaskellValue * HaskellValue -> HaskellValue
  val gt: HaskellValue * HaskellValue -> HaskellValue
  val ge: HaskellValue * HaskellValue -> HaskellValue
  val min: HaskellValue * HaskellValue -> HaskellValue
  val max: HaskellValue * HaskellValue -> HaskellValue
end

val env_tmp = ref Env.Empty_hs
val cntxt_tmp = ref Context.Empty_hs

structure Ord :> ORD =
struct
  fun lt (HsInt_v a, HsInt_v b) =
        HsBool_v (a < b)
    | lt (HsInteger_v a, HsInteger_v b) =
        HsBool_v
          (case LargeInt.compare (a, b) of
             LESS => true
           | _ => false)
    | lt (HsFloat_v a, HsFloat_v b) =
        HsBool_v (a < b)
    | lt (HsFloat_v a, HsInt_v b) =
        HsBool_v (a < Real.fromInt b)
    | lt (HsInt_v a, HsFloat_v b) =
        HsBool_v (Real.fromInt a < b)
    | lt (HsBool_v a, HsBool_v b) =
        HsBool_v
          (case (a, b) of
             (false, true) => true
           | _ => false)
    | lt (HsChar_v a, HsChar_v b) =
        HsBool_v (a < b)
    | lt (HsList_v (a :: l), HsList_v (b :: l')) =
        (case lt (a, b) of
           HsBool_v true => HsBool_v true
         | HsBool_v false =>
             (case Eq.eq (a, b) of
                HsBool_v true => lt (HsList_v l, HsList_v l')
              | _ => HsBool_v false)
         | _ => HsBool_v false)
    | lt (INF, INF) = HsBool_v false
    | lt (INF, _) = HsBool_v false
    | lt (_, INF) = HsBool_v true
    | lt (_, _) = raise NotComparable
  fun le (a, b) =
    (BoolOp.or_hs (Eq.eq (a, b), lt (a, b)))
  fun gt (a, b) = lt (b, a)
  fun ge (a, b) = le (b, a)
  fun max (a, b) =
    (case gt (a, b) of
       HsBool_v true => a
     | _ => b)
  fun min (a, b) =
    (case lt (a, b) of
       HsBool_v true => a
     | _ => b)
  fun compare a b =
    case Eq.eq (a, b) of
      HsBool_v true => HsOrdering_v EQ
    | _ =>
        case lt (a, b) of
          HsBool_v true => HsOrdering_v LT
        | _ => HsOrdering_v GT
end

signature ENUM =
sig
  structure Op: NUM
  val succ: HaskellValue -> HaskellValue
  val pred: HaskellValue -> HaskellValue
end

structure Enum :> ENUM =
struct
  structure Op: NUM = Num
  fun succ (HsInt_v a) =
        Op.plus (HsInt_v a, HsInt_v 1)
    | succ (HsInteger_v a) =
        Op.plus (HsInteger_v a, HsInteger_v 1)
    | succ (HsFloat_v a) =
        Op.plus (HsFloat_v a, HsFloat_v 1.0)
    | succ (HsBool_v a) =
        BoolOp.not_hs (HsBool_v a)
    | succ (HsChar_v a) =
        let
          fun hs_chr (HsInt_v c) =
                HsChar_v (chr c)
            | hs_chr (HsInteger_v c) =
                HsChar_v (chr (LargeInt.toInt c))
            | hs_chr _ = raise NotEvaluable "Err"
        in
          hs_chr (Op.plus (HsInt_v (ord a), HsInt_v 1))
        end
    | succ (HsOrdering_v a) =
        (case a of
           LT => HsOrdering_v EQ
         | EQ => HsOrdering_v GT
         | _ => raise NotEvaluable "Err")
    | succ _ = raise NotEvaluable "Err"
  fun pred (HsInt_v a) =
        Op.minus (HsInt_v a, HsInt_v 1)
    | pred (HsInteger_v a) =
        Op.minus (HsInteger_v a, HsInteger_v 1)
    | pred (HsFloat_v a) =
        Op.minus (HsFloat_v a, HsFloat_v 1.0)
    | pred (HsChar_v a) =
        let
          fun hs_chr (HsInt_v c) =
                HsChar_v (chr c)
            | hs_chr (HsInteger_v c) =
                HsChar_v (chr (LargeInt.toInt c))
            | hs_chr _ = raise NotEvaluable "Err"
        in
          case Ord.gt (HsInt_v 0, (Op.minus (HsInt_v (ord a), HsInt_v 1))) of
            HsBool_v true => hs_chr (Op.minus (HsInt_v (ord a), HsInt_v 1))
          | _ => raise NotEvaluable "Err"
        end
    | pred (HsOrdering_v a) =
        (case a of
           GT => HsOrdering_v EQ
         | EQ => HsOrdering_v LT
         | _ => raise NotEvaluable "Err")
    | pred _ = raise NotEvaluable "Err"
end

(* Infinite Lists naturals [1..] or [2,4..24] ... *)
signature LAZYLIST =
sig
  exception OutOfBound
  datatype 'a lazylist = Empty | Cons of 'a * (unit -> 'a lazylist)
  val range: HaskellValue * HaskellValue * HaskellValue -> HaskellValue lazylist
  val get: HaskellValue lazylist * int -> HaskellValue
end

structure LazyList :> LAZYLIST =
struct
  exception OutOfBound
  datatype 'a lazylist = Empty | Cons of 'a * (unit -> 'a lazylist)
  fun range (s, e, step) =
    case Ord.lt (s, e) of
      HsBool_v true => Cons (s, fn () => range (Num.plus (s, step), e, step))
    | _ =>
        case Eq.eq (s, e) of
          HsBool_v true => Cons (e, fn () => Empty)
        | _ => raise OutOfBound
  fun get (Cons (a, _), 0) = a
    | get (Cons (_, l), index) =
        get (l (), index - 1)
    | get (Empty, _) = raise OutOfBound
end


fun eval (K a, _) = a
  | eval (Plus (a, b), env) =
      Num.plus (eval (a, env), eval (b, env))
  | eval (Minus (a, b), env) =
      Num.minus (eval (a, env), eval (b, env))
  | eval (Mul (a, b), env) =
      Num.mul (eval (a, env), eval (b, env))
  | eval (Equal (a, b), env) =
      Eq.eq (eval (a, env), eval (b, env))
  | eval (Lt (a, b), env) =
      Ord.lt (eval (a, env), eval (b, env))
  | eval (Le (a, b), env) =
      Ord.le (eval (a, env), eval (b, env))
  | eval (Gt (a, b), env) =
      Ord.gt (eval (a, env), eval (b, env))
  | eval (Ge (a, b), env) =
      Ord.ge (eval (a, env), eval (b, env))
  | eval (Var a, env) =
      eval (Env.solve_ref (Var a, env))
  | eval (Closure (_, body), env) = eval (body, env)
  | eval (Bind (Var a, (Call (Lambda (par, body), args))), env) =
      let
        fun count_params (Lambda (_, body')) = 1 + count_params body'
          | count_params _ = 0
      in
        if length args < count_params (Lambda (par, body)) then
          let
            val (env', body') = Env.bind_curried
              (par, args, env, Lambda (par, body), env)
          in
            eval (Bind (Var a, body'), env')
          end
        else if length args = count_params (Lambda (par, body)) then
          ( env_tmp
            := Env.binding (Var a, (Call (Lambda (par, body), args)), env, env)
          ; HsUnit_v ()
          )
        else
          raise NotEvaluable "Expression not evaluable"
      end
  | eval (Bind (Var a, Call (Function (Var fname, params, body), args)), env) =
      if length args < length params then
        let
          fun take (0, _: 'a list) = []
            | take (_, []) = []
            | take (n, a :: l : 'a list) =
                a :: take (n - 1, l)
          val diff = length params - length args
          val env' = Env.bind_list (params, args, env, env)
        in
          eval (Function (Var a, take (diff, rev params), body), env')
        end
      else if length params = length args then
        ( env_tmp
          :=
          Env.binding
            (Var a, (Call (Function (Var fname, params, body), args)), env, env)
        ; HsUnit_v ()
        )
      else
        raise NotEvaluable "Expression not evaluable"

  | eval (Bind (Var a, exp), env) =
      (env_tmp := Env.binding (Var a, exp, env, env); HsUnit_v ())
  | eval (Function (Var fname, par, body), env) =
      ( env_tmp := Env.binding (Var fname, Closure (par, body), env, env)
      ; HsUnit_v ()
      )
  | eval (Lambda (_, body), env) = eval (body, env)
  | eval (Call (Var fname, arg), env) =
      (case Env.solve_ref (Var fname, env) of
         (Closure (par, body), env') =>
           eval (body, Env.bind_list (par, arg, env, env'))
       | (Lambda (par, body), env') =>
           let val (env_curr, _) = Env.bind_curried (par, arg, env, body, env')
           in eval (body, env_curr)
           end
       | _ => raise NotEvaluable "Expression not evaluable")
  | eval (Call (Function (Var fname, par, body), args), env) =
      eval (body, Env.Cons_hs
        ( (Var fname, Closure (par, body), env)
        , Env.bind_list (par, args, env, env)
        ))
  | eval (Call (Lambda (par, body), arg), env) =
      let val (env', _) = Env.bind_curried (par, arg, env, body, env)
      in eval (body, env')
      end
  | eval (Guard (exp, cases), env) =
      let
        fun matchCases [] = raise NotEvaluable "No matching case"
          | matchCases ((case_i, exp_i) :: other_case) =
              (case Eq.eq (eval (exp, env), eval (case_i, env)) of
                 HsBool_v true => eval (exp_i, env)
               | _ => matchCases other_case)
      in
        matchCases cases
      end
  | eval (Let (Bind a, b), env) =
      ( eval (Bind a, env)
      ; let
          val evaluation = eval (b, !env_tmp)
          val _ = Env.clean (!env_tmp)
        in
          evaluation
        end
      )
  | eval (If (condition, caseT, caseF), env) =
      (case eval (condition, env) of
         HsBool_v true => eval (caseT, env)
       | HsBool_v false => eval (caseF, env)
       | _ => raise NotEvaluable "Not a Bool")
  | eval _ = raise NotEvaluable "Expression not evaluable"

(*Type inference function HaskellFun * Context.HsContext -> HaskellType 
TODO: rewrite everything using typeclasses*)
fun t (K (HsInt_v _), _) = HsInt_t
  | t (K (HsInteger_v _), _) = HsInteger_t
  | t (K (HsFloat_v _), _) = HsFloat_t
  | t (K (HsBool_v _), _) = HsBool_t
  | t (K (HsChar_v _), _) = HsChar_t
  | t (K (HsList_v (HsInt_v _ :: _)), _) = HsList_t HsInt_t
  | t (K (HsList_v (HsInteger_v _ :: _)), _) = HsList_t HsInteger_t
  | t (K (HsList_v (HsFloat_v _ :: _)), _) = HsList_t HsFloat_t
  | t (K (HsList_v (HsChar_v _ :: _)), _) = HsList_t HsChar_t
  | t (K (HsList_v (HsBool_v _ :: _)), _) = HsList_t HsBool_t
  | t (K (HsUnit_v _), _) = HsUnit_t
  | t (Var x, cntxt) =
      Context.cntxt_search (Var x, cntxt)
  | t (Plus (exp1, exp2), cntxt) =
      TypeOp.compare (t (exp1, cntxt), t (exp2, cntxt))
  | t (Mul (exp1, exp2), cntxt) =
      TypeOp.compare (t (exp1, cntxt), t (exp2, cntxt))
  | t (Minus (exp1, exp2), cntxt) =
      TypeOp.compare (t (exp1, cntxt), t (exp2, cntxt))
  | t (Equal (exp1, exp2), cntxt) =
      (TypeOp.compare (t (exp1, cntxt), t (exp2, cntxt)); HsBool_t)
  | t (Lt (exp1, exp2), cntxt) =
      (TypeOp.compare (t (exp1, cntxt), t (exp2, cntxt)); HsBool_t)
  | t _ = raise TypeError

val _ = eval
  ( Function (Var "Factorial", [Var "n"], Guard
      ( Var "n"
      , [ (K (HsInteger_v 0), K (HsInteger_v 1))
        , ( Var "n"
          , Mul (Var "n", Call
              (Var "Factorial", [Minus (Var "n", K (HsInteger_v 1))]))
          )
        ]
      ))
  , Env.Empty_hs
  )

fun res_1 () =
  case eval (Call (Var "Factorial", [K (HsInteger_v 20)]), !env_tmp) of
    HsInteger_v v => print ("Result of function: " ^ LargeInt.toString v ^ "\n")
  | _ => print "Errore"


val _ = eval
  ( Function (Var "Do2Times", [Var "fn", Var "x"], Call
      (Var "fn", [Call (Var "fn", [Var "x"])]))
  , Env.Empty_hs
  )
val res_2 = eval
  ( Call
      ( Var "Do2Times"
      , [Lambda (Var "y", Mul (Var "y", K (HsInt_v 3))), K (HsInt_v 10)]
      )
  , !env_tmp
  )

val continuation_fn1 = eval
  ( Call
      ( Lambda (Var "x", Lambda (Var "y", Plus (Var "x", Var "y")))
      , [K (HsInt_v 10), K (HsInt_v 12)]
      )
  , Env.Empty_hs
  )


val continuation_fn2 = eval
  ( Bind (Var "add4", Call
      ( Lambda (Var "x", Lambda (Var "y", Plus (Var "x", Var "y")))
      , [K (HsInt_v 4)]
      )),
   Env.Empty_hs
  )

val letexpLazy = eval
  (Let (Bind (Var "x", Var "y"), K (HsInt_v 10)), Env.Empty_hs)
