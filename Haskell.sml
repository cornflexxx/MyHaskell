exception NotEvaluable of string
exception NotTypeable
exception NotComparable
exception InvalidOperandType of string


(* Types *)
datatype HaskellType =
  HsInt_t
| HsInteger_t
| HsFloat_t
| HsChar_t
| HsBool_t
| HsList_t of HaskellType
| HsTuple_t of HaskellType list
| HsUnit_t
| HsArrow_t of HaskellType * HaskellType
| HsAbstract_t

(* Working types *)
datatype HaskellValue =
  HsInt_v of int
| HsInteger_v of LargeInt.int
| HsFloat_v of real
| HsChar_v of char
| HsBool_v of bool
| HsList_v of HaskellValue list 
| HsTuple_v of HaskellValue list
| HsUnit_v of unit
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
| Lambda of HaskellFun list * HaskellFun
| Closure of HaskellFun list * HaskellFun

(* Enviroment *)
signature ENV =
sig
  exception RefNotFound
  datatype HsEnv =
    Empty_hs
  | Cons_hs of (HaskellFun * HaskellFun * HsEnv) * HsEnv
  val binding: HaskellFun * HaskellFun * HsEnv -> HsEnv
  val solve_ref: HaskellFun * HsEnv -> HaskellFun * HsEnv
  val clean: HsEnv -> HsEnv
  val bind_list: HaskellFun list * HaskellFun list * HsEnv -> HsEnv
end

structure Env :> ENV =
struct

  exception RefNotFound
  exception CantBind

  datatype HsEnv =
    Empty_hs
  | Cons_hs of (HaskellFun * HaskellFun * HsEnv) * HsEnv
  fun binding (Var x, exp, env) =
        Cons_hs ((Var x, exp, env), env)
    | binding (_, _, _) = raise CantBind
  fun solve_ref (Var x, Cons_hs ((Var y, exp, env'), env)) =
        (if x = y then (exp, env') else solve_ref (Var x, env))
    | solve_ref (_, _) = raise RefNotFound
  fun clean (Cons_hs ((_, _, _), env)) = env
    | clean _ = raise RefNotFound
  fun bind_list (_, [], env) = env
    | bind_list (Var p :: params, expr :: exprs, env) =
        Cons_hs ((Var p, expr, env), bind_list (params, exprs, env))
    | bind_list _ = raise CantBind

end


(* Context for type inference *)
signature CONTEXT =
sig
  datatype HsContext = Empty_hs | Cons_hs of HaskellFun * HaskellType
end

structure Context :> CONTEXT =
struct datatype HsContext = Empty_hs | Cons_hs of HaskellFun * HaskellType end

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
end

(* Expression evaluation fun *)
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
  | eval (Bind (Var a, exp), env) =
      (env_tmp := Env.binding (Var a, exp, env); HsUnit_v ()) 
  | eval (Function (Var fname, par, body), env) =
      ( env_tmp := Env.binding (Var fname, Closure (par, body), env)
      ; HsUnit_v ()
      )
  | eval (Call (Var fname, arg), env) =
      (case Env.solve_ref (Var fname, env) of
         (Closure (par, body), _) => eval (body, Env.bind_list (par, arg, env))
       | _ => raise NotEvaluable "Expression not evaluable")
  | eval (Call (Function (Var fname, par, body), args), env) =
      eval (body, Env.Cons_hs
        ((Var fname, Closure (par, body), env), Env.bind_list (par, args, env)))
  | eval (Call (Lambda (par, body), arg), env) =
      eval (body, Env.bind_list (par, arg, env))
  (* Do a better implementation of Lambda functions and passing parameters (Curry) *)
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
          val evaluation = eval (b, env)
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

(*Type inference function HaskellFun * Context.HsContext -> HaskellType wp*)
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
  (* t(Function ...*)
  | t _ = raise NotTypeable

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

fun res () =
  case eval (Call (Var "Factorial", [K (HsInteger_v 20)]), !env_tmp) of
    HsInteger_v v => print ("Result of function: " ^ LargeInt.toString v ^ "\n")
  | _ => print "Errore"
