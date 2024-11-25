exception NotEvaluable of string
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
(* MyHaskell expressions *)
and HaskellFun =
  K of HaskellValue
| Var of string
| Plus of HaskellFun * HaskellFun
| Minus of HaskellFun * HaskellFun
| Mul of HaskellFun * HaskellFun
| Bind of HaskellFun * HaskellFun
| Seq of HaskellFun * HaskellFun
| Fn of HaskellFun * HaskellFun
| Guard of HaskellFun * ((HaskellFun * HaskellFun) list)
| Call of (HaskellFun * HaskellFun)
| Rec of HaskellFun

(* Enviroment *)
signature ENV =
sig
  exception RefNotFound
  datatype HsEnv = Empty_hs | Cons_hs of (HaskellFun * HaskellFun) * HsEnv
  val binding: HaskellFun * HaskellFun * HsEnv -> HsEnv
  val solve_ref: HaskellFun * HsEnv -> HaskellFun
  val clean: HsEnv -> HsEnv
end

structure Env :> ENV =
struct

  exception RefNotFound
  exception CantBind

  datatype HsEnv = Empty_hs | Cons_hs of (HaskellFun * HaskellFun) * HsEnv
  fun binding (Var x, exp, env) =
        Cons_hs ((Var x, exp), env)
    | binding (_, _, _) = raise CantBind
  fun solve_ref (Var x, Cons_hs ((Var y, exp), env)) =
        (if x = y then exp else solve_ref (Var x, env))
    | solve_ref (_, _) = raise RefNotFound
  fun clean (Cons_hs ((_, _), env)) = env
    | clean _ = raise RefNotFound
end

val env_tmp = ref Env.Empty_hs

signature EQ =
sig
  val eq: HaskellValue * HaskellValue -> HaskellValue
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

signature ORD =
sig
  val lt: HaskellValue * HaskellValue -> HaskellValue
  val le: HaskellValue * HaskellValue -> HaskellValue
  val gt: HaskellValue * HaskellValue -> HaskellValue
  val ge: HaskellValue * HaskellValue -> HaskellValue
  val min: HaskellValue * HaskellValue -> HaskellValue
  val max: HaskellValue * HaskellValue -> HaskellValue
end

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
fun eval (K a) = a
  | eval (Plus (a, b)) =
      Num.plus (eval a, eval b)
  | eval (Minus (a, b)) =
      Num.minus (eval a, eval b)
  | eval (Mul (a: HaskellFun, b: HaskellFun)) =
      Num.mul (eval a, eval b)
  | eval (Var x) =
      eval (Env.solve_ref (Var x, !env_tmp))
  | eval (Bind (Var x, exp)) =
      (env_tmp := Env.binding (Var x, exp, !env_tmp); HsUnit_v ())
  | eval (Seq (exp_1, exp_2)) =
      (eval exp_1; eval exp_2)
  | eval (Call (Var fname, arg)) =
      (case Env.solve_ref (Var fname, !env_tmp) of
         Rec (Fn (Var par, body)) =>
           ( eval (Bind (Var par, K (eval arg)))
           ; let
               val evalued = eval body
               val _ = (env_tmp := Env.clean (!env_tmp))
             in
               evalued
             end
           )
       | Fn (Var par, body) =>
           ( eval (Bind (Var par, arg))
           ; let
               val evalued = eval body
               val _ = (env_tmp := Env.clean (!env_tmp))
             in
               evalued
             end
           )
       | _ => raise NotEvaluable "Call to non-function")
  | eval (Guard (exp, cases)) =
      let
        fun matchCases [] = raise NotEvaluable "No matching case"
          | matchCases ((case_i, exp_i) :: other_case) =
              (case Eq.eq (eval exp, eval case_i) of
                 HsBool_v true => eval exp_i
               | _ => matchCases other_case)
      in
        matchCases cases
      end
  | eval _ = raise NotEvaluable "Expression not evaluable"


val _ = eval (Bind (Var "Fact", Rec (Fn (Var "n", Guard
  ( Var "n"
  , [ (K (HsInt_v 0), K (HsInt_v 1))
    , ( Var "n"
      , Mul (Var "n", Call (Var "Fact", Minus (Var "n", K (HsInt_v 1))))
      )
    ]
  )))))
val _ = eval (Call (Var "Fact", K (HsInt_v 7)))
