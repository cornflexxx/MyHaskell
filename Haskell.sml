exception NotEvaluable of string
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

(* Enviroment *)
signature ENV =
sig
  exception RefNotFound
  datatype HsEnv = Empty_hs | Cons_hs of (HaskellFun * HaskellFun) * HsEnv
  val binding: HaskellFun * HaskellFun * HsEnv -> HsEnv
  val solve_ref: HaskellFun * HsEnv -> HaskellFun
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
end

val env_tmp = ref Env.Empty_hs

signature EQ =
sig
  exception NotComparable
  val eq: HaskellValue * HaskellValue -> HaskellValue
end

structure Eq :> EQ =
struct
  exception NotComparable
  fun andalso_hs (HsBool_v a, HsBool_v b) =
        HsBool_v (a andalso b)
    | andalso_hs (_, _) = HsBool_v false
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
        andalso_hs (eq (a, b), eq (HsList_v l, HsList_v l'))
    | eq (HsBool_v a, HsBool_v b) =
        HsBool_v (a = b)
    | eq (HsUnit_v a, HsUnit_v b) =
        HsBool_v (a = b)
    | eq (HsTuple_v (a :: l), HsTuple_v (b :: l')) =
        andalso_hs (eq (a, b), eq (HsTuple_v l, HsTuple_v l'))
    | eq (_, _) = raise NotComparable
end
(* Some numerical operation *)
signature NUM =
sig
  exception InvalidOperandType of string
  val plus: HaskellValue * HaskellValue -> HaskellValue
  val mul: HaskellValue * HaskellValue -> HaskellValue
  val minus: HaskellValue * HaskellValue -> HaskellValue
(*val sign: num * num -> num
val abs: num * num -> num
val negate: num * num -> num*)
end

structure Num :> NUM =
struct
  exception InvalidOperandType of string

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
         Fn (Var par, body) => (eval (Bind (Var par, arg)); eval body)
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
