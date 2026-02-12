///|
/// Term ↑
pub enum ExpI {
  Ann(e~ : ExpC, e_ty~ : ExpC)
  Star
  Pi(e_par_ty~ : ExpC, e_ret_ty~ : ExpC)
  /// 从里往外的第 i 个变量
  Bound(i~ : Int)
  Free(name~ : Name)
  App(e_fun~ : ExpI, e_arg~ : ExpC)
  Nat
  Zero
  Succ(e_l~ : ExpC)
  NatElim(e_m~ : ExpC, e_onz~ : ExpC, e_ons~ : ExpC, e_k~ : ExpC)
  Vec(e_ty~ : ExpC, e_len~ : ExpC)
  Nil(e_ty~ : ExpC)
  Cons(e_ty~ : ExpC, e_len~ : ExpC, e_x~ : ExpC, e_xs~ : ExpC)
  VecElim(
    e_ty~ : ExpC,
    e_m~ : ExpC,
    e_onn~ : ExpC,
    e_onc~ : ExpC,
    e_len~ : ExpC,
    e_xs~ : ExpC
  )
} derive(Show, Eq)

///|
/// Term ↓
pub enum ExpC {
  Inf(e~ : ExpI)
  Lam(e_ret~ : ExpC)
} derive(Show, Eq)

///|
pub enum Name {
  Global(String)
  /// check_type 和 infer_type 函数内部使用的临时名字
  Local(Int)
  /// quote 函数内部使用的临时名字
  Quote(Int)
} derive(Eq, Show)

///|
type Type = Value

///|
pub enum Value {
  VLam(f~ : (Value) -> Value)
  VStar
  VPi(ty_par~ : Value, ty_ret~ : (Value) -> Value)
  VNeutral(n~ : Neutral)
  VNat
  VZero
  VSucc(l~ : Value)
  VVec(ty~ : Value, len~ : Value)
  VNil(ty~ : Value)
  VCons(ty~ : Value, len~ : Value, x~ : Value, xs~ : Value)
}

///|
pub enum Neutral {
  NFree(name~ : Name)
  NApp(n_fun~ : Neutral, arg~ : Value)
  NNatElim(m~ : Value, onz~ : Value, ons~ : Value, n_k~ : Neutral)
  NVecElim(
    ty~ : Value,
    m~ : Value,
    onn~ : Value,
    onc~ : Value,
    len~ : Value,
    n_xs~ : Neutral
  )
} derive(Show)

///|
using @list {type List}

///|
type Env = List[Value]
