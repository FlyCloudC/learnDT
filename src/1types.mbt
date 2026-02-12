///|
/// Term ↑
pub enum ExpI {
  Ann(ExpC, ExpC)
  Star
  Pi(ExpC, ExpC)
  /// 从里往外的第 i 个变量
  Bound(Int)
  Free(Name)
  App(ExpI, ExpC)
  Nat
  Zero
  Succ(ExpC)
  NatElim(ExpC, ExpC, ExpC, ExpC)
  Vec(ExpC, ExpC)
  Nil(ExpC)
  Cons(ExpC, ExpC, ExpC, ExpC)
  VecElim(ExpC, ExpC, ExpC, ExpC, ExpC, ExpC)
} derive(Show, Eq)

///|
/// Term ↓
pub enum ExpC {
  Inf(ExpI)
  Lam(ExpC)
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
  VLam((Value) -> Value)
  VStar
  VPi(Value, (Value) -> Value)
  VNeutral(Neutral)
  VNat
  VZero
  VSucc(Value)
  VVec(Value, Value)
  VNil(Value)
  VCons(Value, Value, Value, Value)
}

///|
pub enum Neutral {
  NFree(Name)
  NApp(Neutral, Value)
  NNatElim(Value, Value, Value, Neutral)
  NVecElim(Value, Value, Value, Value, Value, Neutral)
} derive(Show)

///|
using @list {type List}

///|
type Env = List[Value]
