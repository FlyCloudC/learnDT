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
}

///|
pub enum Neutral {
  NFree(Name)
  NApp(Neutral, Value)
} derive(Show)

///|
using @list {type List}

///|
type Env = List[Value]
