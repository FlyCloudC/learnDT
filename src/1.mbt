///|
fn Value::free(name : Name) -> Value {
  VNeutral(NFree(name))
}

///|
pub fn ExpI::eval(self : ExpI, env : Env) -> Value {
  match self {
    Ann(e, _) => e.eval(env)
    Free(name) => Value::free(name)
    Bound(i) => env.unsafe_nth(i)
    App(e_fun, e_arg) =>
      Value::app( //
        e_fun.eval(env),
        e_arg.eval(env),
      )
  }
}

///|
fn Value::app(self : Value, v : Value) -> Value {
  match self {
    VLam(f) => f(v)
    VNeutral(n) => VNeutral(NApp(n, v))
  }
}

///|
pub fn ExpC::eval(self : ExpC, env : Env) -> Value {
  match self {
    Inf(e) => e.eval(env)
    Lam(e_ret) => VLam(x => e_ret.eval(env.add(x)))
  }
}
