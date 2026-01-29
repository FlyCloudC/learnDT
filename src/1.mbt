///|
fn Value::free(name : Name) -> Value {
  VNeutral(NFree(name))
}

///|
pub fn ExpI::eval(self : ExpI, env : Env) -> Value {
  match self {
    Star => VStar
    Pi(e_par_ty, e_ret_ty) =>
      VPi( //
        e_par_ty.eval(env),
        arg => e_ret_ty.eval(env.add(arg)),
      )
    Ann(e, _) => e.eval(env)
    Free(name) => Value::free(name)
    Bound(i) => env.unsafe_nth(i)
    App(e_fun, e_arg) =>
      Value::app( //
        e_fun.eval(env),
        e_arg.eval(env),
      )
    Nat => VNat
    Zero => VZero
    Succ(k) => VSucc(k.eval(env))
    NatElim(e_m, e_onz, e_ons, e_k) => {
      let onz = e_onz.eval(env)
      let ons = e_ons.eval(env)
      fn rec(k) {
        match k {
          VZero => onz
          VSucc(l) => ons.app(l).app(rec(l))
          VNeutral(n_k) => VNeutral(NNatElim(e_m.eval(env), onz, ons, n_k))
          _ => panic()
        }
      }

      rec(e_k.eval(env))
    }
  }
}

///|
fn Value::app(self : Value, v : Value) -> Value {
  match self {
    VLam(f) => f(v)
    VNeutral(n) => VNeutral(NApp(n, v))
    _ => panic() // TODO: P18 缺少分支
  }
}

///|
pub fn ExpC::eval(self : ExpC, env : Env) -> Value {
  match self {
    Inf(e) => e.eval(env)
    Lam(e_ret) => VLam(x => e_ret.eval(env.add(x)))
  }
}
