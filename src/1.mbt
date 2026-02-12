///|
fn Value::free(name : Name) -> Value {
  VNeutral(n=NFree(name~))
}

///|
pub fn ExpI::eval(self : ExpI, env : Env) -> Value {
  match self {
    Star => VStar
    Pi(e_par_ty~, e_ret_ty~) =>
      VPi( //
        ty_par=e_par_ty.eval(env),
        ty_ret=arg => e_ret_ty.eval(env.add(arg)),
      )
    Ann(e~, ..) => e.eval(env)
    Free(name~) => Value::free(name)
    Bound(i~) => env.unsafe_nth(i)
    App(e_fun~, e_arg~) =>
      Value::app( //
        e_fun.eval(env),
        e_arg.eval(env),
      )
    Nat => VNat
    Zero => VZero
    Succ(e_l~) => VSucc(l=e_l.eval(env))
    NatElim(e_m~, e_onz~, e_ons~, e_k~) => {
      let onz = e_onz.eval(env)
      let ons = e_ons.eval(env)
      fn rec(k) {
        match k {
          VZero => onz
          VSucc(l~) => ons.app(l).app(rec(l))
          VNeutral(n~) =>
            VNeutral(n=NNatElim(m=e_m.eval(env), onz~, ons~, n_k=n))
          _ => panic()
        }
      }

      rec(e_k.eval(env))
    }
    Vec(e_ty~, e_len~) => VVec(ty=e_ty.eval(env), len=e_len.eval(env))
    Nil(e_ty~) => VNil(ty=e_ty.eval(env))
    Cons(e_ty~, e_len~, e_x~, e_xs~) =>
      VCons( //
        ty=e_ty.eval(env),
        len=e_len.eval(env),
        x=e_x.eval(env),
        xs=e_xs.eval(env),
      )
    VecElim(e_ty~, e_m~, e_onn~, e_onc~, e_len~, e_xs~) => {
      let onn = e_onn.eval(env)
      let onc = e_onc.eval(env)
      fn rec(len, xs) {
        match xs {
          VNil(_) => onn
          VCons(ty=_, len=len_, x~, xs=xs_) =>
            onc.app(len_).app(x).app(xs_).app(rec(len_, xs_))
          VNeutral(n=n_xs) =>
            VNeutral(
              n=NVecElim(
                ty=e_ty.eval(env),
                m=e_m.eval(env),
                onn~,
                onc~,
                len~,
                n_xs~,
              ),
            )
          _ => panic()
        }
      }

      rec(e_len.eval(env), e_xs.eval(env))
    }
  }
}

///|
fn Value::app(self : Value, arg : Value) -> Value {
  match self {
    VLam(f~) => f(arg)
    VNeutral(n~) => VNeutral(n=NApp(n_fun=n, arg~))
    _ => panic() // TODO: P18 缺少分支
  }
}

///|
pub fn ExpC::eval(self : ExpC, env : Env) -> Value {
  match self {
    Inf(e~) => e.eval(env)
    Lam(e_ret~) => VLam(f=x => e_ret.eval(env.add(x)))
  }
}
