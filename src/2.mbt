///|
/// i == 当前上下文套的 Lam 的层数
fn ExpI::infer_type(
  self : ExpI,
  i : Int,
  ctx : Context,
) -> Type raise CheckError {
  match self {
    Ann(e~, e_ty~) => {
      e_ty.check_type(i, ctx, VStar)
      let ty = e_ty.eval(Env::empty())
      e.check_type(i, ctx, ty)
      ty
    }
    Star => VStar
    Pi(e_par_ty~, e_ret_ty~) => {
      e_par_ty.check_type(i, ctx, VStar)
      let par_ty = e_par_ty.eval(Env::empty())
      e_ret_ty
      .subst(0, Free(name=Local(i)))
      .check_type(i + 1, ctx.add((Local(i), par_ty)), VStar)
      VStar
    }
    Free(name~) => {
      guard ctx.lookup(name) is Some(ty) else { raise UnknownIdent(name) }
      ty
    }
    App(e_fun~, e_arg~) => {
      let fun_ty = e_fun.infer_type(i, ctx)
      guard fun_ty is VPi(ty_par~, ty_ret~) else { raise IllApply }
      e_arg.check_type(i, ctx, ty_par)
      ty_ret(e_arg.eval(Env::empty()))
    }
    Bound(_) => panic()
    // Because we are turning a bound variable into a free variable,
    // the type checker will never encounter a bound variable.
    Nat => VStar
    Zero => VNat
    Succ(e_l~) => {
      e_l.check_type(i, ctx, VNat)
      VNat
    }
    NatElim(e_m~, e_onz~, e_ons~, e_k~) => {
      e_m.check_type(i, ctx, VPi(ty_par=VNat, ty_ret=_ => VStar))
      let m = e_m.eval(Env::empty())
      e_onz.check_type(i, ctx, m.app(VZero))
      e_ons.check_type(
        i,
        ctx,
        VPi(ty_par=VNat, ty_ret=l => {
          VPi(ty_par=m.app(l), ty_ret=_ => m.app(VSucc(l~)))
        }),
      )
      e_k.check_type(i, ctx, VNat)
      let k = e_k.eval(Env::empty())
      m.app(k)
    }
    Vec(e_ty~, e_len~) => {
      e_ty.check_type(i, ctx, VStar)
      e_len.check_type(i, ctx, VNat)
      VStar
    }
    Nil(e_ty~) => {
      e_ty.check_type(i, ctx, VStar)
      VVec(ty=e_ty.eval(Env::empty()), len=VZero)
    }
    Cons(e_ty~, e_len~, e_x~, e_xs~) => {
      e_ty.check_type(i, ctx, VStar)
      let ty = e_ty.eval(Env::empty())
      e_len.check_type(i, ctx, VNat)
      let len = e_len.eval(Env::empty())
      e_x.check_type(i, ctx, ty)
      e_xs.check_type(i, ctx, VVec(ty~, len~))
      VVec(ty~, len=VSucc(l=len))
    }
    VecElim(e_ty~, e_m~, e_onn~, e_onc~, e_len~, e_xs~) => {
      e_ty.check_type(i, ctx, VStar)
      let ty = e_ty.eval(Env::empty())
      e_m.check_type(
        i,
        ctx,
        VPi(ty_par=VNat, ty_ret=len => {
          VPi(ty_par=VVec(ty~, len~), ty_ret=_ => VStar)
        }),
      )
      let m = e_m.eval(Env::empty())
      e_onn.check_type(i, ctx, m.app(VZero).app(VNil(ty~)))
      e_onc.check_type(
        i,
        ctx,
        VPi(ty_par=VNat, ty_ret=len => {
          VPi(ty_par=ty, ty_ret=x => {
            VPi(ty_par=VVec(ty~, len~), ty_ret=xs => {
              VPi(ty_par=m.app(len).app(xs), ty_ret=_ => {
                m.app(VSucc(l=len)).app(VCons(ty~, len~, x~, xs~))
              })
            })
          })
        }),
      )
      e_len.check_type(i, ctx, VNat)
      let len = e_len.eval(Env::empty())
      e_xs.check_type(i, ctx, VVec(ty~, len~))
      let xs = e_xs.eval(Env::empty())
      m.app(len).app(xs)
    }
  }
}

///|
pub fn ExpI::infer_type0(self : ExpI, ctx : Context) -> Type raise CheckError {
  self.infer_type(0, ctx)
}

///|
fn ExpC::check_type(
  self : ExpC,
  i : Int,
  ctx : Context,
  ty : Type,
) -> Unit raise CheckError {
  match self {
    Inf(e~) => {
      let ty_infer = e.infer_type(i, ctx)
      guard ty.quote() == ty_infer.quote() else { raise MisMatch(self) }
    }
    Lam(e_ret~) => {
      guard ty is VPi(ty_par~, ty_ret~) else { raise MisMatch(self) }
      let new_ctx = ctx.add((Local(i), ty_par))
      e_ret //
      .subst(0, Free(name=Local(i)))
      .check_type(i + 1, new_ctx, ty_ret(Value::free(Local(i))))
    }
  }
}

///|
pub fn ExpC::check_type0(
  self : ExpC,
  ctx : Context,
  ty : Type,
) -> Unit raise CheckError {
  self.check_type(0, ctx, ty)
}

// --------------------------------------------------------------------

///|
/// 把 e_old 出现的 Bound(i) 所代表的变量换成 e_new
/// 这里的 i 和 check_type 的 i 不一样，subst 的时候是从 i=0 开始的
fn ExpI::subst(e_old : ExpI, i : Int, e_new : ExpI) -> ExpI {
  match e_old {
    Ann(e~, e_ty~) => Ann(e=e.subst(i, e_new), e_ty=e_ty.subst(i, e_new))
    Star => e_old
    Pi(e_par_ty~, e_ret_ty~) =>
      Pi( //
        e_par_ty=e_par_ty.subst(i, e_new),
        e_ret_ty=e_ret_ty.subst(i + 1, e_new),
      )
    Bound(i=j) => if i == j { e_new } else { e_old }
    Free(_) => e_old
    App(e_fun~, e_arg~) =>
      App( //
        e_fun=e_fun.subst(i, e_new),
        e_arg=e_arg.subst(i, e_new),
      )
    Nat => e_old
    Zero => e_old
    Succ(e_l~) => Succ(e_l=e_l.subst(i, e_new))
    NatElim(e_m~, e_onz~, e_ons~, e_k~) =>
      NatElim(
        e_m=e_m.subst(i, e_new),
        e_onz=e_onz.subst(i, e_new),
        e_ons=e_ons.subst(i, e_new),
        e_k=e_k.subst(i, e_new),
      )
    Vec(e_ty~, e_len~) =>
      Vec(e_ty=e_ty.subst(i, e_new), e_len=e_len.subst(i, e_new))
    Nil(e_ty~) => Nil(e_ty=e_ty.subst(i, e_new))
    Cons(e_ty~, e_len~, e_x~, e_xs~) =>
      Cons(
        e_ty=e_ty.subst(i, e_new),
        e_len=e_len.subst(i, e_new),
        e_x=e_x.subst(i, e_new),
        e_xs=e_xs.subst(i, e_new),
      )
    VecElim(e_ty~, e_m~, e_onn~, e_onc~, e_len~, e_xs~) =>
      VecElim(
        e_ty=e_ty.subst(i, e_new),
        e_m=e_m.subst(i, e_new),
        e_onn=e_onn.subst(i, e_new),
        e_onc=e_onc.subst(i, e_new),
        e_len=e_len.subst(i, e_new),
        e_xs=e_xs.subst(i, e_new),
      )
  }
}

///|
fn ExpC::subst(e_old : ExpC, i : Int, e_new : ExpI) -> ExpC {
  match e_old {
    Inf(e~) => Inf(e=e.subst(i, e_new))
    Lam(e_ret=e) => Lam(e_ret=e.subst(i + 1, e_new))
  }
}

// --------------------------------------------------------------------

///|
/// 把 Value 反向转回 Term
fn Value::quote(self : Value, i? : Int = 0) -> ExpC {
  match self {
    VLam(f~) => Lam(e_ret=f.quote(i~))
    VStar => Inf(e=Star)
    VPi(ty_par~, ty_ret~) =>
      Inf(e=Pi(e_par_ty=ty_par.quote(i~), e_ret_ty=ty_ret.quote(i~)))
    VNeutral(n~) => Inf(e=n.quote(i~))
    VNat => Inf(e=Nat)
    VZero => Inf(e=Zero)
    VSucc(l~) => Inf(e=Succ(e_l=l.quote(i~)))
    VVec(ty~, len~) => Inf(e=Vec(e_ty=ty.quote(i~), e_len=len.quote(i~)))
    VNil(ty~) => Inf(e=Nil(e_ty=ty.quote(i~)))
    VCons(ty~, len~, x~, xs~) =>
      Inf(
        e=Cons(
          e_ty=ty.quote(i~),
          e_len=len.quote(i~),
          e_x=x.quote(i~),
          e_xs=xs.quote(i~),
        ),
      )
  }
}

///|
fn VFunc::quote(self : VFunc, i~ : Int) -> ExpC {
  self(Value::free(Quote(i))).quote(i=i + 1)
}

///|
fn Neutral::quote(self : Neutral, i~ : Int) -> ExpI {
  match self {
    // Bound 从里往外数
    // Quote 从外往里数
    NFree(name=Quote(k)) => Bound(i=i - k - 1)
    NFree(name~) => Free(name~)
    NApp(n_fun~, arg~) => App(e_fun=n_fun.quote(i~), e_arg=arg.quote(i~))
    NNatElim(m~, onz~, ons~, n_k~) =>
      NatElim(
        e_m=m.quote(i~),
        e_onz=onz.quote(i~),
        e_ons=ons.quote(i~),
        e_k=Inf(e=n_k.quote(i~)),
      )
    NVecElim(ty~, m~, onn~, onc~, len~, n_xs~) =>
      VecElim(
        e_ty=ty.quote(i~),
        e_m=m.quote(i~),
        e_onn=onn.quote(i~),
        e_onc=onc.quote(i~),
        e_len=len.quote(i~),
        e_xs=Inf(e=n_xs.quote(i~)),
      )
  }
}

// --------------------------------------------------------------------

///|
pub impl Debug for VFunc with to_repr(self) {
  self(Value::free(Global("_"))).to_repr()
}

///|
test "example p12" {
  let e_id = Lam(e_ret=Inf(e=Bound(i=0)))
  let e_cst = Lam(e_ret=Lam(e_ret=Inf(e=Bound(i=1))))
  let e_free = name => Inf(e=Free(name=Global(name)))
  // -------------------------------------
  let e_ty_a = e_free("a")
  let e_ty_b = e_free("b")
  let app = (e_fun, e_arg) => App(e_fun~, e_arg~)
  // -------------------------------------
  let fun = (e_par_ty, e_ret_ty) => Inf(e=Pi(e_par_ty~, e_ret_ty~))
  let e_1 = app(Ann(e=e_id, e_ty=fun(e_ty_a, e_ty_a)), e_free("y"))
  let e_2 = Ann(
      e=e_cst,
      e_ty=fun( //
        fun(e_ty_b, e_ty_b),
        fun(e_ty_a, fun(e_ty_b, e_ty_b)),
      ),
    )
    |> app(e_id)
    |> app(e_free("y"))
  // -------------------------------------
  let empty_env : Env = Env::empty()
  let env_1 = Env::from_array([
    (Global("y"), e_ty_a.eval(Env::empty())),
    (Global("a"), VStar),
  ])
  let env_2 = env_1.add( //
    (Global("b"), VStar),
  )
  // -------------------------------------
  debug_inspect(
    e_1.eval(empty_env).quote(),
    content=(
      #|Inf(e=Free(name=Global("y")))
    ),
  )
  debug_inspect(
    e_2.eval(empty_env).quote(),
    content=(
      #|Lam(e_ret=Inf(e=Bound(i=0)))
    ),
  )
  debug_inspect(
    e_1.infer_type(0, env_1),
    content=(
      #|VNeutral(n=NFree(name=Global("a")))
    ),
  )
  debug_inspect(
    e_2.infer_type(0, env_2),
    content=(
      #|VPi(
      #|  ty_par=VNeutral(n=NFree(name=Global("b"))),
      #|  ty_ret=VNeutral(n=NFree(name=Global("b"))),
      #|)
    ),
  )
}

///|
test "example p24:plus" {
  let pi = (e_par_ty, e_ret_ty) => Inf(e=Pi(e_par_ty~, e_ret_ty~))
  let nat = Inf(e=Nat)
  let app = (x, y) => App(e_fun=x, e_arg=Inf(e=y))
  // -------------------------------------
  let e_m = Lam(e_ret=pi(nat, nat)) // _ => (Nat -> Nat)
  let e_onz = Lam(e_ret=Inf(e=Bound(i=0))) // n => n
  let e_ons = Lam( // k =>
    e_ret=Lam( // rec =>
      e_ret=Lam( // n =>
        e_ret=Inf( // Succ(rec(n))
          e=app(Bound(i=1), Bound(i=0)),
        ),
      ),
    ),
  )
  let e_plus = Ann(
    e=Lam(e_ret=Inf(e=NatElim(e_m~, e_onz~, e_ons~, e_k=Inf(e=Bound(i=0))))),
    e_ty=pi(nat, pi(nat, nat)),
  )
  // -------------------------------------
  let ty_plus = e_plus.infer_type(0, Context::empty())
  debug_inspect(
    ty_plus,
    content=(
      #|VPi(ty_par=VNat, ty_ret=VPi(ty_par=VNat, ty_ret=VNat))
    ),
  )
  // -------------------------------------
  let int_to_e_nat = x => {
    loop (x, Zero) {
      (0, e) => e
      (x, e) => continue (x - 1, Succ(e_l=Inf(e~)))
    }
  }
  let nat_to_int = v => {
    loop (v, 0) {
      (VZero, x) => x.to_string()
      (VSucc(l~), x) => continue (l, x + 1)
      _ => panic()
    }
  }
  let n_40 = int_to_e_nat(40)
  let n_2 = int_to_e_nat(2)
  let app = (x, y) => App(e_fun=x, e_arg=Inf(e=y))
  let e_plus_40_2 = e_plus |> app(n_40) |> app(n_2)
  debug_inspect(
    e_plus_40_2.eval(Env::empty()) |> nat_to_int,
    content=(
      #|"2"
    ),
  )
}

///|
test "example p28:append" {
  let pi = (x, y) => Inf(e=Pi(e_par_ty=x, e_ret_ty=y))
  let nat = Inf(e=Nat)
  let e_free = name => Inf(e=Free(name=Global(name)))
  let vec = (ty, len) => Inf(e=Vec(e_ty=ty, e_len=len))
  // appI: second arg is ExpI (we wrap it with Inf), appC: second arg is already ExpC
  let appI = (x, y) => App(e_fun=x, e_arg=Inf(e=y))
  let appC = (x, y) => App(e_fun=x, e_arg=y)

  // reuse plus (from p24) for types
  let e_m = Lam(e_ret=pi(nat, nat)) // _ => (Nat -> Nat)
  let e_onz = Lam(e_ret=Inf(e=Bound(i=0))) // n => n
  let e_ons = Lam(
    e_ret=Lam(
      e_ret=Lam(e_ret=Inf(e=Succ(e_l=Inf(e=appI(Bound(i=1), Bound(i=0)))))),
    ),
  )
  let e_plus = Ann(
    e=Lam(e_ret=Inf(e=NatElim(e_m~, e_onz~, e_ons~, e_k=Inf(e=Bound(i=0))))),
    e_ty=pi(nat, pi(nat, nat)),
  )
  let int_to_e_nat = x => {
    loop (x, Zero) {
      (0, e) => e
      (x, e) => continue (x - 1, Succ(e_l=Inf(e~)))
    }
  }

  // Build append using VecElim, but specialize to a = Global("a") for this test
  let alpha = e_free("a")

  // motive: \m -> (n : Nat) -> 
  let e_m = Lam(
    e_ret=pi(
      nat,
      pi( // Vec alpha n -> Vec alpha (plus m n)
        vec(alpha, Inf(e=Bound(i=0))),
        Inf(e=appI(appI(e_plus, Bound(i=1)), Bound(i=0))),
      ),
    ),
  )

  // on nil: \n w -> w
  let e_onn = Lam(e_ret=Lam(e_ret=Inf(e=Bound(i=0))))

  // on cons: \m v vs rec n w -> Cons alpha (plus m n) v (rec n w)
  let e_onc = {
    let (w, n, rec, _vs, v, m) = (
      Bound(i=0),
      Bound(i=1),
      Bound(i=2),
      Bound(i=3),
      Bound(i=4),
      Bound(i=5),
    )
    let ret = Inf(
      e=Cons(
        e_ty=alpha,
        e_len=Inf(e=e_plus |> appI(m) |> appI(n)),
        e_x=Inf(e=v),
        e_xs=Inf(e=rec |> appI(n) |> appI(w)),
      ),
    )
    Lam(e_ret=Lam(e_ret=Lam(e_ret=Lam(e_ret=Lam(e_ret=Lam(e_ret=ret))))))
  }

  // For the concrete example, directly produce the function by fixing the first vector
  let n_2 = int_to_e_nat(2)
  let n_1 = int_to_e_nat(1)
  let n_0 = int_to_e_nat(0)

  // helpers for clearer construction and application
  let consC = (ty, len, x, xs) => {
    Inf(e=Cons(e_ty=ty, e_len=len, e_x=x, e_xs=xs))
  }
  let nilC = ty => Inf(e=Nil(e_ty=ty))

  // Build vectors (ExpC) using helpers
  let v_left = consC(
    alpha,
    Inf(e=n_1),
    e_free("x"),
    consC(alpha, Inf(e=n_0), e_free("x"), nilC(alpha)),
  )
  let v_right = consC(alpha, Inf(e=n_0), e_free("y"), nilC(alpha))

  // Use VecElim to get the append-like function for the first vector, then apply n and w via pipeline
  let append_fn = VecElim(
    e_ty=alpha,
    e_m~,
    e_onn~,
    e_onc~,
    e_len=Inf(e=n_2),
    e_xs=v_left,
  )
  let e_append_app = append_fn |> appI(n_1) |> appC(v_right)
  let env = Env::empty()
  debug_inspect(
    e_append_app.eval(env).quote(),
    content=(
      #|Inf(
      #|  e=Cons(
      #|    e_ty=Inf(e=Free(name=Global("a"))),
      #|    e_len=Inf(e=Succ(e_l=Inf(e=Succ(e_l=Inf(e=Zero))))),
      #|    e_x=Inf(e=Free(name=Global("x"))),
      #|    e_xs=Inf(
      #|      e=Cons(
      #|        e_ty=Inf(e=Free(name=Global("a"))),
      #|        e_len=Inf(e=Succ(e_l=Inf(e=Zero))),
      #|        e_x=Inf(e=Free(name=Global("x"))),
      #|        e_xs=Inf(
      #|          e=Cons(
      #|            e_ty=Inf(e=Free(name=Global("a"))),
      #|            e_len=Inf(e=Zero),
      #|            e_x=Inf(e=Free(name=Global("y"))),
      #|            e_xs=Inf(e=Nil(e_ty=Inf(e=Free(name=Global("a"))))),
      #|          ),
      #|        ),
      #|      ),
      #|    ),
      #|  ),
      #|)
    ),
  )
}
