///|
/// i == 当前上下文套的 Lam 的层数
fn ExpI::infer_type(
  self : ExpI,
  i : Int,
  ctx : Context,
) -> Type raise CheckError {
  match self {
    Ann(e, e_ty) => {
      e_ty.check_type(i, ctx, VStar)
      let ty = e_ty.eval(Env::empty())
      e.check_type(i, ctx, ty)
      ty
    }
    Star => VStar
    Pi(e_par_ty, e_ret_ty) => {
      e_par_ty.check_type(i, ctx, VStar)
      let par_ty = e_par_ty.eval(Env::empty())
      e_ret_ty
      .subst(0, Free(Local(i)))
      .check_type(i + 1, ctx.add((Local(i), par_ty)), VStar)
      VStar
    }
    Free(name) => {
      guard ctx.lookup(name) is Some(ty) else { raise UnknownIdent(name) }
      ty
    }
    App(e_fun, e_arg) => {
      let fun_ty = e_fun.infer_type(i, ctx)
      guard fun_ty is VPi(ty_par, ty_ret) else { raise IllApply }
      e_arg.check_type(i, ctx, ty_par)
      ty_ret(e_arg.eval(Env::empty()))
    }
    Bound(_) => panic()
    // Because we are turning a bound variable into a free variable,
    // the type checker will never encounter a bound variable.
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
    Inf(e) => {
      let ty_infer = e.infer_type(i, ctx)
      guard ty.quote(0) == ty_infer.quote(0) else { raise MisMatch(self) }
    }
    Lam(e_ret) => {
      guard ty is VPi(ty_par, ty_ret) else { raise MisMatch(self) }
      let new_ctx = ctx.add((Local(i), ty_par))
      e_ret //
      .subst(0, Free(Local(i)))
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
    Ann(e, ty) => Ann(e.subst(i, e_new), ty.subst(i, e_new))
    Star => e_old
    Pi(e_arg_ty, e_ret_ty) =>
      Pi( //
        e_arg_ty.subst(i, e_new),
        e_ret_ty.subst(i + 1, e_new),
      )
    Bound(j) => if i == j { e_new } else { e_old }
    Free(_) => e_old
    App(e_fun, e_arg) =>
      App( //
        e_fun.subst(i, e_new),
        e_arg.subst(i, e_new),
      )
  }
}

///|
fn ExpC::subst(e_old : ExpC, i : Int, e_new : ExpI) -> ExpC {
  match e_old {
    Inf(e) => Inf(e.subst(i, e_new))
    Lam(e) => Lam(e.subst(i + 1, e_new))
  }
}

// --------------------------------------------------------------------

///|
/// 把 Value 反向转回 Term
fn Value::quote(self : Value, i : Int) -> ExpC {
  match self {
    VLam(f) =>
      Lam(
        f(Value::free(Quote(i))) //
        .quote(i + 1),
      )
    VStar => Inf(Star)
    VPi(v, f) =>
      Inf(
        Pi(
          v.quote(i),
          f(Value::free(Quote(i))) //
          .quote(i + 1),
        ),
      )
    VNeutral(n) => Inf(n.quote(i))
  }
}

///|
pub fn Value::quote0(self : Value) -> ExpC {
  self.quote(0)
}

///|
fn Neutral::quote(self : Neutral, i : Int) -> ExpI {
  match self {
    // Bound 从里往外数
    // Quote 从外往里数
    NFree(Quote(k)) => Bound(i - k - 1)
    NFree(name) => Free(name)
    NApp(n_fun, arg) => App(n_fun.quote(i), arg.quote(i))
  }
}

// --------------------------------------------------------------------

///|
pub impl Show for Value with output(self, logger) {
  match self {
    VStar => logger.write_string("VStar")
    VLam(_) => logger.write_string("VLam(...)")
    VNeutral(n) =>
      logger..write_string("VNeutral(")..write_object(n)..write_char(')')
    VPi(par_ty, ret_ty) =>
      logger
      ..write_string("VPi(")
      ..write_object(par_ty)
      ..write_string(", _ => ")
      ..write_object(ret_ty(Value::free(Global("_"))))
      ..write_char(')')
  }
}

///|
test "example p12" {
  let e_id = Lam(Inf(Bound(0)))
  let e_cst = Lam(Lam(Inf(Bound(1))))
  let e_free = name => Inf(Free(Global(name)))
  // -------------------------------------
  let e_ty_a = Inf(Free(Global("a")))
  let e_ty_b = Inf(Free(Global("b")))
  // -------------------------------------
  let fun = (x, y) => Inf(Pi(x, y))
  let e_1 = e_id //
    |> Ann(fun(e_ty_a, e_ty_a))
    |> App(e_free("y"))
  let e_2 = e_cst
    |> Ann(
      fun( //
        fun(e_ty_b, e_ty_b),
        fun(e_ty_a, fun(e_ty_b, e_ty_b)),
      ),
    )
    |> App(e_id)
    |> App(e_free("y"))
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
  inspect(
    e_1.eval(empty_env).quote(0),
    content=(
      #|Inf(Free(Global("y")))
    ),
  )
  inspect(
    e_2.eval(empty_env).quote(0),
    content=(
      #|Lam(Inf(Bound(0)))
    ),
  )
  inspect(
    e_1.infer_type(0, env_1),
    content=(
      #|VNeutral(NFree(Global("a")))
    ),
  )
  inspect(
    e_2.infer_type(0, env_2),
    content=(
      #|VPi(VNeutral(NFree(Global("b"))), _ => VNeutral(NFree(Global("b"))))
    ),
  )
}
