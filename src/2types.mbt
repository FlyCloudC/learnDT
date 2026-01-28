///|
pub(all) enum Kind {
  Star
}

///|
pub(all) enum Info {
  HasKind(Kind)
  HasType(Type)
}

///|
pub type Context = List[(Name, Info)]

///|
pub(all) suberror CheckError {
  UnknownIdent(Name)
  IllApply
  MisMatch(ExpC)
}
