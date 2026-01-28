///|
pub type Context = List[(Name, Type)]

///|
pub(all) suberror CheckError {
  UnknownIdent(Name)
  IllApply
  MisMatch(ExpC)
}
