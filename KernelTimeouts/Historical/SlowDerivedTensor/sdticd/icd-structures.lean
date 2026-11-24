import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names : Array Name := #[
    `Add, `AddCommGroup, `AddGroup, `AddMonoid, `AddSemigroup,
    `AddZero, `AddZeroClass, `CategoryTheory.CategoryStruct,
    `CategoryTheory.Functor, `CategoryTheory.Localization.Construction.LocQuiver,
    `CategoryTheory.NatTrans, `CategoryTheory.ObjectProperty.FullSubcategory,
    `CategoryTheory.Preadditive, `CategoryTheory.Quotient,
    `HomologicalComplex, `NSMul, `Neg, `Quiver, `Sub,
    `SubNegMonoid, `SubNegZeroMonoid, `ZSMul, `Zero]
  for name in names do
    let fields := getStructureFields env name
    let params : Nat := match env.find? name with
      | some (.inductInfo info) => info.numParams
      | _ => 0
    logInfo m!"[ICD-STRUCTURE] {name} params={params} fields={fields}"
    let entry := Json.mkObj [
      ("structure", toJson name.toString),
      ("params", toJson params),
      ("fields", toJson (fields.toList.map toString))]
    logInfo m!"[ICD-STRUCTURE-JSON] {entry.compress}"
