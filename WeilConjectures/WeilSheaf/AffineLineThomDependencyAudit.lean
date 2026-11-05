module

import all WeilConjectures.WeilSheaf.AffineLineBundle
import all WeilConjectures.WeilSheaf.AffineLineSmoothAdjunction
import all WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import all WeilConjectures.WeilSheaf.SmoothPurity
import all WeilConjectures.WeilSheaf.TateTwistPullback
import Lean

/-!
# Dependency audit for the affine-line Thom isomorphism

The Thom proof bypasses the affine-line Weil-trace statement. This audit checks
that its only remaining admitted input is smooth purity; it adds no mathematical
declaration and is not imported by the proof.
-/

#print axioms AlgebraicGeometry.WeilComplex.tateTwistShiftCompUpperStarIso
#print axioms
  AlgebraicGeometry.WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback

open Lean in
run_elab do
  let root :=
    `AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback
  let env ← getEnv
  let rootAxioms ← collectAxioms root
  logInfo m!"Thom axioms: {rootAxioms}"
  for name in rootAxioms do
    unless #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains name do
      throwError "Unexpected axiom: {name}"
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut leaves : Array Name := #[]
  let mut unavailable : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    unless (← collectAxioms name).contains `sorryAx do
      continue
    match env.checked.get.find? name with
    | none => unavailable := unavailable.push name
    | some info =>
      if info.isAxiom then
        unavailable := unavailable.push name
        continue
      match info.value? true with
      | none => unavailable := unavailable.push name
      | some value =>
        let deps := info.type.getUsedConstants ++ value.getUsedConstants
        if deps.contains `sorryAx then
          leaves := leaves.push name
        else if deps.isEmpty then
          unavailable := unavailable.push name
        else
          pending := pending ++ deps
  logInfo m!"Direct admitted dependencies: {leaves.qsort Name.lt}"
  logInfo m!"Unavailable dependency bodies: {unavailable.qsort Name.lt}"
  for name in unavailable do
    if let some idx := env.getModuleIdxFor? name then
      logInfo m!"Missing import all: {env.header.moduleNames[idx.toNat]!}"
  if seen.contains `AlgebraicGeometry.WeilComplex.exists_weilTrace_of_isPullback then
    throwError "The Thom proof still uses the affine-line Weil trace"
  for name in leaves do
    unless name ==
        `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth do
      throwError "Unexpected admitted dependency: {name}"
  unless unavailable.isEmpty do
    throwError "The dependency audit needs the imported proof bodies listed above"
