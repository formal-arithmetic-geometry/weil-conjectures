import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

universe u' u

set_option debug.skipKernelTC true in
lemma adTensorOriginal
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    (X : Scheme.{u}) [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
      @tensorObj
        (DerivedMonoidal DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
        _ inferInstance K L := by
  rfl

set_option debug.skipKernelTC true in
lemma adTensorSamePath
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    (X : Scheme.{u}) [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _
      (inferInstance : MonoidalCategoryStruct (DerivedCategory (Sheaf X.smallEtaleTopology A))) K L =
    @tensorObj
      (DerivedMonoidal DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ (inferInstance : MonoidalCategoryStruct (DerivedCategory (Sheaf X.smallEtaleTopology A))) K L := by
  rfl

set_option debug.skipKernelTC true in
lemma adTensorShared
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    (X : Scheme.{u}) [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    [MC : MonoidalCategoryStruct (DerivedCategory (Sheaf X.smallEtaleTopology A))]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ MC K L =
      @tensorObj
        (DerivedMonoidal DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
        _ MC K L := by
  rfl

private partial def providerPair (a b : Expr) : MetaM (Expr × Expr × LocalContext) := do
  match a, b with
  | .forallE n d body _, .forallE _ _ body' _ =>
    withLocalDeclD n d fun x => providerPair (body.instantiate1 x) (body'.instantiate1 x)
  | _, _ =>
    let left := a.getAppArgs[2]!.getAppArgs[2]!
    let right := b.getAppArgs[2]!.getAppArgs[2]!
    return (left, right, ← getLCtx)

private def inspectProvider (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName | throwError "missing declaration"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "Kernel.check(value) failed"
  let start ← IO.monoMsNow
  let result := Kernel.isDefEq env default inferred info.type
  let stop ← IO.monoMsNow
  let status := match result with
    | .ok true => "equal"
    | .ok false => "unequal"
    | .error _ => "error"
  logInfo m!"AD-PROVIDER root={declName} ms={stop-start} result={status} inferredSize={inferred.sizeWithoutSharing} declaredSize={info.type.sizeWithoutSharing}"
  liftTermElabM do
    let (left, right, lctx) ← providerPair inferred info.type
    let leftType := Kernel.check env lctx left
    let rightType := Kernel.check env lctx right
    let sameType : Bool := match leftType, rightType with
      | .ok l, .ok r => l.equal r
      | _, _ => false
    let typeDefeq := match leftType, rightType with
      | .ok l, .ok r =>
        match Kernel.isDefEq env lctx l r with
        | .ok true => "equal"
        | .ok false => "unequal"
        | .error _ => "error"
      | _, _ => "invalid"
    let pairStart ← IO.monoMsNow
    let pairResult := Kernel.isDefEq env lctx left right
    let pairStop ← IO.monoMsNow
    let pairStatus := match pairResult with
      | .ok true => "equal"
      | .ok false => "unequal"
      | .error _ => "error"
    logInfo m!"AD-PROVIDER-PAIR root={declName} ms={pairStop-pairStart} result={pairStatus} leftSize={left.sizeWithoutSharing} rightSize={right.sizeWithoutSharing} equal={left.equal right} sameType={sameType} typeDefeq={typeDefeq}"

set_option maxHeartbeats 0 in
run_cmd do
  inspectProvider ``adTensorOriginal
  inspectProvider ``adTensorSamePath
  inspectProvider ``adTensorShared

end AlgebraicGeometry
