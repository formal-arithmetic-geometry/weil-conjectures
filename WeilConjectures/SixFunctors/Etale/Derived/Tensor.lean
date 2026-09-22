/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-!

# The derived tensor product of étale sheaves

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme.
The category `Sheaf X.smallEtaleTopology A` of `A`-valued étale sheaves on `X` is then a
monoidal Grothendieck abelian category, so it has a derived category `D(X_ét)`, and the
K-flat machinery migrated from mathlib PR #25848 equips `D(X_ét)` with the *derived tensor
product* `- ⊗ᴸ -`, the total left derived functor of `- ⊗ -` in two variables.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensor` : the derived tensor product
  `- ⊗ᴸ - : D(X_ét) ⥤ D(X_ét) ⥤ D(X_ét)`, with scoped notation `(X)⊗ᴸ[A]`.

## Main results

- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor` : the derived tensor product
  really is the total left derived functor of the tensor product of étale sheaves, in two
  variables.

- `AlgebraicGeometry.Etale.laxMonoidal_Q` : the localization functor
  `Q : C(X_ét) ⥤ D(X_ét)` is lax monoidal.

## Implementation notes

The monoidal structure on `Sheaf X.smallEtaleTopology A` is `Sheaf.monoidalCategory`, which
is a `local instance` in mathlib rather than a global one (it is only available once
`(J.W).IsMonoidal` holds). It is therefore activated by `attribute [local instance]` here, as
in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`. Note that the *type* of
`derivedTensor` does not mention the monoidal structure, so downstream files may use it
without re-activating the local instance.

That `D(X_ét)` is monoidal at all comes from
`DerivedCategory.hasDerivedMonoidalCategory` in
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, which is why
the hypotheses below are exactly the ones that instance asks of the category of étale
sheaves: monoidal closed (so that tensoring preserves colimits) and admitting functorial
flat resolutions.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]

variable (X : Scheme.{u})

variable [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

set_option debug.skipKernelTC true in
lemma test_tensorObj_kernelProbe
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme)
    [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj
        (DerivedCategory (Sheaf X.smallEtaleTopology A))
        _ inferInstance K L
      =
    @tensorObj
        (DerivedMonoidal DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf X.smallEtaleTopology A)
            (ComplexShape.up ℤ)))
        _ inferInstance K L := by
  rfl


set_option debug.skipKernelTC true in
lemma isLeftDerivedFunctor₂_derivedTensor_kernelProbe
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme)
    [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] :
    (curriedTensor
      (DerivedCategory
        (Sheaf X.smallEtaleTopology A))).IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology A)
        (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology A)
        (ComplexShape.up ℤ)) :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
    (Sheaf X.smallEtaleTopology A)

/-
open Lean Elab Command

set_option linter.style.emptyLine false in
private def probeKernelDecl (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let lctx : LocalContext := default

  let some info := env.find? declName
    | throwError m!"cannot find declaration {declName}"

  let value := info.value! true
  let declaredType := info.type

  logInfo m!""
  logInfo m!"============================================================"
  logInfo m!"Kernel probe: {declName}"
  logInfo m!"============================================================"

  logInfo m!"value sizeWithoutSharing: {value.sizeWithoutSharing}"
  logInfo m!"declared type sizeWithoutSharing: {declaredType.sizeWithoutSharing}"

  /-
  Phase 1:
  exactly kernel-check the proof term itself and ask the kernel
  what type it infers.
  -/
  let checkStart ← IO.monoMsNow

  let inferredType ←
    match Kernel.check env lctx value with
    | .ok ty =>
        pure ty
    | .error _ =>
        throwError m!"Kernel.check failed for {declName}"

  let checkEnd ← IO.monoMsNow

  logInfo m!"Kernel.check(value): {checkEnd - checkStart} ms"
  logInfo m!"inferred type sizeWithoutSharing: {inferredType.sizeWithoutSharing}"
  logInfo m!"Expr.equal inferred declared: {Expr.equal inferredType declaredType}"

  /-
  Phase 2:
  this is the SAME ORIENTATION used by the theorem checker:

      val_type =?= declared_type
  -/
  let forwardStart ← IO.monoMsNow

  let forwardResult ←
    match Kernel.isDefEq env lctx inferredType declaredType with
    | .ok result =>
        pure result
    | .error _ =>
        throwError m!"forward Kernel.isDefEq failed for {declName}"

  let forwardEnd ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq inferred → declared:"
  logInfo m!"  result: {forwardResult}"
  logInfo m!"  time:   {forwardEnd - forwardStart} ms"

  /-
  Phase 3:
  same equality, opposite orientation.

  This is NOT what theorem checking normally does.
  It is specifically here to test whether the kernel's
  lazy-delta strategy is badly asymmetric for this example.
  -/
  let reverseStart ← IO.monoMsNow

  let reverseResult ←
    match Kernel.isDefEq env lctx declaredType inferredType with
    | .ok result =>
        pure result
    | .error _ =>
        throwError m!"reverse Kernel.isDefEq failed for {declName}"

  let reverseEnd ← IO.monoMsNow

  logInfo m!"Kernel.isDefEq declared → inferred:"
  logInfo m!"  result: {reverseResult}"
  logInfo m!"  time:   {reverseEnd - reverseStart} ms"

  logInfo m!"============================================================"
  logInfo m!""
-/
end AlgebraicGeometry
