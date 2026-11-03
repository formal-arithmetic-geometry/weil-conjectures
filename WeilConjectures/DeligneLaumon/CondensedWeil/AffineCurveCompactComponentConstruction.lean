/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedWeil.AffineCurveCompactComponent
public import WeilConjectures.AlgebraicGeometry.AffineGeometricComponentsFiniteExtension
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedConstantExtensionFrobenius
import all WeilConjectures.DeligneLaumon.CondensedWeil.CondensedConstantExtensionFrobenius
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel

/-! Explicit native coefficient and compactification on a descended component. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open scoped CategoryTheory.Obj
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedWeil

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.upperStarId CondensedQbarGeometricEvaluation.fieldFiber

/-- A native lisse coefficient on the Noetherian geometric fibre is constructible.
Source: the coefficient restriction paragraph
(blueprint: def-zl-native-affine-compact-component-construction).
Proof: use the trivial stratification and the finite-free local model of lissity. -/
theorem native_lisse_constructible
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (M : WeilModule D ell X)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber X).left M.carrier := by
  let Λ := Profinite.padicAlgClRingObj ell
  let T := D.geometricFiber X
  have : LocallyOfFiniteType T.hom := inferInstanceAs
    (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact T.hom := inferInstanceAs
    (QuasiCompact (CategoryTheory.Limits.pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  have : IsNoetherian T.left := {}
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  exact ⟨Scheme.Stratification.trivial T.left, fun _ ↦
    pullback_finiteConstantLocalModel Λ (𝟙 T.left) M.carrier
      (heart_free_model Λ M.carrier hM)⟩

end WeilConjectures.CondensedWeil
