/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedCore
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# The derived extension vanishes above its defining level

## References

* Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1 (printed p. 21)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Above the defining level every evaluated derived extension is zero. -/
theorem coefficientEvaluationDerivedAbove
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (core : CoefficientEvaluationDerivedCoreData ordinary)
    (n q : ℕ) (hq : n < q) (N : DerivedCategory (coefficientLevelModules (J := J) O ell n)) :
    IsZero ((core.evaluation q).obj ((core.derivedExtension n).obj N)) := by
  classical
  let X := DerivedCategory.Q.objPreimage N
  let i := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  have := core.computes n P hP
  let K := ((ordinary.extension n).mapHomologicalComplex (.up ℤ)).obj P
  let Z := ((coefficientEvaluation (J := J) (O := O) (ell := ell) q).mapHomologicalComplex
    (.up ℤ)).obj K
  have hz : IsZero Z := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_f_injective
    funext j
    exact (ordinary.above n q hq (P.X j)).eq_of_src _ _
  have hQZ := DerivedCategory.Q.map_isZero hz
  let i₁ := (core.evaluation q).mapIso (asIso ((core.counit n).app P)) ≪≫
    (core.evaluationFactors q).app K
  have h₁ : IsZero ((core.evaluation q).obj
      ((core.derivedExtension n).obj (DerivedCategory.Q.obj P))) := hQZ.of_iso i₁
  exact h₁.of_iso ((core.evaluation q).mapIso
    ((core.derivedExtension n).mapIso (asIso (DerivedCategory.Q.map s) ≪≫ i))).symm

end SheafOfModules
