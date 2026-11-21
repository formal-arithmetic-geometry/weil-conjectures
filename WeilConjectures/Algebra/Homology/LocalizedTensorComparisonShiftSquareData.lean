/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorOrdinaryShiftModel
import WeilConjectures.Algebra.Homology.TensorCoefficientShiftHomology

/-!
# Model data for the shift square of localized tensor comparison

## References

* Stacks Project, Tags 06Y6 and 08IB, with the shift argument of Tag 0DJA(1)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

/-- Transport a model's localization comparison through an isomorphism to a shifted complex. -/
theorem exists_shift_square_data
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (e : L ≅ K⟦-n⟧)
    (mK : BaseDerivedTensorCohomologyModel R A B K C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let eH := (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) (i + n)).mapIso
      (F.mapIso e ≪≫ (F.commShiftIso (-n)).app K) ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-n) (i + n) i
        (by omega)).app (F.obj K)
    ∃ (mL : BaseDerivedTensorCohomologyModel R A B L C)
      (eS : (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mL.cohomology (i + n)) ≅
        (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mK.cohomology i)),
    mK.localizedComparison i = eS.inv ≫ mL.localizedComparison (i + n) ≫ eH.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  intro F eH
  obtain ⟨mL, eT, hordinary⟩ :=
    exists_baseDerivedTensor_ordinary_shift_model R A B C K L n e mK i
  let S := extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)
  let G := restrictScalars.{u} (algebraMap (A ⊗[R] B) C)
  let adj := extendRestrictScalarsAdj.{u, u, u} (algebraMap (A ⊗[R] B) C)
  let eS := S.mapIso eT
  refine ⟨mL, eS, ?_⟩
  have hcoeff := tensorCoefficient_shift_homology
    (algebraMap A (A ⊗[R] B)) (algebraMap (A ⊗[R] B) C) K L n e
    mK.ordinaryToLocalized mL.ordinaryToLocalized
    mK.ordinaryToLocalized_tmul mL.ordinaryToLocalized_tmul i
  have hsquare : eS.hom ≫ mK.localizedComparison i =
      mL.localizedComparison (i + n) ≫ eH.hom := by
    apply (adj.homEquiv _ _).injective
    change (adj.homEquiv _ _) (S.map eT.hom ≫ mK.localizedComparison i) = _
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
      Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      mK.localized_eq, mL.localized_eq]
    dsimp only at hcoeff hordinary
    dsimp only [G, F, eH] at *
    simp only [Category.assoc]
    rw [hcoeff, ← Category.assoc]
    rw [← hordinary]
    simp only [Category.assoc]
  rw [← hsquare]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end ModuleCat
