/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.CategoryTheory.FlatScalarKoszulModels

/-! # Ordered-coordinate scalar comparison for finite Koszul towers

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-weil-pbc-strict-scalar-koszul-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

private theorem coordinate_naturality (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) (m : ℕ)
    (e : Fin r → Bool) (n : ℤ) :
    (((ringedKoszulTensorTowerFunctor O r a).map f).f n).app (op m) ≫
        coordinate O r a M m e n =
      coordinate O r a N m e n ≫ f.f (n + degree r e) := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  change (HomologicalComplex.mapBifunctorMap f
    (𝟙 ((ringedKoszulDualTower O r a).obj (op m))) (tensor O) (.up ℤ)).f n ≫ _ = _
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.id_f, Functor.map_id, Category.id_comp]
  dsimp only [coordinate]
  simp only [HomologicalComplex.ι_mapBifunctorDesc,
    HomologicalComplex.ι_mapBifunctorDesc_assoc]
  by_cases hp : p = n + degree r e
  · subst p
    simp only [dif_pos, eqToHom_refl, Category.comp_id]
    rw [← Category.assoc,
      ← ((tensor O).map (f.f (n + degree r e))).naturality
        (dualCoordinate O r a m e q), Category.assoc]
    exact congrArg (fun g ↦ ((tensor O).obj (N.X (n + degree r e))).map
      (dualCoordinate O r a m e q) ≫ g)
      (MonoidalCategory.rightUnitor_naturality (f.f (n + degree r e)))
  · simp only [dif_neg hp, comp_zero, zero_comp]

private theorem emptyUnitComponent_isIso (O : Sheaf J CommRingCat.{u})
    (a : Fin 0 → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (m : ℕᵒᵖ) :
    IsIso (ringedKoszulTensorUnitComponent O 0 a N m) := by
  have hP : ringedKoszulProjection O 0 a m.unop = 𝟙 _ := rfl
  have : IsIso (ringedKoszulProjection O 0 a m.unop) := by
    rw [hP]
    infer_instance
  have : IsIso (ringedKoszulDualUnit O 0 a m.unop) := by
    unfold ringedKoszulDualUnit
    infer_instance
  dsimp only [ringedKoszulTensorUnitComponent]
  infer_instance

/-- The finite ordered Koszul comparison is independent of flatness and of derived
categories.

Source: Stacks Project, algebraization.tex, Tag 0A0E (finite Koszul calculation);
more-algebra.tex, Tag 0913 (Koszul complexes).
(blueprint: lem-weil-pbc-strict-scalar-koszul-comparison).

Proof: Each positive factor is free of rank one in degrees zero and one. Inductively
expand their ordered tensor into its summands indexed by Boolean subsets. Dualizing
these finite free sums and tensoring with N gives, in total degree n, the direct sum
of N.X (n + degree e). Its coordinate projections are exactly coordinate: evaluation
on positiveBasis is the dual projection, and mapBifunctorDesc supplies the projection
from the tensor totalization. Under scalar restriction both direct sums have the same
summands and the same R action. The identity on each coordinate therefore gives
mutually inverse maps. The total differential is the sum of the differential of N
and the signed multiplication maps by the images of a_i^(m+1). Restriction sends
every multiplication by a_i to multiplication by its image, so these identity
coordinate maps commute with the differential. The inverse-system transition on
the subset e multiplies by the product of the image sections selected by e; these
maps also commute. The construction is natural in chain maps N. Finally, the
coaugmentation has only its empty-subset coordinate, equal to the identity, so it
is carried to the coaugmentation over R. Empty lists, zero sections, repeated
sections and the zero ring satisfy these same finite formulas. -/
theorem strictScalarKoszulComparison (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections) :
    ∃ h : ringedKoszulTensorTowerFunctor B r (imageSections φ a) ⋙
        restrictTowerComplex φ ≅
      restrictComplex φ ⋙ ringedKoszulTensorTowerFunctor R r a,
      (∀ (N : ringedSiteComplex B) (m : ℕ) (e : Fin r → Bool) (n : ℤ),
        ((h.hom.app N).f n).app (op m) ≫
            coordinate R r a ((restrictComplex φ).obj N) m e n =
          (restriction φ).map (coordinate B r (imageSections φ a) N m e n)) ∧
      (∀ (N : ringedSiteComplex B) (m : ℕᵒᵖ) (n : ℤ),
        (restriction φ).map
            ((ringedKoszulTensorUnitComponent B r (imageSections φ a) N m).f n) ≫
            ((h.hom.app N).f n).app m =
          (ringedKoszulTensorUnitComponent R r a ((restrictComplex φ).obj N) m).f n) := by sorry

end CategoryTheory.FlatScalarKoszul
