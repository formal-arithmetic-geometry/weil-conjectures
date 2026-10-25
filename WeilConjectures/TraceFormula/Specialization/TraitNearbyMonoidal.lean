/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.TraceFormula.PointDualizable
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.Specialization.PointModel

/-!

# The nearby cycles of the trait are monoidal

Let `S = Spec k'⟦t⟧` be the strictly henselian trait of a separably closed field `k'`, with
geometric generic point `η̄ : Spec Ω ⟶ S` and closed point `i : Spec k' ⟶ S`. The nearby cycles
`Ψ_S = Li^* Rη̄_*` of the trait are monoidal on bounded constructible `ℚ̄_ℓ`-complexes on `Spec Ω`:
the Künneth map of the trait as a model of its geometric generic point is an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap_traitGenericModel`).
This is the computation, in the global-sections step of Gabber's Künneth formula, of the nearby
cycles of `RΓ(X_η̄, A) ⊗ RΓ(Y_η̄, B)`.

## Proof

Every bounded constructible complex on `Spec Ω` is a finite direct sum of shifts `𝟙⟦d⟧` of the
unit (`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`), and `𝟙⟦d⟧ = Lη̄^* 𝟙_S⟦d⟧`. For
`W = 𝟙_S⟦d⟧` the lax tensor map `μ : Rη̄_* Lη̄^* W ⊗ Rη̄_* V ⟶ Rη̄_* (Lη̄^* W ⊗ V)`, precomposed with
the unit `W ⟶ Rη̄_* Lη̄^* W`, is the left projection morphism of `η̄`
(`CategoryTheory.Adjunction.whiskerRight_unit_comp_homEquiv`), an isomorphism since `W` is
invertible. After `Li^*` the unit at `W` is invertible: it is at `W = 𝟙_S` (the cohomology of the
geometric generic point of `S` is that of its closed point,
`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_unit_app`) and the unit commutes with
the shifts. A natural transformation between additive functors which is invertible at the
summands of a finite direct sum is invertible at the sum
(`CategoryTheory.ShiftDecomposition.isIso_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Abstract lemmas -/

namespace CategoryTheory

namespace ShiftDecomposition

variable {C D : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Category D] [Preadditive D] {F G : C ⥤ D}
  [F.Additive] [G.Additive]

/-- A natural transformation between additive functors which is invertible at the summands
`E⟦nⱼ⟧` of a decomposition `P = ⨁ⱼ E⟦nⱼ⟧` is invertible at `P`. -/
lemma isIso_app (τ : F ⟶ G) {E P : C} (Dc : ShiftDecomposition E P)
    (h : ∀ j, IsIso (τ.app ((shiftFunctor C (Dc.deg j)).obj E))) : IsIso (τ.app P) := by
  refine ⟨∑ j, G.map (Dc.proj j) ≫ inv (τ.app _) ≫ F.map (Dc.incl j), ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    calc _ = ∑ j, F.map (Dc.proj j ≫ Dc.incl j) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← τ.naturality_assoc, IsIso.hom_inv_id_assoc, F.map_comp]
      _ = 𝟙 _ := by rw [← F.map_sum, Dc.total, F.map_id]
  · rw [Preadditive.sum_comp]
    calc _ = ∑ j, G.map (Dc.proj j ≫ Dc.incl j) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Category.assoc, Category.assoc, τ.naturality, IsIso.inv_hom_id_assoc, G.map_comp]
      _ = 𝟙 _ := by rw [← G.map_sum, Dc.total, G.map_id]

end ShiftDecomposition

namespace Adjunction

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The lax tensor map `G F B ⊗ G A ⟶ G (F B ⊗ A)` of the right adjoint `G` (the transpose of the
tensor product of the counits), precomposed with the unit `B ⟶ G F B`, is the left projection
morphism `B ⊗ G A ⟶ G (F B ⊗ A)`. -/
lemma whiskerRight_unit_comp_homEquiv (B : D) (A : C) :
    adj.unit.app B ▷ G.obj A ≫ adj.homEquiv _ _
        (Functor.OplaxMonoidal.δ F (G.obj (F.obj B)) (G.obj A) ≫
          (adj.counit.app (F.obj B) ⊗ₘ adj.counit.app A)) =
      adj.leftProjectionMorphism B A := by
  rw [← homEquiv_naturality_left, leftProjectionMorphism]
  congr 1
  refine (Functor.OplaxMonoidal.δ_natural_left_assoc F (adj.unit.app B) (G.obj A)
    (adj.counit.app (F.obj B) ⊗ₘ adj.counit.app A)).symm.trans ?_
  congr 1
  rw [← tensorHom_id, tensorHom_comp_tensorHom]
  erw [left_triangle_components]
  rw [Category.id_comp, id_tensorHom]
  rfl

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The unit of the geometric generic point of the trait -/

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k' : Type u) [Field k'] [IsSepClosed k']

/-- After restriction to the closed point, the derived unit `Λ_S ⟶ Rη̄_* Lη̄^* Λ_S` of the
geometric generic point of the trait is an isomorphism. -/
lemma isIso_upperStar_traitClosedPoint_map_derivedUnit_app_unit :
    IsIso (L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
      ((derivedUpperStarLowerStarAdjunction Λ (NearbyCyclesModel.traitGenericModel k').j).unit.app
        (𝟙_ _))) := by
  have hU : UpperStarInvertsLowerStarUnit Λ (traitGenericPoint k') (traitClosedPoint k') :=
    ⟨isIso_upperStar_traitClosedPoint_map_unit_app Λ k',
      isZero_upperStar_traitClosedPoint_obj_rightDerived Λ k'⟩
  have h := (NearbyCyclesModel.traitGenericModel k').isIso_unit_of_upperStarInvertsLowerStarUnit Λ
    hU
  have h' := @IsIso.of_isIso_comp_left _ _ _ _ _ (leftDerivedUpperStarUnitIso Λ _).inv _ _ h
  rw [Functor.map_comp] at h'
  exact IsIso.of_isIso_comp_right _ (L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
    (R(((NearbyCyclesModel.traitGenericModel k').j)_*⟦Λ⟧).map
      ((leftDerivedUpperStarUnitIso Λ (NearbyCyclesModel.traitGenericModel k').j).hom ≫
        (leftDerivedUpperStarUnitIso Λ (NearbyCyclesModel.traitGenericModel k').ε).inv)))

/-- After restriction to the closed point, the derived unit `W ⟶ Rη̄_* Lη̄^* W` of the geometric
generic point of the trait is an isomorphism at the shifts `W = Λ_S⟦d⟧` of the unit. -/
lemma isIso_upperStar_traitClosedPoint_map_derivedUnit_app_shift (d : ℤ) :
    IsIso (L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧).map
      ((derivedUpperStarLowerStarAdjunction Λ (NearbyCyclesModel.traitGenericModel k').j).unit.app
        ((shiftFunctor _ d).obj (𝟙_ _)))) := by
  let τ := Functor.whiskerRight
    (derivedUpperStarLowerStarAdjunction Λ (NearbyCyclesModel.traitGenericModel k').j).unit
    L(((NearbyCyclesModel.traitGenericModel k').i)^*⟦Λ⟧)
  have := isIso_upperStar_traitClosedPoint_map_derivedUnit_app_unit Λ k'
  exact (NatTrans.isIso_app_shift_iff τ (𝟙_ _) d).2 this

end Unit


end AlgebraicGeometry.ProEtale.CondensedRing
