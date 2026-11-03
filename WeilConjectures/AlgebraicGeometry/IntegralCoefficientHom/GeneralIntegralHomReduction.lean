/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientHom.IntegralConstructibleInternalHomData

/-! # Canonical integral Hom reduction: transpose compatibility

The constructions and evaluation equation are supplied by the existing data module.
This file proves compatibility with arbitrary tensor-Hom transposes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientHom
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

set_option maxHeartbeats 1000000 in
-- Elaborating naturality involves the two universe-polymorphic derived tensor categories.
/-- Reduced tensor-Hom transposes commute with the canonical quotient-Hom map.
Source: lem-coef-integral-hom-reduction.proof.md, first paragraph.
(blueprint: lem-coef-general-integral-hom-reduction). -/
theorem comparison_transpose (X : Scheme.{u}) (π : R) (n : ℕ)
    (K L T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)))
    (f : T ⟶
      (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
        (op K)).obj L)) :
    (CondensedRing.derivedTensorHomAdjunction
      (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R)))
        ((reduction R X π n).obj K)).homEquiv _ _
      ((reductionTensorIso R X π n K T).inv ≫
        (reduction R X π n).map
          (((CondensedRing.derivedTensorHomAdjunction
            (Profinite.continuousCoefficientRingObj R) K).homEquiv T L).symm f)) =
      (reduction R X π n).map f ≫ comparison R X π n K L := by
  let F := reduction R X π n
  let A := CondensedRing.derivedTensorHomAdjunction
    (Profinite.continuousCoefficientRingObj R) K
  let B := CondensedRing.derivedTensorHomAdjunction
    (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R))) (F.obj K)
  apply (B.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, B.homEquiv_naturality_left_symm]
  change _ = (F.obj K ◁ F.map f) ≫ _
  rw [Adjunction.homEquiv_counit, F.map_comp]
  let := Mod.extendScalarsMonoidal (coefficientMap (quotientMap R π n) X)
  let := Mod.extendScalars_preservesFlat (coefficientMap (quotientMap R π n) X)
  let τ := asIso
    (Mod.extendScalars (coefficientMap (quotientMap R π n) X)).leftDerivedTensorComparison
  have ht := ((τ.app K).inv.naturality f).symm
  change (reductionTensorIso R X π n K T).inv ≫ F.map (K ◁ f) =
    (F.obj K ◁ F.map f) ≫
      (reductionTensorIso R X π n K
        (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
          (op K)).obj L)).inv at ht
  change (reductionTensorIso R X π n K T).inv ≫
      F.map (K ◁ f) ≫ F.map (A.counit.app L) =
    (F.obj K ◁ F.map f) ≫ _
  have hev : (B.homEquiv _ _).symm (comparison R X π n K L) =
      (reductionTensorIso R X π n K
        (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
          (op K)).obj L)).inv ≫ F.map (A.counit.app L) :=
    (B.homEquiv _ _).symm_apply_apply _
  rw [hev, ← Category.assoc, ht, Category.assoc]

end AlgebraicGeometry.ProEtale.IntegralCoefficientHom
