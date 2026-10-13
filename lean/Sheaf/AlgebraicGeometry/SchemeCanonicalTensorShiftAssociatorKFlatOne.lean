/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.TensorShiftOneAssociator
import Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization

/-! # Reassociation of the first-factor translation on K-flat representatives

Source: Stacks Project, Tag 06YH, K-flat total tensor localization; the
triple-totalization calculation of lem-sc-scheme-canonical-tensor-shift-associator.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator-kflat-one).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- Comparing the recorded monoidal and shift instance terms needs extra elaboration work.
/-- First-factor translation by one commutes with reassociation at a K-flat representative.
Source: Stacks Project, Tag 06YH, total tensor localization; the representative
calculation of lem-sc-scheme-canonical-tensor-shift-associator.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator-kflat-one).

Proof. Use P, T and U themselves as representatives of all three factors.
K-flatness makes the tensor localization comparisons invertible.
On the total tensor summand of tridegree (p,q,r), the first-factor translation
comparison has no extra scalar and changes the first index to p+1. Both composites
therefore apply the inverse sheaf-module associator to this same summand.
The differential coefficients of the translated source are -1, (-1)^p and
(-1)^(p+q). Translating the target differential multiplies its coefficients
1, (-1)^(p+1) and (-1)^(p+1+q) by -1, giving the same coefficients.
Thus the two chain maps agree on every summand. Localize this equality. The lax
monoidal associativity equation for localization replaces the complex associators
with the recorded derived associators. The localization shift squares defining
schemeCanonicalTensorShift replace the complex shift comparisons with the recorded
ones. Cancel the invertible tensor and shift comparisons. This asserts the equality only
at Q(P), Q(T), Q(U) and for shift one; transport in all three factors and extension
to other integer shifts are separate steps. Zero factors and the empty scheme give the
unique maps between zero objects, and the sign computation also holds in
characteristic two. No cancellation of noninvertible maps is used. -/
theorem schemeCanonicalTensorShift_associator_kFlat_one (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    ((tensorRight (K ⊗ M)).commShiftIso (1 : ℤ)).hom.app A ≫
        (α_ A K M).inv⟦(1 : ℤ)⟧' =
      (α_ (A⟦(1 : ℤ)⟧) K M).inv ≫
        (((tensorRight K).commShiftIso (1 : ℤ)).hom.app A) ▷ M ≫
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app (A ⊗ K) := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : CategoryTheory.IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  dsimp only
  obtain ⟨hc, hl, hr⟩ := schemeTensorShift_localization_normalization X P T U hP hT hU
  have : IsIso (schemeTensorShiftTargetComparison X P T U) := hc
  have hf := CochainComplex.tensorShiftOne_associator P T U
  have hd :
      (α_ (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧) (DerivedCategory.Q.obj T)
        (DerivedCategory.Q.obj U)).hom ≫
        ((tensorRight (DerivedCategory.Q.obj T ⊗ DerivedCategory.Q.obj U)).commShiftIso
          (1 : ℤ)).hom.app (DerivedCategory.Q.obj P) =
      (((tensorRight (DerivedCategory.Q.obj T)).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj P)) ▷ DerivedCategory.Q.obj U ≫
        ((tensorRight (DerivedCategory.Q.obj U)).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj T) ≫
        (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T)
          (DerivedCategory.Q.obj U)).hom⟦(1 : ℤ)⟧' := by
    apply (cancel_mono (schemeTensorShiftTargetComparison X P T U)).1
    rw [hl, hr, hf]
  apply (cancel_epi (α_ (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧)
    (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj U)).hom).1
  apply (cancel_mono ((α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T)
    (DerivedCategory.Q.obj U)).hom⟦(1 : ℤ)⟧')).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact hd

end AlgebraicGeometry
