/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator

/-! # Associativity of tensor with the translated unit

Source: Stacks Project, Tag 06YH, first-variable total tensor translation;
associativity calculation in the parent translated-unit plan.
(blueprint: lem-sc-scheme-canonical-shift-unit-associativity).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

private theorem tensorShiftUnitCalculation {C : Type*} [Category* C]
    [MonoidalCategory C] [HasShift C ℤ]
    [∀ B : C, (tensorRight B).CommShift ℤ]
    (K M : C) (n : ℤ)
    (h : ((tensorRight (K ⊗ M)).commShiftIso n).hom.app (𝟙_ C) ≫
        (α_ (𝟙_ C) K M).inv⟦n⟧' =
      (α_ ((𝟙_ C)⟦n⟧) K M).inv ≫
        (((tensorRight K).commShiftIso n).hom.app (𝟙_ C)) ▷ M ≫
        ((tensorRight M).commShiftIso n).hom.app ((𝟙_ C) ⊗ K)) :
    ((tensorRight (K ⊗ M)).commShiftIso n).hom.app (𝟙_ C) ≫
        (λ_ (K ⊗ M)).hom⟦n⟧' =
      (α_ ((𝟙_ C)⟦n⟧) K M).inv ≫
        (((tensorRight K).commShiftIso n).hom.app (𝟙_ C) ≫
          (λ_ K).hom⟦n⟧') ▷ M ≫
        ((tensorRight M).commShiftIso n).hom.app K := by
  simp only [comp_whiskerRight, Category.assoc]
  have hn := (tensorRight M).commShiftIso_hom_naturality (λ_ K).hom n
  dsimp at hn
  rw [leftUnitor_tensor_hom, Functor.map_comp, ← Category.assoc, h]
  simp only [Category.assoc]
  rw [← hn]

/-- The first-variable canonical shift comparison is tensoring the translated-unit
comparison with the fixed factor, after reassociating. This is a tensor identity
on a single scheme; it makes no assertion about pullback or triangulated functors.
Source: Stacks Project, Tag 06YH, total tensor translation, and the associativity
calculation of the parent plan.
(blueprint: lem-sc-scheme-canonical-shift-unit-associativity).

Proof. On total tensor complexes use the structure sheaf concentrated in degree
zero as the unit. Its translate has its sole term in degree minus one. The
comparison c_K is the canonical first-variable shift comparison followed by the
translated left unitor. In the triple tensor total complex, reassociation sends
the summand with indices (-1,p,q) to that with the same indices. Applying c_K and
then translating K tensor M gives the same first-variable comparison as applying
c_(K tensor M) directly. The differential of the triple totalization has signs
1, (-1)^(-1), (-1)^(-1+p); the shift comparison on the two paths changes these
signs identically. Thus the component maps agree on each summand, and hence on
the total complex. Choose K-flat representatives and use associativity of the
localized tensor comparisons. Both expressions are natural in K and M and are
unchanged under quasi-isomorphisms of these representatives, so the equality
descends to the recorded tensor product on the derived category. Zero factors
and the empty scheme give the same identity of zero morphisms. -/
theorem schemeCanonicalShiftUnitIso_tensor (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K M : schemeDerivedCategory X) :
    letI := schemeCanonicalTensorShift X
    letI : (tensorRight M).CommShift ℤ :=
      Functor.CommShift₂.commShiftFlipObj (h := .int) M
    (schemeCanonicalShiftUnitIso X (K ⊗ M)).hom =
      (α_ ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) K M).inv ≫
        (schemeCanonicalShiftUnitIso X K).hom ▷ M ≫
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  simpa only [schemeCanonicalShiftUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom] using tensorShiftUnitCalculation K M (1 : ℤ)
      (schemeCanonicalTensorShift_associator X (𝟙_ (schemeDerivedCategory X)) K M 1)

end AlgebraicGeometry
