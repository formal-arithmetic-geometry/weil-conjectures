/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Reflector-unit normalization of the conjugate compositor

Source: Stacks Project, Tag 099N, `lemma-pushforward-Noetherian-case` (2),
with the two-transpose reflection calculation using Tags 0037, 0DV0 and 0B65
(blueprint: lem-sbc-reflected-compositor-unit-normalization).

## Main definitions and statements

* `CategoryTheory.ReflectedCompositor.adjunction`: the reflected Hom adjunction.
* `CategoryTheory.ReflectedCompositor.rightIso`: restriction of the right compositor.
* `CategoryTheory.ReflectedCompositor.compositor`: its specified adjunction conjugate.
* `CategoryTheory.ReflectedCompositor.unit_normalization`: the natural unit equation
  and its equivalent ordinary inverse-transpose description.
-/

@[expose] public section

noncomputable section

universe u₀ u₁ u₂ v₀ v₁ v₂

namespace CategoryTheory.ReflectedCompositor

open _root_.CategoryTheory.Functor

variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂]

/-- The specified adjunction on the full subcategories: first use the reflector Hom
bijection, then the ambient adjunction Hom bijection, and identify the full Hom sets.
It is the restriction of the composite of the ambient and reflection adjunctions.
Source: Stacks Tags 0037, 0DV0 and 099N(2)
(blueprint: lem-sbc-reflected-compositor-unit-normalization). -/
def adjunction (P : ObjectProperty A₀) (Q : ObjectProperty A₁)
    {L : A₀ ⥤ A₁} {R : A₁ ⥤ A₀} (adj : L ⊣ R)
    {C : A₁ ⥤ Q.FullSubcategory} (r : C ⊣ Q.ι)
    (hR : ∀ N : Q.FullSubcategory, P (R.obj N.obj)) :
    (P.ι ⋙ L ⋙ C) ⊣ P.lift (Q.ι ⋙ R) hR :=
  (adj.comp r).restrictFullyFaithful P.fullyFaithfulι
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- The completion-unit comparison `L M ⟶ C (L M)`, natural for objects in the source
full subcategory. Source: the reflector in Stacks Tag 099N(2)
(blueprint: lem-sbc-reflected-compositor-unit-normalization). -/
def unitComparison (P : ObjectProperty A₀) (Q : ObjectProperty A₁) (L : A₀ ⥤ A₁)
    {C : A₁ ⥤ Q.FullSubcategory} (r : C ⊣ Q.ι) :
    P.ι ⋙ L ⟶ (P.ι ⋙ L ⋙ C) ⋙ Q.ι :=
  whiskerLeft (P.ι ⋙ L) r.unit

section Triple

variable (P₀ : ObjectProperty A₀) (P₁ : ObjectProperty A₁) (P₂ : ObjectProperty A₂)
  {L₀₁ : A₀ ⥤ A₁} {R₁₀ : A₁ ⥤ A₀} {L₁₂ : A₁ ⥤ A₂} {R₂₁ : A₂ ⥤ A₁}
  {L₀₂ : A₀ ⥤ A₂} {R₂₀ : A₂ ⥤ A₀}
  (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₀₂ : L₀₂ ⊣ R₂₀)
  {C₁ : A₁ ⥤ P₁.FullSubcategory} {C₂ : A₂ ⥤ P₂.FullSubcategory}
  (r₁ : C₁ ⊣ P₁.ι) (r₂ : C₂ ⊣ P₂.ι)
  (h₁₀ : ∀ N : P₁.FullSubcategory, P₀ (R₁₀.obj N.obj))
  (h₂₁ : ∀ N : P₂.FullSubcategory, P₁ (R₂₁.obj N.obj))
  (h₂₀ : ∀ N : P₂.FullSubcategory, P₀ (R₂₀.obj N.obj))
  (d : R₂₀ ≅ R₂₁ ⋙ R₁₀)

/-- Restriction of the right-adjoint composition isomorphism through the full inclusions.
The maps are the original components of `d` and its inverse, using fullness.
Source: Stacks Tag 0B65 applied to the full subcategories in Tag 099N(2)
(blueprint: lem-sbc-reflected-compositor-unit-normalization). -/
def rightIso :
    P₀.lift (P₂.ι ⋙ R₂₀) h₂₀ ≅
      P₁.lift (P₂.ι ⋙ R₂₁) h₂₁ ⋙ P₀.lift (P₁.ι ⋙ R₁₀) h₁₀ :=
  Functor.fullyFaithfulCancelRight P₀.ι (isoWhiskerLeft P₂.ι d)

/-- The reflected compositor is the conjugate of the specified restricted right compositor,
using the composite reflected adjunction, rather than an arbitrary isomorphism of functors.
Source: Stacks Tags 0DV0, 0B65 and 099N(2)
(blueprint: lem-sbc-reflected-compositor-unit-normalization). -/
def compositor :
    (P₀.ι ⋙ L₀₁ ⋙ C₁) ⋙ (P₁.ι ⋙ L₁₂ ⋙ C₂) ≅ P₀.ι ⋙ L₀₂ ⋙ C₂ :=
  (conjugateIsoEquiv (adjunction P₀ P₂ adj₀₂ r₂ h₂₀)
    ((adjunction P₀ P₁ adj₀₁ r₁ h₁₀).comp (adjunction P₁ P₂ adj₁₂ r₂ h₂₁))).symm
    (rightIso P₀ P₁ P₂ h₁₀ h₂₁ h₂₀ d)

/-- The two successive completion units, as a natural transformation. Its component is
`L₁₂(k₀₁,M) ≫ k₁₂,P₀₁M`; no completion unit is inverted.
Source: the explicit two-transpose calculation for Stacks Tag 099N(2)
(blueprint: lem-sbc-reflected-compositor-unit-normalization). -/
def successiveUnits :
    P₀.ι ⋙ L₀₁ ⋙ L₁₂ ⟶ ((P₀.ι ⋙ L₀₁ ⋙ C₁) ⋙ (P₁.ι ⋙ L₁₂ ⋙ C₂)) ⋙ P₂.ι :=
  whiskerRight (unitComparison P₀ P₁ L₀₁ r₁) L₁₂ ≫
    whiskerLeft (P₀.ι ⋙ L₀₁ ⋙ C₁) (unitComparison P₁ P₂ L₁₂ r₂)

/-- Compatibility of the specified ambient and reflected conjugates with all three reflector
units, and the equivalent ordinary composite-adjunction inverse-transpose formula.
The first equality is an equality of natural transformations, including naturality in `M`.
Source: Stacks Tag 099N(2), with the explicit calculation using Tags 0037, 0DV0 and 0B65
(blueprint: lem-sbc-reflected-compositor-unit-normalization).

Proof plan:
1. Expand the reflected Hom bijection as the reflector precomposition followed by the ambient
   Hom bijection. Its unit is the ambient unit followed by `R(k)`.
2. Apply lem-weil-pbc-conjugate-iso-unit-equation to the reflected composite adjunction
   (def-weil-pbc-composite-adjunction). The double reflected transpose of the compositor is
   the reflected unit followed by the restricted right compositor.
3. Naturality of the ambient `12` unit at `k₀₁,M` shows that the ordinary double transpose
   after the two completion units is the same double reflected transpose.
4. The ambient conjugacy unit equation and naturality of `d` at `k₀₂,M` give the same
   transpose for the ambient conjugate followed by `k₀₂,M`. Injectivity of the composite
   Hom bijection proves the equation and the inverse-transpose formula.
5. Naturality of the two successive units follows by applying reflector-unit naturality
   first to the `12` unit and then to the `01` unit. Composing with the natural reflected
   conjugate gives the left side; unit naturality and ambient conjugate naturality give
   the right side. Hence the component equations form the stated natural equation. -/
theorem unit_normalization
    {C₀ : A₀ ⥤ P₀.FullSubcategory} (_r₀ : C₀ ⊣ P₀.ι) :
    successiveUnits P₀ P₁ P₂ r₁ r₂ ≫
        whiskerRight (compositor P₀ P₁ P₂ adj₀₁ adj₁₂ adj₀₂ r₁ r₂ h₁₀ h₂₁ h₂₀ d).hom P₂.ι =
      whiskerLeft P₀.ι ((conjugateIsoEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm d).hom ≫
        unitComparison P₀ P₂ L₀₂ r₂ ∧
    ∀ M : P₀.FullSubcategory,
      ((conjugateIsoEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm d).hom.app M.obj ≫
          r₂.unit.app (L₀₂.obj M.obj) =
        ((adj₀₁.comp adj₁₂).homEquiv M.obj
          (P₂.ι.obj ((P₀.ι ⋙ L₀₂ ⋙ C₂).obj M))).symm
          (P₀.ι.map ((adjunction P₀ P₂ adj₀₂ r₂ h₂₀).unit.app M) ≫
            d.hom.app (P₂.ι.obj ((P₀.ι ⋙ L₀₂ ⋙ C₂).obj M))) := by
  sorry

end Triple

end CategoryTheory.ReflectedCompositor
