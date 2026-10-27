/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.VaryingSiteAbelianSystems
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Coherence of the explicit arrow-indexed free transitions

Source: Stacks Project, spaces-simplicial.tex, Tag 09WG, proof of (5)-(6),
with the supplied coherent site pseudofunctor in place of the simplicial diagram
(blueprint: lem-per-varying-site-free-evaluation-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory

namespace CategoryTheory.CoherentSitePseudofunctor

variable {I : Type u} [Category.{v} I]
  {F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w, w}} (D : CoherentSitePseudofunctor I F)

/-- The actual sum of inverse images. Source: Stacks 09WG (6)
(blueprint: lem-per-varying-site-free-evaluation-coherence). -/
abbrev abelianFreeFamily (i : I) (A : D.abelianFibre i) (j : I) : D.abelianFibre j :=
  ∐ (fun a : j ⟶ i ↦ (D.abelianInverse a).obj A)

/-- The canonical transition, defined by the preserved coproduct universal property.
Source: Stacks 09WG, proof of (5)-(6)
(blueprint: lem-per-varying-site-free-evaluation-coherence). -/
def abelianFreeTransition (i : I) (A : D.abelianFibre i) {j k : I} (c : k ⟶ j) :
    (D.abelianInverse c).obj (D.abelianFreeFamily i A j) ⟶ D.abelianFreeFamily i A k :=
  letI := (D.abelianAdjunction c).leftAdjoint_preservesColimits
  inv (sigmaComparison (D.abelianInverse c)
    (fun a : j ⟶ i ↦ (D.abelianInverse a).obj A)) ≫
      Sigma.desc (fun a : j ⟶ i ↦ (D.abelianInverseComp c a).hom.app A ≫
        Sigma.ι (fun a : k ⟶ i ↦ (D.abelianInverse a).obj A) (c ≫ a))

/-- The defining equation on every pulled-back summand. Source: Stacks 09WG (6)
(blueprint: lem-per-varying-site-free-evaluation-coherence). -/
@[reassoc]
theorem abelianFreeTransition_ι (i : I) (A : D.abelianFibre i)
    {j k : I} (c : k ⟶ j) (a : j ⟶ i) :
    (D.abelianInverse c).map
        (Sigma.ι (fun a : j ⟶ i ↦ (D.abelianInverse a).obj A) a) ≫
      D.abelianFreeTransition i A c =
    (D.abelianInverseComp c a).hom.app A ≫
      Sigma.ι (fun a : k ⟶ i ↦ (D.abelianInverse a).obj A) (c ≫ a) := by
  let : PreservesColimitsOfSize.{v, v} (D.abelianInverse c) :=
    (D.abelianAdjunction c).leftAdjoint_preservesColimits
  simp [abelianFreeTransition]

/-- Identity, cocycle, and identity-generator normalization for the explicit sums.
Source: Stacks 09WG, proof of (5)-(6); the coherence check is the agent's
expansion for a general small coherent diagram
(blueprint: lem-per-varying-site-free-evaluation-coherence).

Proof: direct image is precomposition with the supplied site pseudofunctor, so its
unitors and compositors satisfy the two unit triangles and the associativity
pentagon, componentwise by the corresponding laws of that pseudofunctor. Taking
adjunction mates gives the same laws for abelianInverseId and abelianInverseComp
(Mathlib's leftAdjointCompIso_id_comp, leftAdjointCompIso_comp_id and
leftAdjointCompIso_assoc). Each inverse image preserves coproducts by its given
adjunction. For the identity equation, precompose with the image of each
coprojection and use abelianFreeTransition_ι. The inverse-image unit triangle
identifies the result with the unitor on the sum, by naturality of that unitor.
For the cocycle precompose with the iterated image of each coprojection.
Both sides select the coprojection indexed by (a ≫ b) ≫ t = a ≫ (b ≫ t),
and the mate associativity law identifies their preceding comparison maps.
These precompositions detect equality since the iterated images are coproducts.
Finally apply abelianFreeTransition_ι to the identity summand. The other mate
unit triangle cancels the mapped inverse unitor, leaving the a-summand.
The empty coproduct causes no exception: its mapped coprojections still jointly
detect equality by the same universal property. -/
theorem abelianFreeEvaluation_coherence (i : I) (A : D.abelianFibre i) :
    (∀ j : I, D.abelianFreeTransition i A (𝟙 j) =
      (D.abelianInverseId j).hom.app (D.abelianFreeFamily i A j)) ∧
    (∀ {j k l : I} (a : j ⟶ k) (b : k ⟶ l),
      (D.abelianInverseComp a b).hom.app (D.abelianFreeFamily i A l) ≫
          D.abelianFreeTransition i A (a ≫ b) =
        (D.abelianInverse a).map (D.abelianFreeTransition i A b) ≫
          D.abelianFreeTransition i A a) ∧
    (∀ (j : I) (a : j ⟶ i),
      (D.abelianInverse a).map
          ((D.abelianInverseId i).inv.app A ≫
            Sigma.ι (fun t : i ⟶ i ↦ (D.abelianInverse t).obj A) (𝟙 i)) ≫
          D.abelianFreeTransition i A a =
        Sigma.ι (fun t : j ⟶ i ↦ (D.abelianInverse t).obj A) a) := by sorry

end CategoryTheory.CoherentSitePseudofunctor
