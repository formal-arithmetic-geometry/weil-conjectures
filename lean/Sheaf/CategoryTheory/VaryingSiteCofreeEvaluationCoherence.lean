/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.VaryingSiteAbelianSystems
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Coherence of the explicit arrow-indexed cofree transitions

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ, canonical product
transitions and compatibility of the displayed map gamma
(blueprint: lem-per-varying-site-cofree-evaluation-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory

namespace CategoryTheory.CoherentSitePseudofunctor

variable {I : Type u} [Category.{v} I]
  {F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w, w}} (D : CoherentSitePseudofunctor I F)

/-- The actual product of direct images. Source: Stacks 0EXZ
(blueprint: lem-per-varying-site-cofree-evaluation-coherence). -/
abbrev abelianCofreeFamily (i : I) (A : D.abelianFibre i) (j : I) : D.abelianFibre j :=
  ∏ᶜ (fun a : i ⟶ j ↦ (D.abelianDirect a).obj A)

/-- The transition is a product lift of explicit counit maps. Inverse image is
not assumed to preserve this product. Source: Stacks 0EXZ
(blueprint: lem-per-varying-site-cofree-evaluation-coherence). -/
def abelianCofreeTransition (i : I) (A : D.abelianFibre i) {j k : I} (c : k ⟶ j) :
    (D.abelianInverse c).obj (D.abelianCofreeFamily i A j) ⟶
      D.abelianCofreeFamily i A k :=
  Pi.lift (fun b : i ⟶ k ↦
    (D.abelianInverse c).map
      (Pi.π (fun a : i ⟶ j ↦ (D.abelianDirect a).obj A) (b ≫ c) ≫
        (D.abelianDirectComp b c).inv.app A) ≫
      (D.abelianAdjunction c).counit.app ((D.abelianDirect b).obj A))

/-- The extension family before checking transition compatibility.
Source: Stacks 0EXZ, the factors of gamma
(blueprint: lem-per-varying-site-cofree-evaluation-coherence). -/
def abelianCofreeExtension [∀ (j k : I) (a : j ⟶ k), (D.abelianInverse a).Additive]
    (i : I) (X : D.AbelianSystem) (A : D.abelianFibre i) (h : X.obj i ⟶ A) (j : I) :
    X.obj j ⟶ D.abelianCofreeFamily i A j :=
  Pi.lift (fun a : i ⟶ j ↦
    (D.abelianAdjunction a).homEquiv (X.obj j) A (X.transition a ≫ h))

/-- The defining factor equation. Source: Stacks 0EXZ
(blueprint: lem-per-varying-site-cofree-evaluation-coherence). -/
@[reassoc]
theorem abelianCofreeTransition_π (i : I) (A : D.abelianFibre i)
    {j k : I} (c : k ⟶ j) (b : i ⟶ k) :
    D.abelianCofreeTransition i A c ≫
        Pi.π (fun b : i ⟶ k ↦ (D.abelianDirect b).obj A) b =
      (D.abelianInverse c).map
        (Pi.π (fun a : i ⟶ j ↦ (D.abelianDirect a).obj A) (b ≫ c) ≫
          (D.abelianDirectComp b c).inv.app A) ≫
        (D.abelianAdjunction c).counit.app ((D.abelianDirect b).obj A) := by
  exact Pi.lift_π _ _

/-- The product-transition identities and compatibility of the explicit extension.
There is no adjunction assertion here, and no inverse identities of Hom maps are assumed.
Source: Stacks 0EXZ, canonical transitions and compatibility of gamma; categories.tex,
Tags 0037 and 0DV0 for naturality and composite adjunctions
(blueprint: lem-per-varying-site-cofree-evaluation-coherence).

Proof: write P_a for direct image and Q_a for its left adjoint. Direct-image
unitors and compositors are induced by the site pseudofunctor, hence obey its
triangles and pentagon on each section. The mate comparisons obey the same laws.
Transpose the c-transition to t_c: R_j -> P_c R_k. Its b-projection, after P_c,
is the (b ≫ c)-projection followed by the inverse direct-image compositor.
This follows from counit naturality and the triangle identities. Right adjoints
preserve products, so these mapped projections detect equality. They show the
identity law and the cocycle for t: on the e-factor both composite maps select
(e ≫ a) ≫ b = e ≫ (a ≫ b), with equal transports by the pentagon.
The composite Hom bijection transports this to the displayed cocycle for Q.
For the third clause, the mate definition of Q_id -> Id identifies the adjunct
of Q_id X -> X -> Y with h followed by the inverse of P_id Y -> Y, so composition
with the latter gives h. For the fourth clause, the identity-factor projection of
t_a, followed by P_a of P_id A -> A, is the a-projection, by the direct-image
unit triangle. Naturality of the Hom bijection gives exactly the fourth equation.
Finally transpose the system cocycle for X. It says theta_(a≫b) equals theta_b
followed by P_b(theta_a), with the direct-image compositor inserted. Composing
with P_(a≫b)(h) and using naturality proves that the extension family has the
same b-factor on the two sides of its compatibility equation. The mapped product
projections detect equality; transposition gives the final clause. No inverse
image of an infinite product is identified with a product. Empty products and
nonidentity endomorphisms are covered by these universal-property arguments. -/
theorem abelianCofreeEvaluation_coherence
    [∀ (j k : I) (a : j ⟶ k), (D.abelianInverse a).Additive]
    (i : I) (A : D.abelianFibre i) :
    (∀ j : I, D.abelianCofreeTransition i A (𝟙 j) =
      (D.abelianInverseId j).hom.app (D.abelianCofreeFamily i A j)) ∧
    (∀ {j k l : I} (a : j ⟶ k) (b : k ⟶ l),
      (D.abelianInverseComp a b).hom.app (D.abelianCofreeFamily i A l) ≫
          D.abelianCofreeTransition i A (a ≫ b) =
        (D.abelianInverse a).map (D.abelianCofreeTransition i A b) ≫
          D.abelianCofreeTransition i A a) ∧
    (∀ (X : D.abelianFibre i) (h : X ⟶ A),
      (D.abelianAdjunction (𝟙 i)).homEquiv X A
          ((D.abelianInverseId i).hom.app X ≫ h) ≫
        (D.abelianDirectId i).hom.app A = h) ∧
    (∀ (j : I) (a : i ⟶ j),
      (D.abelianAdjunction a).homEquiv (D.abelianCofreeFamily i A j) A
          (D.abelianCofreeTransition i A a ≫
            Pi.π (fun t : i ⟶ i ↦ (D.abelianDirect t).obj A) (𝟙 i) ≫
              (D.abelianDirectId i).hom.app A) =
        Pi.π (fun t : i ⟶ j ↦ (D.abelianDirect t).obj A) a) ∧
    (∀ (X : D.AbelianSystem) (h : X.obj i ⟶ A) {j k : I} (c : k ⟶ j),
      (D.abelianInverse c).map (D.abelianCofreeExtension i X A h j) ≫
          D.abelianCofreeTransition i A c =
        X.transition c ≫ D.abelianCofreeExtension i X A h k) := by sorry

end CategoryTheory.CoherentSitePseudofunctor
