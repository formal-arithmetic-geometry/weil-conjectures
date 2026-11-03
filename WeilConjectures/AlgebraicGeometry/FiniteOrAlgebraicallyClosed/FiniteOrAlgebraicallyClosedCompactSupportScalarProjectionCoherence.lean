/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteExceptionalTensor.FiniteExceptionalCoefficientTensor

/-!
# Compact-support scalar projection coherence

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, Proof (3), Tensor map
(blueprint: lem-sp-finite-or-algebraically-closed-compact-support-scalar-projection-coherence).

The statement uses the existing fixed-scalar presentation of the ordinary constant-ring
pro-etale derived categories and its recorded operations and canonical maps from
`AlgebraicGeometry.ProEtale.FiniteExceptionalTensor` (owner node
lem-pur-exceptional-coefficient-comparison): `D`, `ctf`, the scalar functor `scalar`
(the recorded `scalarExtensionFunctor` of det-sp-scalar-extension-functor transported along
the finite-coefficient equivalences), exact restriction `restrict`, compact support
`support` = Rp_* j_!, pullback `pull`, the Koszul `braiding`, the ordered projection map
`projection`, and the adjunction mates `scalarTensor`, `scalarUnit`, `scalarPull`
(= lambda_f⁻¹), `compactComparison` (= b) and `sigma`.  None of these is redefined here.
Those definitions involve no property of the base field, so they serve the finite or
algebraically closed base of this node.  The statement includes nonflat coefficient maps
and zero rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed

/-- The finite-or-algebraically-closed compact-support scalar projection statement.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, Proof (3), Tensor map
(blueprint: lem-sp-finite-or-algebraically-closed-compact-support-scalar-projection-coherence).

Proof steps (postponed):
(1) For each `R = A, B`, apply the finite-coefficient constructible-derived-origin theorem and
transport the finite-Tor interval to an etale origin.  The finite-coefficient pro-etale
projection theorem then makes the recorded proper/open projection map an isomorphism;
naturality of its counit transpose and the two tensor symmetries gives `projection` and its
naturality.
(2) The ordinary coefficient equivalence identifies the recorded scalar extension, its
restriction adjunction, the tensorator and its unit with the displayed constructions.  The
fixed pullback comparison is its normalized adjunction mate, so `scalarPull` and
`sigma = (lambda_f⁻¹ ⊗ 1) μ_X`.  The same normalization identifies the recorded direct-image
comparison `b`; its isomorphism applies to `M` and to `F_A K ⊗ M`, with constructibility and
finite-Tor stability supplied by the scalar-extension theorem.
(3) Apply the compact-support scalar-comparison coherence theorem to the same compactification
and substitute the symmetry-conjugated projection maps.  Naturality of `b` and the tensorator
coherence give exactly the displayed square.
(4) Its unitor and symmetry clauses give the final two equations; the derived braidings carry
the Koszul signs.  The constructions cover zero rings, empty schemes and nonflat coefficient
maps, and no additional flatness hypothesis is introduced.
-/
theorem finiteOrAlgebraicallyClosedCompactSupportScalarProjectionCoherence
    (k : Type u) [Field k] (p : ℕ) (hp : p.Prime) (hpk : ringChar k = p)
    (hscope : Finite k ∨ IsAlgClosed k) (ell : ℕ) (hell : ell.Prime) (hEll : ell ≠ p)
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, 1 ≤ n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (hB : ∃ n : ℕ, 1 ≤ n ∧ ∀ b : B, (ell ^ n) • b = 0)
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (c : Compactification f) [c.Z.Over (Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
    [QuasiCompact (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (K : D A Y) (L : D A Y) (M : D A X) (hK : ctf A Y K)
    (hL : ctf A Y L) (hM : ctf A X M) (aX : scalar φ X ⊣ restrict φ X)
    (aY : scalar φ Y ⊣ restrict φ Y) (U V : D A Y) :
    IsIso (projection A c K M) ∧
      IsIso (projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M)) ∧
      IsIso (compactComparison φ c aX aY M) ∧
      IsIso (compactComparison φ c aX aY ((pull A f).obj K ⊗ M)) ∧
      IsIso (scalarTensor φ Y aY K L) ∧
      IsIso (sigma φ f aX aY K M) ∧
      IsIso (scalarPull φ f aX aY K) ∧
      IsIso (scalarUnit φ Y aY) ∧
      (scalar φ Y).map (projection A c K M) ≫
          compactComparison φ c aX aY ((pull A f).obj K ⊗ M) ≫
          (support B c).map (sigma φ f aX aY K M) =
        scalarTensor φ Y aY K ((support A c).obj M) ≫
          (𝟙 ((scalar φ Y).obj K) ⊗ₘ compactComparison φ c aX aY M) ≫
          projection B c ((scalar φ Y).obj K) ((scalar φ X).obj M) ∧
      (∀ {K₁ K₂ : D A Y} {M₁ M₂ : D A X} (g : K₁ ⟶ K₂) (h : M₁ ⟶ M₂),
        (g ⊗ₘ (support A c).map h) ≫ projection A c K₂ M₂ =
          projection A c K₁ M₁ ≫ (support A c).map ((pull A f).map g ⊗ₘ h)) ∧
      (∀ {K₁ K₂ : D B Y} {M₁ M₂ : D B X} (g : K₁ ⟶ K₂) (h : M₁ ⟶ M₂),
        (g ⊗ₘ (support B c).map h) ≫ projection B c K₂ M₂ =
          projection B c K₁ M₁ ≫ (support B c).map ((pull B f).map g ⊗ₘ h)) ∧
      (∀ {U₁ U₂ V₁ V₂ : D A Y} (g : U₁ ⟶ U₂) (h : V₁ ⟶ V₂),
        (scalar φ Y).map (g ⊗ₘ h) ≫ scalarTensor φ Y aY U₂ V₂ =
          scalarTensor φ Y aY U₁ V₁ ≫
            ((scalar φ Y).map g ⊗ₘ (scalar φ Y).map h)) ∧
      (∀ {K₁ K₂ : D A Y} (g : K₁ ⟶ K₂),
        (scalar φ X).map ((pull A f).map g) ≫ scalarPull φ f aX aY K₂ =
          scalarPull φ f aX aY K₁ ≫ (pull B f).map ((scalar φ Y).map g)) ∧
      (∀ {M₁ M₂ : D A X} (h : M₁ ⟶ M₂),
        (scalar φ Y).map ((support A c).map h) ≫ compactComparison φ c aX aY M₂ =
          compactComparison φ c aX aY M₁ ≫ (support B c).map ((scalar φ X).map h)) ∧
      (∀ {K₁ K₂ : D A Y} {M₁ M₂ : D A X} (g : K₁ ⟶ K₂) (h : M₁ ⟶ M₂),
        sigma φ f aX aY K₁ M₁ ≫
            ((pull B f).map ((scalar φ Y).map g) ⊗ₘ (scalar φ X).map h) =
          (scalar φ X).map ((pull A f).map g ⊗ₘ h) ≫ sigma φ f aX aY K₂ M₂) ∧
      ((scalar φ Y).map (λ_ V).hom =
        scalarTensor φ Y aY (𝟙_ _) V ≫
          (scalarUnit φ Y aY ⊗ₘ 𝟙 ((scalar φ Y).obj V)) ≫
          (λ_ ((scalar φ Y).obj V)).hom) ∧
      ((scalar φ Y).map (braiding A Y U V).hom ≫ scalarTensor φ Y aY V U =
        scalarTensor φ Y aY U V ≫
          (braiding B Y ((scalar φ Y).obj U) ((scalar φ Y).obj V)).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed
