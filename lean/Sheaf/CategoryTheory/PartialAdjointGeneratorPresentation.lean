module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Generator presentations for a partially defined adjoint

Source: Stacks Project, Homology, Tag 0793, `lemma-partially-defined-adjoint`,
first paragraph and the exact presentation in the second paragraph, with an additive functor
(blueprint: lem-trf-partial-adjoint-generator-presentation).
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

open CategoryTheory.Limits

namespace CategoryTheory

/-- Generator presentations and their transported relations for supplied partial adjoints.

Source: Stacks Project, Homology, Tag 0793, `lemma-partially-defined-adjoint`, first paragraph
and the exact presentation in the second paragraph; additive specialization
(blueprint: lem-trf-partial-adjoint-generator-presentation).

Proof: (1) Apply naturality to the identity of each `L p` to express every value of `θ`
as composition with `θ p (L p) (𝟙 (L p))`. Additivity of `R` gives `R.map 0 = 0`, hence
`θ p X 0 = 0` (`def-weil-pbc-additive-functor`).
(2) Cover `Y` by an epimorphism `q` from `p₁`, take a kernel `k : K ⟶ p₁`, and cover
`K` by an epimorphism `r` from `p₂` (`def-sp-abelian`). Then `(r ≫ k) ≫ q = 0`.
(3) If `(r ≫ k) ≫ h = 0`, cancel the epimorphism `r` to obtain `k ≫ h = 0`.
Since an epimorphism in an abelian category is the cokernel of its kernel, `h` factors
uniquely through `q`. Equivalently, normality writes `q` as a cokernel of some map `t`;
factor `t` through `k` and apply that cokernel property (`def-sp-abelian`).
(4) Take `D` to be the inverse image of `(r ≫ k) ≫ θ p₁ (L p₁) (𝟙 (L p₁))`
under `θ p₂ (L p₁)`. Bijectivity gives its equation and uniqueness. Naturality and
the formula in (1) give `θ p₂ X (D ≫ a) = (r ≫ k) ≫ θ p₁ X a`.
(5) The zero compatibility in (1) and injectivity of `θ p₂ X` identify the two zero
conditions, in both directions. -/
theorem partialAdjointGeneratorPresentation
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (R : A ⥤ B) [R.Additive]
    (P : Set B)
    (hcover : ∀ Y : B, ∃ p : P, ∃ q : p.1 ⟶ Y, Epi q)
    (L : P → A)
    (θ : ∀ (p : P) (X : A), (L p ⟶ X) ≃ (p.1 ⟶ R.obj X))
    (hθ : ∀ (p : P) (X X' : A) (a : L p ⟶ X) (u : X ⟶ X'),
      θ p X' (a ≫ u) = θ p X a ≫ R.map u) :
    (∀ (p : P) (X : A) (a : L p ⟶ X),
      θ p X a = θ p (L p) (𝟙 (L p)) ≫ R.map a ∧ θ p X 0 = 0) ∧
    ∀ Y : B, ∃ (p₁ p₂ : P) (q : p₁.1 ⟶ Y) (K : B)
      (k : K ⟶ p₁.1) (r : p₂.1 ⟶ K) (hk : k ≫ q = 0),
      Epi q ∧ Epi r ∧ Nonempty (IsLimit (KernelFork.ofι k hk)) ∧
      (r ≫ k) ≫ q = 0 ∧
      (∀ (Z : B) (h : p₁.1 ⟶ Z), (r ≫ k) ≫ h = 0 →
        ∃! b : Y ⟶ Z, q ≫ b = h) ∧
      ∃ D : L p₂ ⟶ L p₁,
        θ p₂ (L p₁) D = (r ≫ k) ≫ θ p₁ (L p₁) (𝟙 (L p₁)) ∧
        (∀ D' : L p₂ ⟶ L p₁,
          θ p₂ (L p₁) D' = (r ≫ k) ≫ θ p₁ (L p₁) (𝟙 (L p₁)) → D' = D) ∧
        ∀ (X : A) (a : L p₁ ⟶ X),
          θ p₂ X (D ≫ a) = (r ≫ k) ≫ θ p₁ X a ∧
          (D ≫ a = 0 ↔ (r ≫ k) ≫ θ p₁ X a = 0) := by
  sorry

end CategoryTheory
