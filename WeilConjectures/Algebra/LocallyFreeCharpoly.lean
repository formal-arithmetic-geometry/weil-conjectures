/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.CharpolyLocallyFree

/-! # Characteristic polynomial of a finite locally free module of constant rank

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph
(blueprint: def-weil-pbc-charpoly-locally-free).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

/-- The characteristic polynomial of a finite locally free module of constant rank.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: def-weil-pbc-charpoly-locally-free).
The polynomial is chosen from `charpoly_locallyFree_exists_unique`, using scalar extensions
in the base ring's universe. Its characterization below holds in every universe. Only the
existence proof is postponed: the definition contains no missing data. -/
noncomputable def locallyFreeCharpoly {n r : ℕ} (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin r,
      ∃ _e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (φ : M →ₗ[A] M) : Polynomial A :=
  Classical.choose (charpoly_locallyFree_exists_unique.{u, v, u} f hgen hfree φ)

/-- Characterization, uniqueness, monic expansion, and the free case.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: def-weil-pbc-charpoly-locally-free).
Proof (step 1 of the node): apply `lem-weil-pbc-charpoly-locally-free-existence`, whose
hypotheses are exactly this cover and these local bases. Its chosen polynomial has the
characterizing property, the expansion, and the free-case identity. For a larger universe,
apply that lemma there too. Lift each original localization by `ULift` to the larger
universe, transport its local basis, and compare both polynomials there. The lift is a ring
isomorphism, so coefficientwise injectivity on the standard cover identifies them. For a
target ring in a smaller universe, lift it and its scalar-extended basis in the same way;
transport the matrix equality back along the ring isomorphism. The matrix expression is
precisely the determinant of T times identity minus the scalar-extended endomorphism,
independent of the basis, by `def-weil-endomorphism-determinant`. The free case is scalar
extension by the identity ring map, using `def-weil-module-base-change`. -/
theorem locallyFreeCharpoly_spec {n r : ℕ} (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin r,
      ∃ _e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (φ : M →ₗ[A] M) :
    let P : Polynomial A → Prop := fun χ ↦
      ∀ (A' : Type (max u w)) [CommRing A'] (ρ : A →+* A'),
        letI : Algebra A A' := RingHom.toAlgebra ρ;
        ∀ e : Module.Basis (Fin n) A' (A' ⊗[A] M),
          χ.map ρ = (LinearMap.toMatrix e e (φ.baseChange A')).charpoly;
    (P (locallyFreeCharpoly f hgen hfree φ) ∧
      ∀ χ : Polynomial A, P χ → χ = locallyFreeCharpoly f hgen hfree φ) ∧
    (∃ c : Fin n → A,
      locallyFreeCharpoly f hgen hfree φ = Polynomial.X ^ n +
        ∑ k : Fin n, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)) ∧
    (∀ e : Module.Basis (Fin n) A M,
      locallyFreeCharpoly f hgen hfree φ = (LinearMap.toMatrix e e φ).charpoly) := by
  sorry

/-- Over a nonzero ring the module determines its constant rank.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: def-weil-pbc-charpoly-locally-free).
Proof (step 3 of the node): choose a maximal ideal and an element of each cover outside it.
The localization at their product is nonzero and has both bases after further localization
(`def-weil-pbc-module-localization-away`, `def-weil-ring-localization-away`). Tensor with a
residue field (`def-weil-module-base-change`) and compare the two finite basis sizes. -/
theorem locallyFree_constantRank_eq [Nontrivial A] {n m r s : ℕ}
    (f : Fin r → A) (g : Fin s → A)
    (hfgen : Ideal.span (Set.range f) = ⊤)
    (hffree : ∀ i : Fin r,
      ∃ _e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (hggen : Ideal.span (Set.range g) = ⊤)
    (hgfree : ∀ j : Fin s,
      ∃ _e : Module.Basis (Fin m) (Localization.Away (g j))
        (LocalizedModule.Away (g j) M), True) : n = m := by
  sorry

/-- Independence of both the trivializing cover and the stated constant rank.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: def-weil-pbc-charpoly-locally-free).
Proof (steps 2 and 3 of the node): at equal ranks the characterization does not mention the
cover, so uniqueness in `lem-weil-pbc-charpoly-locally-free-existence` identifies the choices.
For different ranks, if A is zero its polynomial ring is zero, hence the choices are equal.
Otherwise choose a maximal ideal, then cover elements f i and g j outside it. Localize both
bases further at their product, using `def-weil-pbc-module-localization-away` and
`def-weil-ring-localization-away`. This common localization is nonzero. Reduce at a maximal
ideal of it and use `def-weil-module-base-change`: the two vector-space bases have sizes n
and m, so invariant basis number gives n = m. Apply the equal-rank argument. -/
theorem locallyFreeCharpoly_eq {n m r s : ℕ} (f : Fin r → A) (g : Fin s → A)
    (hfgen : Ideal.span (Set.range f) = ⊤)
    (hffree : ∀ i : Fin r,
      ∃ _e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (hggen : Ideal.span (Set.range g) = ⊤)
    (hgfree : ∀ j : Fin s,
      ∃ _e : Module.Basis (Fin m) (Localization.Away (g j))
        (LocalizedModule.Away (g j) M), True)
    (φ : M →ₗ[A] M) :
    locallyFreeCharpoly f hfgen hffree φ = locallyFreeCharpoly g hggen hgfree φ := by
  classical
  by_cases hA : Nontrivial A
  · have := hA
    have hnm := locallyFree_constantRank_eq (M := M) f g hfgen hffree hggen hgfree
    subst m
    exact (((locallyFreeCharpoly_spec.{_,_,0} (M := M) f hfgen hffree φ).1.2
      _ (locallyFreeCharpoly_spec.{_,_,0} (M := M) g hggen hgfree φ).1.1).symm)
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    exact Subsingleton.elim _ _

end Algebra
