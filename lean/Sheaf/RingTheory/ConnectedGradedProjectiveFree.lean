module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous bases of finite projective modules over connected graded algebras

Source: Stacks Project, Algebra, Tags 0EKB and 05CF, with the homogeneous-basis
consequence extracted in the DAG (blueprint: lem-sfb-connected-graded-projective-free).
-/

@[expose] public section

universe u v w

namespace GradedAlgebra

/-- A finite projective integer-graded module over a connected nonnegatively graded
algebra over a field has a finite homogeneous basis.

Source: Stacks Project, Algebra, Tag 0EKB, parts (1) and (4), and Tag 05CF,
projective lifting (blueprint: lem-sfb-connected-graded-projective-free).

The finite set is `Fin r`, the basis vectors are `b i`, and their degrees are `e i`.
The final equivalence spells out the shifted graded isomorphism without introducing
another shift construction: `b.repr.symm` sends a finitely supported coefficient family
`c` to its linear combination of the basis vectors. In degree `j`, its `i`-th coefficient
belongs to `A_(j-e i)`; that component is zero for `j-e i < 0`. Thus the source is exactly
`⨁ i, A(-e i)`, with the convention `A(d)_j = A_(j+d)`. The equivalence specifies both
forward and inverse degree preservation. No nonzero, Noetherian, or finite-type condition
is imposed, and `r = 0` is permitted.

Proof:
1. If `P = 0`, use the empty basis. Otherwise let `I = A_+`. Replace a finite ungraded
   generating family by its finitely many homogeneous components. Their images span
   `P/IP` over `k`, since coefficients act there through their degree-zero components.
   Retain successively independent images to obtain a homogeneous residue basis, and
   take the corresponding homogeneous representatives `p_i` of degrees `e_i`.
2. Form `F = ⨁ i, A(-e_i)` and the degree-preserving map `q` taking its standard basis
   to the `p_i`. Clause (1) of lem-sfb-graded-nakayama-connected makes `q` surjective.
   Its residue map is an isomorphism. In particular `q⁻¹(IP) = IF`: independence of
   the residue basis forces each degree-zero coefficient in such a preimage to vanish.
3. Projectivity, def-weil-pbc-projective-module, gives an ungraded section `s` of `q`.
   Put `K = ker q` and `h = 1-sq`. Then `h` takes values in `K` and is the identity on
   `K`. Applying `h` to the finite standard basis of `F` gives finite generators of `K`.
   The kernel is internally graded: uniqueness of homogeneous decomposition in `P`
   forces every homogeneous component of an element of `K` to remain in `K`.
4. Step 2 implies `K ⊆ IF`. Applying `h` to an expression in `IF` proves `K ⊆ IK`;
   the opposite inclusion is automatic. Clause (2) of lem-sfb-graded-nakayama-connected
   applied to the finite graded module `K` gives `K = 0`.
5. Thus `q` is an isomorphism and the `p_i` form the required basis. If `q(f)` is
   homogeneous of degree `j`, decompose `f` into homogeneous parts. Internalness in `P`
   and injectivity of `q` kill all parts of degrees other than `j`. Hence its inverse
   also preserves degrees, yielding precisely the displayed coefficient equivalence. -/
theorem exists_homogeneous_basis_of_finite_projective
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    (hzero : 𝒜 0 = Submodule.span k ({1} : Set A))
    {P : Type w} [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (ℙ : ℤ → AddSubgroup P) (hℙ : DirectSum.IsInternal ℙ)
    (hsmul : ∀ (a : ℕ) (j : ℤ) (x : A) (p : P),
      x ∈ 𝒜 a → p ∈ ℙ j → x • p ∈ ℙ ((a : ℤ) + j)) :
    ∃ (r : ℕ) (e : Fin r → ℤ) (b : Module.Basis (Fin r) A P),
      (∀ i : Fin r, b i ∈ ℙ (e i)) ∧
      (∀ (j : ℤ) (c : Fin r →₀ A),
        b.repr.symm c ∈ ℙ j ↔
          ∀ i : Fin r, if 0 ≤ j - e i then c i ∈ 𝒜 (j - e i).toNat else c i = 0) := by
  sorry

end GradedAlgebra
