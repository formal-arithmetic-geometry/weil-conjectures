module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# A global function separating finitely many points from another point

Source: Stacks Project, Properties, Tag 0F20, proof of
`lemma-quasi-affine-invertible-nonvanishing-section`, affine scalar construction
(blueprint: lem-sfb-affine-finite-point-scalar-separation).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- On an affine scheme, a finite set can be separated by a global function from a point
outside the closure of each of its points. Values are germs followed by the residue map.

Source: Stacks Project, Properties, Tag 0F20, proof of
`lemma-quasi-affine-invertible-nonvanishing-section`, affine scalar construction
(blueprint: lem-sfb-affine-finite-point-scalar-separation).

Proof:
1. Put `A = Γ(X, ⊤)`. By `lem-weil-pbc-affine-open-spec-points` with the top open,
   identify `X` with `Spec A`, and let `p_x` and `q` correspond to `x ∈ F` and `z`.
   This is a homeomorphism. By `lem-weil-pbc-spec-irreducible-closed-subsets-primes` (1),
   `z ∈ closure {x}` is equivalent to `q ∈ V(p_x)`, hence to `p_x ≤ q`.
   The hypothesis therefore gives `p_x ≰ q` for every `x ∈ F`.
2. Choose `a_x ∈ p_x` outside `q` for every `x ∈ F`, and take the finite product `f`.
   The empty product is `1`. For each `x ∈ F`, isolating its factor shows `f ∈ p_x`.
   Primality of `q` and induction on the number of factors give `f ∉ q`, including
   the empty case since `q` is proper.
3. By `lem-weil-pbc-affine-open-section-vanishing-prime` (a), membership in `p_x`
   means that the residue-field value of the germ of `f` at `x` is zero, while
   nonmembership in `q` means its value at `z` is nonzero. Thus `f` has the required values. -/
theorem exists_globalSection_zero_on_finite_ne_zero
    (X : Scheme.{u}) [IsAffine X] (F : Set X) (hF : F.Finite) (z : X)
    (hz : ∀ x ∈ F, z ∉ closure ({x} : Set X)) :
    ∃ f : Γ(X, ⊤), (∀ x ∈ F, X.Γevaluation x f = 0) ∧ X.Γevaluation z f ≠ 0 := by
  sorry

end AlgebraicGeometry.Scheme
