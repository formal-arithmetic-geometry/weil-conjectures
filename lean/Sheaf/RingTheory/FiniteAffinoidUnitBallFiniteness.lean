module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Finiteness on spectral unit balls of finite affinoid maps

Source: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, Section 6.4.1,
Corollaries 5--6; Conrad, Perfectoid Seminar, Lecture 12, after Example 12.2.5
(blueprint: lem-trf-finite-affinoid-unit-ball-finiteness).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RestrictedSeries

/-- The character supremum used to define the spectral unit ball. The supremum is over
continuous unital `K`-algebra homomorphisms, with the given norm topologies. For nonzero
strict affinoids over an algebraically closed complete field this is a finite real supremum.
Source: BGR, Section 6.2.1, and Section 6.4.1, Corollaries 5--6
(blueprint: lem-trf-finite-affinoid-unit-ball-finiteness). -/
noncomputable def characterSupremum
    (K : Type u) [NormedField K] (H : Type v) [NormedCommRing H] [Algebra K H]
    (h : H) : ℝ :=
  sSup {r : ℝ | ∃ χ : H →ₐ[K] K, Continuous χ ∧ r = ‖χ h‖}

/-- A finite affinoid map with reduced target is finite on spectral unit balls.
Finite generation is written as an explicit finite family and its coefficient expansions;
the coefficient action is multiplication by the image under `φ`.

Source: BGR, Section 6.4.1, Corollaries 5--6; Conrad, Perfectoid Seminar,
Lecture 12, paragraph after Example 12.2.5
(blueprint: lem-trf-finite-affinoid-unit-ball-finiteness).

Proof plan (BGR, Theorem 6.4.1/3 and Corollary 5):
1. Identify the continuous-character supremum with the maximal-residue-field supremum
using algebraic closedness and the bounds of
`lem-trf-affinoid-supremum-seminorm-calculus`. Obtain the ultrametric, product and scalar
inequalities, and hence the subring structures of the unit balls.
2. Use `lem-trf-tate-normalization-lift` to find a finite injective Tate algebra map
`T → A`. Composing with `φ` makes `B` finite over `T`; the action is Gauss-contractive.
3. By `lem-trf-affinoid-minimal-component-norm`, embed reduced `B` isometrically in the
finite product of its nonzero minimal-prime domain quotients. Their spectral functions
are norms by `lem-trf-affinoid-spectral-banach-norm`.
4. Normalize `T` modulo its kernel on each component. Apply
`lem-trf-tate-fraction-orthogonal-spectral-norm` to the resulting finite injective Tate
map: the component fraction field has an orthogonal basis for its extended spectral norm.
5. The minimal-polynomial norm formula puts all nonzero norm values in the value group
of `K`: Gauss norms are attained coefficients and algebraic closedness supplies roots.
Clear the finitely many denominators of component generators in the orthogonal basis.
Rescale its vectors by scalars in `K` to enclose the component in an isometric free Tate
lattice with unit-weight maximum norm.
6. Apply `lem-trf-tate-submodule-norm-controlled-generators` to the inverse image of the
component in that lattice. Its normalized generators represent every component element
with coefficients bounded by its spectral norm.
7. Transport the component coefficient expansions to the common `T` and concatenate
in the finite product. The resulting free-module map is contractive, and every element
of the product has a preimage of exactly its norm.
8. Apply `lem-trf-tate-submodule-norm-controlled-generators` again to the inverse image
of `B` under this map. The images of the normalized generators give finitely many
`yᵢ` in `B` of spectral norm at most one. Every `b` has an expansion with Tate
coefficients of Gauss norm at most its spectral norm.
9. For `b` in the unit ball, these coefficients map to the unit ball of `A`.
Thus the `yᵢ` generate the unit ball over that of `A` through `φ`. Conversely every such
combination is in the ball by contraction and the ultrametric and product inequalities.
Neither reducedness of `A` nor injectivity of `φ` is needed. -/
theorem finite_affinoid_unit_ball_finiteness
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [IsAlgClosed K]
    (A : Type v) [NormedCommRing A] [Nontrivial A] [Algebra K A]
    (B : Type w) [NormedCommRing B] [Nontrivial B] [Algebra K B] [IsReduced B]
    (_hA : IsAffinoidQuotient K A (algebraMap K A))
    (_hB : IsAffinoidQuotient K B (algebraMap K B))
    (φ : A →ₐ[K] B) (_hφ : Continuous φ)
    (_hcontract : ∀ a : A, characterSupremum K B (φ a) ≤ characterSupremum K A a)
    (_hfinite : φ.Finite) :
    ∃ (n : ℕ) (y : Fin n → B),
      (∀ i : Fin n, characterSupremum K B (y i) ≤ 1) ∧
      ∀ b : B, characterSupremum K B b ≤ 1 →
        ∃ a : Fin n → A, (∀ i : Fin n, characterSupremum K A (a i) ≤ 1) ∧
          b = ∑ i : Fin n, φ (a i) * y i := by
  sorry

end RestrictedSeries
