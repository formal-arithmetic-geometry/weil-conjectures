## Worker report

The module `Sheaf.RingTheory.MaximalAdicGradedLengthBridge` states
`IsLocalRing.maximalAdicGradedLengthBridge` with one `sorry`. It also provides
`IsLocalRing.maximalAdicResidueAlgebra`, a real instance whose entire data is the
existing `Ideal.associatedGradedAlgebra (maximalIdeal R)`. This only exposes its
coefficient type through Mathlib's `IsLocalRing.ResidueField` wrapper; it does not
choose a coefficient field or another algebra action.

Hypotheses and clauses, in order:

- `R : Type u`, `[CommRing R]`, `[IsNoetherianRing R]`, `[IsLocalRing R]` render
  the nonzero commutative Noetherian local ring. `IsLocalRing` extends
  `Nontrivial R`, so a separate nontriviality binder is redundant and causes
  an overlapping-instance warning. No zero ring is admitted.
- `ResidueField R` is Mathlib's actual definition `R ⧸ maximalIdeal R`. The
  associated graded ring and its quotients are exactly `Ideal.associatedGraded`
  and `Ideal.associatedGradedPiece` from the dependency module.
- The first existential introduces `𝒜 : ℕ → Submodule (ResidueField R) S` and
  requires the underlying set of every `𝒜 i` to equal the range of the existing
  `DirectSum.of ... i`. These are precisely the homogeneous summands in the
  node, with the canonical scalar action. Equality of underlying sets uniquely
  determines each submodule; there is no arbitrary family of subspaces.
- The subsequent `∃ (_grading : GradedAlgebra 𝒜)` supplies the internal direct-sum
  decomposition and graded multiplication, and `GradedAlgebra.IsStandard
  (k := ResidueField R) 𝒜` is the recorded standard-graded notion. Together with
  the existing degree-zero algebra inclusion this renders the standard graded
  k-algebra clause, including degree zero and the multiplication laws.
- `∀ (t : ℕ) (y : Fin t → ↥(maximalIdeal R ^ 1)), Ideal.span (Set.range
  (fun j ↦ (y j).val)) = maximalIdeal R → ...` quantifies over every finite
  generating list of the maximal ideal. Its first-power subtype is the ideal
  itself since `pow_one`; this avoids any additional membership assumptions.
  Repetitions, zero entries, and the empty list are allowed.
- `Algebra.adjoin ... (Set.range (fun j ↦ DirectSum.of ... 1
  (Submodule.Quotient.mk (y j)))) = ⊤` states that their degree-one classes
  generate S as a k-algebra.
- The following `∀ i`, equality of `Submodule.span` with `𝒜 i`, states that
  their degree-i monomials span that piece. Monomials are products indexed by
  `j : Fin i`, with every map `f : Fin i → Fin t`, so repetitions of generators
  are allowed. These products give exactly all monomials of total degree i.
- `∀ i, Module.Finite (ResidueField R) (𝒜 i) ∧ Module.length R
  (Ideal.associatedGradedPiece ... i) = (Module.finrank ... (𝒜 i) : ℕ∞)` renders
  finite dimensionality and equality of composition length to dimension. Length
  is taken on the original quotient module, whose R-action is already provided;
  dimension is taken on its identical embedded homogeneous summand. The range
  equality and injectivity of `DirectSum.of` identify these two presentations.
- `∀ n : ℕ, 1 ≤ n → ...` renders every integer n at least one.
  `IsFiniteLength R (R ⧸ maximalIdeal R ^ n)` gives finite composition length;
  the next equality is exactly the sum over `Finset.range n`, coerced from ℕ to
  ℕ∞; the last conjunct is `1 ≤ Module.length R (R ⧸ maximalIdeal R ^ n)`.
- `∀ P : Polynomial ℚ`, with `∃ a, ∀ i, a ≤ i → (Module.finrank ... : ℚ) =
  P.eval (i : ℚ)`, is the eventual polynomial hypothesis on the graded dimensions.
  There is no nonzero assumption on P.
- `∃ Q : Polynomial ℚ, Q ≠ 0 ∧ 0 < Q.leadingCoeff ∧ ∃ N : ℕ, 1 ≤ N ∧ ...`
  renders all the claimed output conditions. The final equality evaluates Q at
  every n at least N and identifies it with the rational cast of the actual
  quotient length. `toNat` is lossless here by the finite-length clause, since
  N is at least one. Natural-number binders cover exactly the nonnegative and
  positive integer indices used in the node.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with its ideal-finite-
  generation interpretation (`isNoetherianRing_iff_ideal_fg`).
- `WeilConjectures.RingTheory.AssociatedGradedRing`:
  `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`, and
  `Ideal.associatedGradedAlgebra`. This also supplies the recorded ring-structure
  proof dependency, including its homogeneous product and scalar formulas.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`:
  `GradedAlgebra.IsStandard`. Read its complete signature and docstring:
  finite generation in degree one and generation as an algebra; its
  `grade_zero_eq_one` identifies degree zero with the image of k.
- `Mathlib.RingTheory.Length`: `Module.length`, `IsFiniteLength`; the same module
  provides the proof dependency `Module.length_eq_add_of_exact`.
- `Mathlib.NumberTheory.Bernoulli` (proof import): `sum_range_pow`, the recorded
  match for `lem-trf-rational-power-sum-formula`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: residue field, maximal ideal,
  and the inherited nontriviality of a local ring. Polynomial evaluation uses
  `Mathlib.Algebra.Polynomial.Eval.Defs`.

The source was read locally: `literature/stacks-project/algebra.tex`, the
Noetherian-local-rings section's power-filtration identity immediately before
Tag 00K8, proposition-hilbert-function-polynomial itself, Tag 00IY
lemma-dimension-is-length, and Tag 00JZ lemma-numerical-polynomial. The proof
in the declaration docstring follows all five steps of the DAG, including the
explicit rational power sums and the elementary leading-term positivity bound.

Edge cases checked before finalizing: a field (m = 0), the empty generating list,
repeated/zero generators, i = 0 (one empty monomial, giving k), i > 0 with t = 0
(no monomials, giving the zero subspace), n = 1 (length and dimension both one),
n = 0 (outside the asserted positivity range, available as the induction base),
P = 0 (eventually constant positive Q), constant nonzero P, and arbitrary ring
characteristic. The universe u is unrestricted. No statement correction or
STATEMENT-DISPUTED issue was found.

Searches performed with the prescribed msearch.py wrapper:

- leanfinder: "associated graded algebra of the maximal ideal of a Noetherian
  local ring is standard graded and quotient lengths are cumulative dimensions".
  Eight hits, including Krull-dimension inequalities for quotient rings; none
  gives this graded algebra, monomial spanning, and cumulative-polynomial bridge.
- loogle: `"associatedGraded", "length"`. Zero hits.
- grep, Mathlib/RingTheory:
  `associatedGraded|associated_graded|length.*finrank|finrank.*length`. Seven hits,
  including `Module.length_eq_finrank` for vector spaces and ramification formulas;
  none states the complete node.
- leansearch: "The Hilbert Samuel function is the sum of dimensions of the
  associated graded pieces". Eight hits, including `Polynomial.hilbertPoly`
  and generic `GradedAlgebra`; none is an exact match.
- rg on `lean/WeilConjectures` and `lean/Sheaf`:
  `associatedGraded|associated_graded|graded.*[Ll]ength|[Ll]ength.*graded`, followed
  by `length.*finrank|finrank.*length|[Mm]aximal.*[Aa]dic.*[Ll]ength|[Hh]ilbert.*[Ss]amuel.*[Pp]olynomial`.
  Read the associated-graded construction, `HilbertSamuelGrowthDimension`, and
  `SimpleResidueExtensionHilbertComparison`. The latter two respectively give
  a different eventual dimension theorem and consume this bridge. The existing
  `Hironaka.adicGrade` helper is in a downstream node, whose proof dependency
  `lem-trf-simple-residue-extension-hilbert-comparison` cites this item; it cannot
  be imported here without a DAG dependency cycle. No duplicate helper is defined:
  the theorem specifies the homogeneous subspaces directly by the primitive
  summand ranges from the recorded associated-graded dependency.
- rg for the item id in `lean/WeilConjectures`: no match. rg for
  `maximalAdicGradedLengthBridge` in both source roots and the upstream name index:
  no existing declaration.

## Second reading by Q63

Independent reading supplied by the maintainer's stage-2 reviewer (the group's own
section was a self-reading by the first worker, which H11 does not accept). Node,
Stacks algebra.tex 00K8 (proposition-hilbert-function-polynomial and the
power-filtration identity before it), 00IY, 00IV, 00JZ, and the dependency modules
`WeilConjectures.RingTheory.AssociatedGradedRing` and
`WeilConjectures.RingTheory.GradedAlgebra.Standard` were read against the Lean.

1. (R, m) nonzero commutative Noetherian local: `R : Type u`, `[CommRing R]`,
   `[IsNoetherianRing R]`, `[IsLocalRing R]` (IsLocalRing extends Nontrivial).
   Nothing stronger; universe free. Correct.
2. k = R/m with the degree-zero k-algebra structure: `ResidueField R`
   (Mathlib `def` = `R ⧸ maximalIdeal R`) and the helper instance
   `maximalAdicResidueAlgebra`, whose data is literally
   `Ideal.associatedGradedAlgebra (maximalIdeal R)` (ι₀ from the dependency).
   Real data, not hollow. Correct.
3. S_i: `∃ 𝒜`, pinned by `(𝒜 i : Set S) = Set.range (DirectSum.of _ i)`; a
   submodule is determined by its carrier, so 𝒜 is the canonical summand family.
   Correct.
4. S standard graded: `∃ _ : GradedAlgebra 𝒜, GradedAlgebra.IsStandard
   (k := ResidueField R) 𝒜`; a conclusion, and the decomposition is a
   subsingleton for fixed 𝒜. `grade_zero_eq_one` gives S₀ = k. Correct.
5. Every finite generating list: `∀ t (y : Fin t → ↥(m ^ 1)), Ideal.span (range
   (val ∘ y)) = m → adjoin k {ι₁ ȳ_j} = ⊤ ∧ ∀ i, span k {∏_{j<i} ι₁ ȳ_{f j} | f :
   Fin i → Fin t} = 𝒜 i`. All degree-i monomials, repetitions allowed. Correct.
6. `Module.Finite k (𝒜 i)` and `Module.length R (associatedGradedPiece m i) =
   finrank k (𝒜 i)`. Correct.
7. ∀ n ≥ 1: `IsFiniteLength R (R ⧸ m^n)`, length = Σ_{i<n} finrank (in ℕ∞),
   `1 ≤ length`. Correct.
8. ∀ P : ℚ[X], eventual equality d_i = P(i) → ∃ Q ≠ 0, 0 < leadingCoeff Q,
   ∃ N ≥ 1, ∀ n ≥ N, (length).toNat = Q(n); `toNat` is lossless by clause 7.
   P = 0 allowed. Correct.

Edge cases: R a field (m = 0, t = 0: i = 0 gives the empty monomial 1 spanning
k, i > 0 gives ⊥ = 0); repeated/zero generators; n = 1 (H = 1); P = 0 (constant
positive Q, e.g. k[ε]/ε² with Q = 2, N ≥ 2); any characteristic.

One definition per notion: the homogeneous-subgroup family
`Ideal.associatedGradedGrading` (GradedNormalizationFractionMap.lean) and the
same residue-field instance `IsLocalRing.associatedGradedAlgebra`
(SmoothLocalTangentConeExtension.lean) exist, but both are helpers of theorem
nodes (lem-sfb-graded-normalization-fraction-map,
lem-trf-smooth-local-tangent-cone-extension), not definition nodes, so the item
cannot cite them; it inlines the summand ranges, and its instance is
definitionally the same `Ideal.associatedGradedAlgebra`, so importers of both
see no diamond. No Module diamond: the pieces carry no `ResidueField R`-module
instance, so `Algebra.toModule` is the only `Module (ResidueField R) S`.

Docstrings carry source places and the blueprint id; the theorem docstring has
the node's five proof steps; body `sorry` only. No change to the Lean or node.
