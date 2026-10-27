## Worker report

The delivery states `Ideal.bennett_normal_flat_numerical_criterion` in
`Sheaf.RingTheory.BennettNormalFlatNumericalCriterion`. Its sole proof is `sorry`.
There are no new definitions, helper declarations, new nodes, dependency repairs,
or changes to the natural-language statement or its dependencies. The node copy
changes only `lean`. The declaration docstring includes all thirteen proof steps
from the accepted split, including their cited supporting nodes.

Source read: [Cossart--Jannsen--Saito, March 12, 2009 preprint](https://epub.uni-regensburg.de/13766/1/MP32.pdf),
Theorem 2.3(1) iff (2), printed p.29, with Definition 2.1 on p.28 and the inclusive
summation convention in Definition 1.11/Remark 1.12 on pp.12--13. Its graded-piece
Hilbert function becomes the quotient-length convention by one summation, which
commutes with the dimension-fold summation. The extra geometric restriction on
centres in Definition 2.1 is not imposed on this raw algebraic criterion: the
accepted DAG explicitly allows I=0 and supplies an agent-written proof covering
it. ILO VIII 2.3.13 is motivation only. No new appeal to Bennett is used as a proof.
The local node's accepted proof, not a changed route, is carried into the docstring.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node clause | Lean rendering |
| --- | --- |
| F is a field | `{F : Type u} [Field F]` |
| R is a commutative F-algebra | `{R : Type v} [CommRing R] [Algebra F R]` |
| R is nonzero and local, with maximal ideal m | `[IsLocalRing R]`; this class extends `Nontrivial R`, and m is `IsLocalRing.maximalIdeal R` |
| R is reduced | `[IsReduced R]` |
| R is Noetherian | `[IsNoetherianRing R]` |
| R is essentially of finite type over F | `[Algebra.EssFiniteType F R]`, Mathlib's localization-of-finite-type notion |
| I is a prime ideal contained in m | `(I : Ideal R) [I.IsPrime] (hI : I ≤ IsLocalRing.maximalIdeal R)` |
| A = R/I is regular local | `[IsRegularLocalRing (R ⧸ I)]` |
| d = dim A | `(d : ℕ)` and `(hd : ringKrullDim (R ⧸ I) = (d : WithBot ℕ∞))` |
| R_I is localization at I | `Localization.AtPrime I` with its existing local ring instance |
| The maximal ideal of R_I is IR_I | `IsLocalRing.maximalIdeal (Localization.AtPrime I)`; `IsLocalization.AtPrime.map_eq_maximalIdeal` identifies this with the mapped ideal I |
| h_R(n) = length_R(R/m^(n+1)) for every n ≥ 0 | `fun n : ℕ ↦ Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))` |
| h_(R_I)(n) = length_(R_I)(R_I/(IR_I)^(n+1)) | The right-hand lambda uses `Module.length (Localization.AtPrime I)` and the quotient by the `(n + 1)`st power of its maximal ideal |
| Lambda f(n) = sum from j=0 through n of f(j) | The inline function `fun (f : ℕ → ℕ∞) (n : ℕ) ↦ ∑ j ∈ Finset.range (n + 1), f j` |
| Lambda iterated d times | `(...^[d])`, Mathlib's `Function.iterate`, including d=0 |
| gr_I R is the direct sum of I^j/I^(j+1), with canonical A-action | Existing `Ideal.associatedGraded I` and `Ideal.associatedGradedAlgebra I`, from the recorded upstream module |
| Flatness over A means tensoring injections preserves injectivity | `Module.Flat (R ⧸ I) (associatedGraded I)`; the recorded flat-module declaration has the arbitrary-module tensor-injectivity characterization |
| Flat iff h_R = Lambda^d h_(R_I) | The outer `↔` and equality of functions on `ℕ`, with no eventual-equality or polynomial replacement |
| I=0 is allowed | No hypothesis `I ≠ ⊥` or positive-height/positive-dimension condition |

The named d is a dimension parameter, not an additional finiteness assumption:
`IsRegularLocalRing.spanFinrank_maximalIdeal` identifies the dimension with the
natural spanFinrank of the maximal ideal. Therefore every ring covered by the
node supplies such d and hd. Universes u (field) and v (ring) are independent.
No finite-dimensional-field, perfectness, separability, equidimensionality,
completeness, or F-linear coefficient-section assumption has been introduced.

The inline summation is an expression, not a second declared definition.
`AlgebraicGeometry.HilbertSamuel.summation` in the project acts on `ℕ → ℕ` and
`localFunction` on scheme stalks, whereas this statement uses arbitrary local rings
and the exact `Module.length : ℕ∞` throughout. Inlining the finite sum preserves
that codomain without truncating infinite lengths or introducing a duplicate API.
The hypotheses ensure all these quotient lengths are finite; no `toNat` is used.

Statement dependencies, with their source signatures and docstrings read:

- `def-weil-pbc-essentially-finite-type-algebra`: `Algebra.EssFiniteType` in
  `Mathlib.RingTheory.EssentialFiniteness` (class and its localization docstring).
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs` (all ideals finitely generated).
- `def-weil-regular-scheme`: the ring clause supplied by its `mathlib_match`,
  `IsRegularLocalRing` in `Mathlib.RingTheory.RegularLocalRing.Defs`. Its recorded
  `AlgebraicGeometry.IsRegularScheme` is the scheme clause, irrelevant to this ring
  statement; the recorded ring match is used directly, without a private copy.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim` in
  `Mathlib.RingTheory.KrullDimension.Basic`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, including the local instance and
  the maximal-ideal identification.
- `def-weil-pbc-module-length`: `Module.length` in `Mathlib.RingTheory.Length`.
- `def-weil-pbc-associated-graded-ring`: `Ideal.associatedGraded`, its pieces, ring
  structure, and canonical quotient-algebra structure in
  `WeilConjectures.RingTheory.AssociatedGradedRing`.
- `def-weil-pbc-flat-ring-map`: its recorded module clause `Module.Flat` in
  `Mathlib.RingTheory.Flat.Basic`, rather than a newly defined predicate.

Proof dependencies are plain imports. In the node's order, their declarations are:
`IsRegularLocalRing.isDomain` (upstream RegularLocalRing.Defs), `Submodule.FG.of_le`
(Mathlib Noetherian.Basic), `LocalizedModule.map_exact` (LocalizedModule.Exact),
`IsLocalRing.map_mkQ_eq_top` (LocalRing.Module), `Module.length_eq_add_of_exact`
(Length, already public), `AdicCompletion.isNoetherianRing_and_isAdicComplete_of_quotient`
(upstream AdicCompletionNoetherianOfQuotient), the completion local-ring/residue
instances (Mathlib AdicCompletion.LocalRing), `AdicCompletion.pow_smul_top_eq_ker_eval`
(Completeness), `AdicCompletion.isRegularLocalRing_iff` (upstream
CompletionRegularLocal), `RingTheory.completion_dimension_eq` (upstream
CompletionDimensionEquality), `AdicCompletion.exists_local_completion_quotient`
(upstream LocalCompletionQuotient), `AdicCompletion.map_injective/map_exact/map_surjective`
(Mathlib Exactness), `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`
(Mathlib AsTensorProduct), `AdicCompletion.isAdicComplete` (Completeness, shared import),
`IsLocalRing.exists_coefficient_subring` (upstream ExistsCoefficientSubring),
`IsLocalRing.exists_ringEquiv_regular_complete_coefficients`
(Sheaf.RingTheory.RegularCompleteCoefficientCoordinates),
`MvPowerSeries.exists_unique_adic_evaluation` (upstream PowerSeriesAdicEvaluation),
and `Module.free_of_flat_of_isLocalRing` (Mathlib LocalRing.Module, shared import).
No proof dependency import was omitted for a cycle.

Edge cases checked mathematically before writing:

- At n=0, both quotient lengths are 1, and inclusive summation preserves the value
  at zero. `Finset.range (n+1)` includes precisely 0 through n.
- For I=m, A is the residue field, d=0, and R_m is canonically R. Iteration zero is
  the identity; the equality is the full length sequence with itself. The graded
  ring is a vector space over A and hence flat.
- For I=0 (when prime), the regular quotient is R, R_I is its fraction field, and
  its quotient-length sequence is constant 1. The regular local length sequence
  is the dimension-fold summation of 1. No case is excluded by a nonzero-centre
  hypothesis. The field case has d=0 as well.
- A singular reduced example is R=F[x,y]_(x,y)/(xy), I=(x). Here A=F[y]_(y),
  d=1, and R_I is a field. The target sum is n+1 whereas h_R(n)=2n+1; at n=1
  it is 2 versus 3. The degree-one conormal piece has nonzero y-torsion, so the
  flat side also fails. The statement does not accidentally assert automatic flatness.
- Arbitrary positive characteristic and inseparable residue extensions are kept.
  The copied proof obtains a ring section after completion, without asserting
  F-linearity. The zero ring is excluded exactly by the original nonzero/local
  hypothesis, implemented by `IsLocalRing`'s `Nontrivial` parent.

Searches actually run with msearch.py, group Q18 and this item, on 2026-10-24:

- LeanFinder: `Bennett numerical criterion: associated graded algebra flat over
  regular prime quotient iff Hilbert Samuel lengths agree with iterated partial
  sums of localized Hilbert Samuel lengths`. Eight results, including
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`,
  `Module.flat_of_isLocalized_maximal`, and regular-sequence/going-down facts;
  none states the iff of complete Hilbert--Samuel sequences.
- Loogle: `"associatedGraded", "Flat"`. Zero hits.
- grep: `Bennett|bennett|normal.?flat|hilbertSamuel|HilbertSamuel`. Zero Mathlib hits.
- LeanSearch: `A local algebra is normally flat along a regular prime quotient if
  and only if its Hilbert Samuel length function equals the dimension-fold partial
  sum of that of the localization at the prime`. Eight results concerning flat
  localization and local flatness, none this criterion.
- `rg` of the project Sheaf and upstream WeilConjectures directories for Bennett,
  HilbertSamuel, and normal-flat iff declarations, and `grep -rn` of the item id
  in WeilConjectures. No exact criterion exists. The relevant existing files
  `NormalFlatHilbertConvolution`, `FlatGradedFibreRegularLift`,
  `HilbertSamuelInvariant`, and `HilbertSamuelNearNormalCone` were read. The first
  supplies one direction in a different numerical form; none states this theorem.
  The last mentions this item only as an intended proof input.

No STATEMENT-DISPUTED flag or node fault is needed. The statement, dependencies,
proof, proof-dependency list, and source are unchanged.

Validation: prescribed `scompile.py` completed successfully against current server
sources (1.6 seconds, 60-second limit, two threads, nice 19), with no compiler
errors or non-sorry warnings. The wrapper's local attempt reported no free disk
space and automatically confirmed the result on the server. No direct compiler,
global build, source checkout edit, or direct git command was used.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
