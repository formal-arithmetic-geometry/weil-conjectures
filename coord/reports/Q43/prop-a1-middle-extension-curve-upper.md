## Worker report

The module `Sheaf.Paper.CurveMiddleExtensionUpper` states
`AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_compactlySupportedCohomology_curveMiddleExtension`
with proof `sorry`. It formalizes the proposition in the current blueprint
`main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/prop-a1-middle-extension-curve-upper.md`.
The natural statement, statement dependencies and proof dependencies are unchanged.
There are two dependency interface modules, described below, and no new DAG nodes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The standing finite-field convention is `{k₀ : Type u} [Field k₀] [Finite k₀]`.
  Every finite field has cardinality p^a with a >= 1; the proposition does not use a
  separately named p or a. `[Fact l.Prime] [Fact (ringChar k₀ ≠ l)]` supplies the
  coefficient prime and its distinction from the characteristic. `PadicAlgCl l`
  is the existing chosen algebraic closure of Q_l. Replacing an algebraic closure
  by the chosen isomorphic closure does not restrict the coefficients.
- U₀ and C₀ are `{U C : Scheme.{u}}` with the two `Over (Spec (.of k₀))`
  instances. The two `IsCurve` instances give separatedness, finite type and
  dimension at most one. The two `SmoothOfRelativeDimension 1` instances express
  smooth curves of pure dimension one. The two `GeometricallyConnected`
  instances express geometric connectedness, including nonemptiness. Together
  these are exactly smooth geometrically connected curves, not affine or proper
  curves and not zero-dimensional schemes.
- The open immersion is `(j : U ⟶ C) [IsOpenImmersion j]`; being a morphism over
  k₀ is `[j.IsOver (Spec (.of k₀))]`. Density is `(hj : DenseRange j.base)`.
  There is no extra quasi-compactness assumption on j: the middle-extension
  interface derives it from quasi-compactness of U's structure morphism and
  quasi-separatedness of C's structure morphism.
- The given coefficient identification is `(ι : PadicAlgCl l ≃+* ℂ)`, matching
  the source's isomorphism. The existing weight predicates take its underlying
  ring homomorphism; this forgets no condition on the given iota.
- `(F : WeilSheaf k₀ l U)` is the constructible Qbar-Weil sheaf in the standing
  coefficient convention, and `(hF : F.IsLisse)` is precisely lissity of its
  underlying sheaf. `(w : ℝ)` allows every real weight.
- `(hw : F.IsPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) w)` is punctual
  purity at every closed point. The existing predicate uses the local geometric
  Frobenius and that point's residue-field cardinality.
- `((curveWeilMiddleExtension j).obj F)` is ordinary sheaf j_*F, retaining
  the Weil structure via the canonical geometric Frobenius comparison. It is
  neither Rj_*F nor a shifted/perverse object.
- `(ordinaryCompactWeilSheafCohomology ... r).2` is precisely H_c^r(C,j_*F)
  as a finite-dimensional vector space with geometric Frobenius. The `.1`
  component of the same dependency is ordinary cohomology, so the ordinary and
  compact-support constructions have distinct, explicit meanings.
- `(r : ℤ)` means every integer degree. `HasWeightsAtMostOver k₀ ... (w +
  (r : ℝ))` is the displayed upper bound: every eigenvalue alpha of geometric
  Frobenius has |iota(alpha)| <= (#k₀)^((w+r)/2). No vanishing, purity, or
  lower-bound assertion is added to the conclusion.

Dependency declarations used:

- `def-weil-punctual-weights`: `WeilConjectures.DeligneLaumon.Reduction.Weights`
  reexports `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight` from
  `WeilConjectures.WeilSheaf.Stalk`; read its full signature and docstring, and
  the recorded mixed-filtration definition. Purity is used directly.
- `def-wf-middle-extension`: the new recorded interface is
  `Sheaf.Paper.CurveWeilMiddleExtension`, declaration
  `AlgebraicGeometry.WeilSheaf.curveWeilMiddleExtension`. Its real data are the
  existing `WeilSheaf.directImage` from `WeilConjectures.WeilSheaf.OpenImmersion`,
  itself the existing ordinary `lowerStar`, with Frobenius transported by
  `adicLowerStarGeometricFiberMapCompFrobeniusIso`. The previously recorded
  `Scheme.curveMiddleExtension`, its coefficient-stage constructions and its
  shifted version remain publicly imported from `Sheaf.Paper.CurveMiddleExtension`.
- `def-weil-ordinary-compact-cohomology`: the new recorded interface is
  `Sheaf.Paper.OrdinaryCompactWeilCohomology`, declaration
  `AlgebraicGeometry.WeilSheaf.ordinaryCompactWeilSheafCohomology`. Its real
  data are the existing upstream `WeilSheaf.cohomology` and
  `WeilSheaf.compactlySupportedCohomology` from `WeilConjectures.WeilSheaf.Cohomology`.
  These take geometric sections of cohomology of Ra_* and Ra_!, with induced
  geometric Frobenius. The original full finite, integral, rational and Qbar
  coefficient definitions remain publicly imported from
  `Sheaf.Paper.OrdinaryCompactCohomology`; its primary tuple and relevant
  qbarWeilSheafCohomology definitions were read in full.

The proof docstring follows both proof paragraphs in the node: affine core and
lisse recovery/transitivity, then the zero-rank case, affine bounds, boundary
weights and concentration, localization in each degree, and subquotient/extension
stability. Already recorded proof modules are imported without `public`: affine
core, mixed extension and subquotient bounds, DegreeOne, LocalDuality and lisse
recovery. Finite-boundary cohomology is already in the public cohomology import.
The three proof nodes without Lean records (affine-curve upper, finite-boundary
weights, boundary-stalk invariants) have no module to import; they are retained in
the DAG and in the proof docstring, not restated as additional assumptions.
The published affine-core source was read using `scompile.py --source` because
that source is absent in the older local checkout.

Edge cases checked: j = identity has ordinary direct image F and gives the usual
curve estimate; a proper C and a non-affine C are both allowed; an empty boundary
is allowed; rank-zero F is allowed and the eigenvalue condition is vacuous on its
zero cohomology; degrees r < 0 and r > 2 are included and have the expected zero
cohomology; r = 0 has bound w and r = 1 has bound w+1. Empty schemes are excluded
by the stated geometric connectedness, not by an added assumption. No rank,
monodromy, unramified-at-infinity, affineness, or properness hypothesis is added.
All universe variables and binders are explicit, with both auto-implicit options
disabled. The general dependency interfaces themselves permit empty curves or
empty finite-type schemes where their original notions do.

Searches for existing notions/statements:

- `msearch.py ... leanfinder "Compactly supported cohomology of a curve middle
  extension of a pure lisse sheaf has weights at most w plus degree"`: eight
  unrelated hits (sheaf H and Lie weights); no curve estimate.
- `msearch.py ... loogle "WeilSheaf, compactlySupportedCohomology"`: zero hits,
  unknown identifier WeilSheaf in the Mathlib index.
- `msearch.py ... leansearch "weights of compactly supported cohomology middle
  extension smooth curve"`: service unavailable, rate limit exceeded (60/min).
- `msearch.py ... grep "middleExtension|PunctuallyPure|compactlySupportedCohomology"`:
  zero Mathlib hits.
- `rg` of the source WeilConjectures tree, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item's id, middle-extension upper bounds,
  and the three proposed declaration names: no existing general curve statement
  or conflicting name. The source `AffineLine.Upper` has only the affine-line
  theorem with an unramified-at-infinity hypothesis, so it is not this statement.
- Direct source searches located the existing ordinary `directImage`, both
  cohomology definitions and the eigenvalue weight predicates; these are reused
  rather than reconstructed. The dependency helpers are transparent API
  specializations/packaging, not alternative sheaf or cohomology definitions.

Validation: all three delivered modules compiled cleanly through `scompile.py`
as separate files in dependency order (approximately 2.2, 3.4 and 4.2 seconds for
library-form checks). No errors or unexpected warnings. An initial direct use
of ordinary j_* did not synthesize `QuasiCompact j`; the dependency wrapper now
supplies it from existing facts, without a new theorem or extra assumption.
Only the proposition has a sorry; both dependency definitions have real data.
No STATEMENT-DISPUTED flag or source-statement correction is needed.

## Second reading by Q43

Author's second pass, as required by the direct-dispatch brief; the maintainer
provides the independent review, and no other agent was started. Reopened the
node and all three files and checked the displayed bound against the signature.
Both curves have smooth relative dimension one and geometric connectedness;
j is an open immersion over k₀ and is explicitly dense; F is lisse and pure of
the same real w. The iota parameter was checked to be an isomorphism rather than
an arbitrary map. The conclusion uses the second, compact-support component,
ordinary j_* with no shift, #k₀ rather than a closed point's cardinality, and
w+r for every integer r. There is no affine or rank-positive restriction.

The interface mismatches found on first reading were that the original
middle-extension output had no Weil structure in its type, and the original
coefficient cohomology output did not retain a Frobenius operator. The two
transparent dependency interfaces now use the existing native Weil operations
with their canonical Frobenius, and publicly import all original coefficient
interfaces. The middle-extension wrapper also repairs failed instance inference
for quasi-compactness of j. Checked that neither wrapper contains sorry, an
arbitrary map, a noncanonical choice or a new unproved theorem. Checked that only
`lean` changes in both copied dependency nodes and the item, and all signatures
in those records are extracted verbatim from their corresponding files.

## Dependency modules

`def-wf-middle-extension`: `Sheaf.Paper.CurveWeilMiddleExtension` adds
`AlgebraicGeometry.WeilSheaf.curveWeilMiddleExtension`. The original
`Scheme.curveMiddleExtension` produces a coefficient-pair object without the
Weil structure needed to apply the recorded punctual weight predicate. The
new interface is ordinary `WeilSheaf.directImage`, with its existing canonical
Frobenius transport and no derived functor or shift. It derives the necessary
quasi-compactness from the curve hypotheses. Its public import retains the
original finite-extension adic coefficient realization and shift interfaces;
only the dependency's Lean record is changed. It is usable on the proposition's
smooth geometrically connected dense-open curve situation without extra data.

`def-weil-ordinary-compact-cohomology`:
`Sheaf.Paper.OrdinaryCompactWeilCohomology` adds
`AlgebraicGeometry.WeilSheaf.ordinaryCompactWeilSheafCohomology`. The original
coefficient-valued output cannot be supplied to weight predicates on
FrobeniusModule. The added pair is the existing ordinary and compact-support
cohomology of a Qbar-Weil sheaf, retaining the canonical geometric Frobenius
in every integer degree. No arbitrary endomorphism is chosen. All four original
coefficient interfaces, point-fibre equivalences, twists, constants and
linear-algebra operations remain publicly imported. This repairs the final
Weil-sheaf clause required here, without redefining any coefficient construction
or changing the dependency's natural statement or any field other than `lean`.

Dry-run repair: the preflight statement reader stops at a line beginning with `|`.
Replaced pipeline notation in the conclusion by the fully qualified application
`FrobeniusModule.HasWeightsAtMostOver`; the elaborated proposition is unchanged.
Refreshed the verbatim signature and reran compilation and the required dry run.
