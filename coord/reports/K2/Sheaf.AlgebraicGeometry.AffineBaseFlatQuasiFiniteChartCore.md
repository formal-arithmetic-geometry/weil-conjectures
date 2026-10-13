## What changed

Proved `AlgebraicGeometry.exists_affine_base_flat_quasiFinite_chart_core` in
`Sheaf.AlgebraicGeometry.AffineBaseFlatQuasiFiniteChartCore`, preserving its signature,
visibility and existing docstring. Added proof-only imports of
`Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart`,
`Sheaf.AlgebraicGeometry.PolynomialChartFibreFlatCriterion`, and
`Sheaf.RingTheory.OpenFlatLocus`.

The proof chooses affine neighborhoods inside the flat finitely presented restriction,
transports the fibre depth equality through actual fibre-stalk ring equivalences, applies
the quasi-finite chart theorem and the pointwise fibre-flatness criterion, and restricts
the chart to its open stalk-flat locus. The image-open isomorphism gives a morphism whose
source is an open of the original X. The projection compatibility is proved explicitly.
Private helpers prove depth invariance, restriction comparisons, and affine stalk-flat
locus openness; their arguments follow the already proved private helpers in
`FibreCohenMacaulayLocus`, `RestrictedFibreCohenMacaulayLocus` and
`AffineFibreCohenMacaulayLocus`. These larger modules are not imported.
Updated the item's node proof and proof dependencies to match this argument.

Single-file lcompile.py check passed without errors or warnings. The sandbox contains
only the item's Lean module and its updated existing node, with no new modules or nodes.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.exists_affine_base_flat_quasiFinite_chart_core`
(node `lem-sbc-affine-base-flat-quasi-finite-chart-core`).

No sorry remains in the delivered module. No new holes were added. This is a proof from
existing project declarations, not a new decomposition; existing transitive obligations
of the chart and fibre-flatness declarations remain for their respective workers.

## No longer needed

No original import was removed, and no existing project module is claimed globally pruned.
The original ring-level polynomial-factorization, miracle-flatness, fibrewise-flatness and
dimension-formula steps are supplied through the existing scheme-level chart and criterion
nodes, rather than imported and reconstructed here. Openness of flatness is still used
explicitly. The old direct proof dependencies no longer used directly are:
`lem-weil-pbc-quasi-finite-over-polynomial-algebra`,
`lem-weil-pbc-criterion-flatness-fibre`,
`lem-weil-pbc-miracle-flatness`, and
`lem-weil-pbc-dimension-at-point-local-ring-trdeg`.
These are encapsulated by the scheme-level chart and criterion; this does not
claim their modules are pruned from the target closure.
The updated direct proof dependencies are
`lem-sbc-quasi-finite-polynomial-chart`,
`lem-sbc-polynomial-chart-fibre-flat-criterion`, and
`lem-weil-pbc-openness-of-flatness`.

Removed the earlier sandbox's unpublished modules `AffineBaseChartUnderlying` and
`AffineBaseChartProperties` and their unpublished nodes `new-affine-base-chart-underlying`
and `new-affine-base-chart-properties`. Neither is needed. No unit statement or proof step
is bypassed: the affine polynomial factorization, fibrewise flatness, and flat shrinking
route is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier `affine_base_chart_properties` lemma was false: compatibility with f does not
make an arbitrary map to affine space flat or locally quasi-finite. This delivery deletes
that proposed split entirely. It first chooses a quasi-finite chart with the correct
number of variables, proves stalk flatness using the depth and dimension criterion, then
shrinks the source to its flat locus. Finding the false proposed intermediate statement
therefore did not obstruct the original theorem.

The repository has no local Stacks algebra.tex copy. Read [Stacks Tag 00RH](https://stacks.math.columbia.edu/tag/00RH), whose proof
chooses a quasi-finite polynomial factorization, establishes fibrewise then stalk flatness,
and shrinks using openness of flatness. This is the route implemented here. Empty source and empty U require no
special construction: the supplied point and ht exclude those cases. Dimension zero is
allowed throughout, including Fin 0 affine space. No affine intersection or Noetherian
base hypothesis is assumed.


## Second reading by K2

1. Compared the only delivered Lean module with the repository using `diff` and
   checked the existing theorem signature byte for byte. Verdict: unchanged
   hypotheses, conclusion, visibility, definitions and public imports. Only
   three proof-only imports, proved private helpers and the proof were added.
   There are no changed statements, new public statements or change records.
2. Compiled the module independently with `lcompile.py`: no errors or warnings.
   Scanned the source: no sorry, axiom, unsafe, opaque, extern, implemented_by,
   hollow definition or kernel bypass. Compiled a scratch copy with `#print axioms`
   for all eight private helpers and the main theorem. Verdict: only propext,
   Classical.choice and Quot.sound, plus existing transitive sorryAx for the
   flat-locus helpers and main theorem. All other helpers use just the three
   permitted axioms. No hole was added by this delivery. The existential chart
   is eliminated inside a proposition proof; no definition selects arbitrary
   data from an unproved existence theorem.
3. No split-off statements, new nodes or new holes remain. Verdict: nothing to
   validate as a new decomposition. Read the chart, fibre-flatness criterion and
   flat-locus declarations used by the proof. Checked empty source and empty U
   (excluded by y and ht), zero-dimensional fibres (Fin 0 is permitted), and
   arbitrary non-Noetherian bases. The source and base fibre-stalk comparisons
   use genuine open-immersion/isomorphism stalk maps, with regular sequences
   transported by ring equivalences; no hypothesis is silently strengthened.
4. Searched the upstream and Sheaf sources for alternate chart, depth-invariance
   and open flat-stalk declarations, and Mathlib with Lean Finder and Loogle
   using different queries. Verdict: no shorter available chart theorem;
   existing comparison helpers elsewhere are private. All three added imports
   are used directly. Each original public import supplies signature notions.
   Read the unit `sk-prop-normal-form`, including its `realized` field (empty),
   and [Stacks Tag 00RH](https://stacks.math.columbia.edu/tag/00RH).
   Polynomial factorization, fibrewise flatness and flat shrinking are retained;
   no realized unit step is bypassed. The final image-open isomorphism gives
   an actual open O of X containing y, and the projection equality is proved.
5. Compared both node JSON files and checked the dependency union of the proof
   steps. Verdict: only proof, proof_deps and proof_origin changed; they match
   the Lean argument and the three imported project declarations. Statement,
   source, unit, blueprint and Lean signature record are unchanged. No new
   node requirements apply.

Second reading changed only this report: explicitly listed all four retired
old direct proof dependencies under `## No longer needed`, recorded the axiom
limits and all five review verdicts. The Lean proof and node needed no repair.
