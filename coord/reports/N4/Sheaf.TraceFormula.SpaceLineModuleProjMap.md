## What changed

Kept the statement, public imports and definitions of the assigned module unchanged.
Replaced its sorry by a proof using a directly constructed generation subfunctor and
scheme-test morphisms. The natural transformation, its uniqueness, inverse-image
subfunctor identification and uniqueness of the primed transformation are proved
in private helpers of the assigned module.

Added SpaceLineGenerationOpen with a complete proof: generation sets are open and
pull back along arbitrary scheme-test morphisms; the everywhere-generation condition
is an fppf subsheaf represented by an open on each test; pulling back the atlas and
diagonal gives an algebraic space. The reverse generation implication uses a local
ring map reflecting a unit at the image point, not arbitrary pullback reflecting
surjectivity globally. No coherence hypothesis is required for this part.

The two remaining scheme calculations are separate public statements in
SpaceLineTestMap and SpaceLineTestBaseChange. The first constructs the unique scheme
map with its formulas on further tests. The second compares coefficientwise
base change on a single scheme test; it constructs neither an algebraic space nor
a natural transformation. Their sources and full arguments are in their docstrings
and new nodes. The assigned node now follows the implemented proof.

All four retained Lean files compile together through lcompile.py --all. The resumed
full compile passed with exit code zero; there were no errors or warnings. Lines are at most 100 characters. No adopted source-library file was changed.

## Proved and sorry left

Closed the assigned hole in
AlgebraicGeometry.AlgebraicSpace.space_line_module_proj_map (one of one).
This is a decomposition, not a proof of its entire dependency closure: two new holes
remain, a net increase of one relative to this packet's original single hole.

Proved without a new sorry:
AlgebraicGeometry.AlgebraicSpace.exists_space_line_generation_open
(node lem-trf-space-line-generation-open), and the private canonical-map assembly
and base-change assembly helpers in SpaceLineModuleProjMap.

Added exactly two sorries:

- AlgebraicGeometry.AlgebraicSpace.existsUnique_space_line_test_map,
  node lem-trf-space-line-test-map, in SpaceLineTestMap.
- AlgebraicGeometry.AlgebraicSpace.space_line_test_base_change,
  node lem-trf-space-line-test-base-change, in SpaceLineTestBaseChange.

There are zero sorries in the assigned module, zero in SpaceLineGenerationOpen,
one in SpaceLineTestMap and one in SpaceLineTestBaseChange. Every new sorry is the
entire proof of its named public theorem. No definition has a sorry.

## No longer needed

The assigned module removes these private imports:

- WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
- Mathlib.AlgebraicGeometry.Gluing
- Sheaf.AlgebraicGeometry.AlgebraicSpace
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
- WeilConjectures.AlgebraicGeometry.Modules.Invertible
- WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
- WeilConjectures.AlgebraicGeometry.RelativeProj.Basic

The definitions and already proved APIs needed from these sources remain available
through the unchanged public input module. These removals do not withdraw any source
declaration or imply that those modules are absent from the transitive closure.

This proof does not use the old planned argument nodes
lem-trf-line-proj-affine-chart-atlas (Sheaf.TraceFormula.LineProjAffineChartAtlas),
lem-trf-line-proj-chart-pullback (Sheaf.TraceFormula.LineProjChartPullback), or
lem-trf-etale-open-chart-morphism-descent
(Sheaf.AlgebraicGeometry.EtaleOpenChartMorphismDescent). It constructs the open
subfunctor directly, and assembles the morphism on all scheme tests by uniqueness.
Their statements take sheaf presentations and actual tensor-pullback sheaf maps;
the assigned statement instead takes affine-basis GradedAlgebraData and cartesian
scheme-test components. No bridge back to those sheaf presentations is supplied by
the cited declarations. The new scheme statements expose the needed calculations
in the actual input interface instead of assuming such a bridge.

The parent's proof_deps also no longer directly lists def-pc-module-pullback,
def-sc-invertible-module, def-trf-algebraic-space,
lem-weil-pbc-scheme-morphism-gluing, lemma-nagata-relative-proj-base-change-arbitrary,
or lemma-nagata-relative-proj-exists: the retained subresults and input definitions
account for their uses. No global module withdrawal is claimed. No unit statement
or realized unit step is bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid, but its existing declared sheaf-level chart lemmas
do not directly accept the affine-basis/cartesian-test inputs of this item. Searches
in the library found no inverse GradedAlgebraData-to-RelativeProjAlgebra interface.
The input's own naturality law gives a shorter proof of the generation subfunctor
than choosing a new etale descent datum. There is no disputed existing statement,
no signature repair or forced adaptation. The preflight requested a record for the
two added local elaboration options; this is documented in
`coord/changes/N4-space-line-proj-proof-elaboration.md`, including every consumer.
The first preflight refused only that missing record and pushed nothing.

The interrupted session preserved the original sandbox and deadline. No delivery
was repeated from an unknown outcome: no item delivery was running and no delivery
receipt was present. The existing packet was read again and all four modules were
compiled successfully before delivery.

## New nodes

lem-trf-space-line-generation-open is fully proved. It isolates the geometric
representability of the generation condition and includes arbitrary-test pullback,
fppf descent, diagonal and atlas verification.

lem-trf-space-line-test-map is the scheme construction and its uniqueness on a
generating test, before any natural transformation or base-change assertion. The
new IsCanonicalTestMap predicate is an explicit definition, with no chosen data.

lem-trf-space-line-test-base-change is the coefficient calculation and equality of
specified maps on individual scheme tests. It assumes those maps already exist;
the parent independently constructs and assembles them. Its local-ring calculation
uses arbitrary coefficientwise base change and includes empty tests and arbitrary
grading degrees. Both remaining statements are strictly parts of the original
argument and have independent sources in Stacks 01NK, 01O9 and 0D2Z.

Change record: `coord/changes/N4-space-line-proj-proof-elaboration.md`.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
