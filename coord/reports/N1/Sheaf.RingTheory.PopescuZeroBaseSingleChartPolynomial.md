## What changed

Replaced the hole in Algebra.PopescuLiftPresentation.zero_base_single_chart_polynomial
by a compiling composition of two algebra equivalences, with its signature unchanged.
The coefficient image of a_k is a unit by localization; the given normalization maps
to the normalized linear system over the coefficient tensor product.

Added Sheaf.RingTheory.PolynomialLinearElimination with a complete proof of
MvPolynomial.linear_elimination. Both inverse maps are explicit polynomial evaluation
maps. The reverse map descends through the ideal; both composites are proved to be
identities on generators. It supports arbitrary variable types, including infinite
ones with a finite free subset.

Added Sheaf.RingTheory.PopescuZeroBaseSingleChartPresentation with the remaining
coefficient-presentation calculation. Its coefficient map and ideal are explicit
constructions, with no choices from unproved existence statements. Updated the
original node's proof route and added nodes for the two calculations.

## Proved and sorry left

Closed: Algebra.PopescuLiftPresentation.zero_base_single_chart_polynomial (original
node lem-weil-pbc-popescu-zero-base-single-chart-polynomial). There are no sorries in
the item's module.

Proved without sorry dependencies: MvPolynomial.linear_elimination
(lem-weil-pbc-polynomial-linear-elimination).

Added one hole: Algebra.PopescuLiftPresentation.zero_base_single_chart_presentation
(lem-weil-pbc-popescu-zero-base-single-chart-presentation). This is a decomposition,
not a net hole reduction: one original hole closed, one strictly smaller hole added.
The remaining lemma retains all auxiliary variables and linear equations and has no
normalization hypothesis. The solved part is elimination of the dependent variables.

All three modules compile together without warnings using lcompile.py --all.
Edge cases checked in the argument: empty E (every auxiliary variable is zero),
E containing every variable (all linear relations are zero), zero coefficient ring,
and a_k zero in the original coefficient quotient (localization becomes the zero ring).
None needs a nonzero-ring hypothesis. No existing statement or definition was changed.

## No longer needed

No original imports removed. In the new PolynomialLinearElimination module, narrowed
public Mathlib.Algebra.MvPolynomial.CommRing to Basic, imported Eval only for the proof,
and removed the redundant public Mathlib.Algebra.Algebra.Equiv import. Quotient.Operations
is public because the statement needs its quotient algebra instance.
The existing public import of PopescuLiftPresentation
is needed by the unchanged statement. No original modules or nodes become unnecessary:
the original dependencies supply the presentation and localization definitions.
The old direct proof edges lem-weil-pbc-popescu-lift-preparation and
def-weil-pbc-module-localization-away are replaced by the two calculation nodes and
def-weil-ring-localization-away. The preparation node still supplies the data definitions
through stmt_deps; module localization is not used in this ring calculation. Neither
old module becomes unreachable, so no module is claimed pruned.
No preparation theorem, conormal basis, smoothness, differential basis, or other-chart
relation lemma is used. Proof-only imports of the two new modules were added.

## Where the brief, the DAG or earlier work was wrong

The original node's proof dependencies named definitions but did not state the
coefficient-presentation calculation needed to implement its first two steps. That
calculation is now a separate theorem. The final linear elimination step is proved
in Lean instead of being postponed together with it.

LeanSearch returned HTTP Internal Server Error for both queries; this is recorded
as unavailable, not as a negative search result. LeanFinder found general presentation
base-change and polynomial-quotient ingredients, but no exact single-chart theorem.
Blueprint searches for polynomial linear, single chart, 07CP, and linear relation
returned no matching blueprint nodes. The unit's realized statement and steps are
unaffected.

## New nodes

lem-weil-pbc-polynomial-linear-elimination: the normalized linear system over an
arbitrary commutative ring with a unit leading coefficient; fully proved in
Sheaf.RingTheory.PolynomialLinearElimination.

lem-weil-pbc-popescu-zero-base-single-chart-presentation: scalar extension killing pi,
coefficient reduction, quotient and localization before any auxiliary-variable
elimination; one remaining public theorem hole in
Sheaf.RingTheory.PopescuZeroBaseSingleChartPresentation.

## Second reading by N1

1. Compared the original module with the repository using diff. The existing signature,
   docstring, visibility, and definitions are byte for byte unchanged. Only its proof
   and two plain proof imports changed. The other two modules are new; no forced
   adaptations or statement-change records are needed. Verdict: pass.
2. Compiled all three modules with lcompile.py. Searched all delivered sources for
   sorry and prohibited declarations: the sole hole is the named public theorem
   Algebra.PopescuLiftPresentation.zero_base_single_chart_presentation. Scratch-copy
   #print axioms checks show only propext, Classical.choice, Quot.sound for
   MvPolynomial.linear_elimination, singleChartCoefficient and singleChartLinearIdeal;
   the presentation theorem and the original theorem additionally show sorryAx.
   The coefficient map and ideal are explicit constructions; neither uses data from
   an unproved existence theorem. Verdict: pass as a decomposition, not a completed
   proof without sorry dependencies.
3. Read both new statements and every line of the elimination proof. Its evaluation
   maps kill the relation ideal and fix generators in both composites. Checked E empty
   (all variables become zero), E full (all relations vanish), m=0 and n=0, and zero
   coefficient rings, including localization at zero. The presentation lemma keeps
   all equations and variables without normalization, so it is a proper part of the
   argument, not a restatement. Its source and complete universal-property argument
   are in its docstring and matching node. Independently searched LeanFinder using
   generators/relations and annihilated-coefficient descriptions, Mathlib grep for
   killed variables and tensor equivalences, and both project source roots. Inspected
   the presentation/base-change candidates; they are ingredients, not an exact match
   or a short closure of the remaining calculation. Verdict: pass.
4. Checked the argument downward from the original hole and read the displayed
   calculation in [Stacks Tag 07CP](https://stacks.math.columbia.edu/tag/07CP).
   The single-chart variant retains all f equations, so no prepared-conormal hypothesis
   is needed. The already proved elimination is the direct generator argument. Narrowed
   its imports as listed above and checked public versus proof-only visibility. Listed
   both old direct proof edges under No longer needed, distinguishing retained statement
   definitions from unused proof steps. Read dag/units/sk-thm-p1.json realized: this
   calculation lies below its prescribed steps and bypasses none of them. Verdict: pass.
5. Compared all three nodes with their Lean statements, dependencies, source, proof
   steps and origin; checked new-node metadata and the union of each proof's uses.
   Corrected the original node's coefficient-unit step to cite
   def-weil-ring-localization-away, since the Lean uses algebraMap_isUnit, not lift.
   The new presentation node still describes its unproved universal-property route;
   the elimination node describes the fully checked evaluation proof. Verdict: pass.

Changed only the new elimination module's imports, the original node's dependency
citation and explanation, and this report. No proof body or statement needed repair.
One original hole is closed syntactically and one lower hole is added; net hole
reduction is zero. No modules are pruned.
