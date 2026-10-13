## What changed

The original module's declaration signatures and existing definition bodies are unchanged.
Its sole hole is replaced by a reduction to normalized local comparisons and generation by
whole-chart sections. Restriction naturality is proved by span induction, in a local argument
for arbitrary scheme modules; the local argument introduces no declaration or axiom.
The only new imports in the item are proof-only imports of
`ProjGradedModuleChartBasisComparisonFixedMaps` and
`ProjGradedModuleChartBasisComparisonFixedGenerators`. The maps module publicly imports
ProjectiveSpectrum.Basic and Modules.Tilde because its statement uses those APIs. The generators
module needs only ProjectiveSpectrum.Basic and Modules.Sheaf; it does not import Tilde.

The first worker's false compatibility theorem and its node were removed. The core construction
was repaired to retain `hcanonical` and assert normalization on whole-chart restrictions.
The generators theorem is a separate, strictly smaller geometric statement. No arbitrary
object is defined by selecting a witness of an unproved existence theorem: existential maps
are eliminated only inside the proof of a proposition. All definitions are actual constructions.

## Proved and sorry left

Hole closed syntactically:
`AlgebraicGeometry.Proj.gradedModuleChart_basisComparison_fixed`.
Its naturality argument is proved using normalization, functoriality, and span induction.

Holes added, each in a new module with a source and complete proof in words:

- `AlgebraicGeometry.Proj.gradedModuleChart_basisComparison_fixed_core`, node
  `lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-core`:
  construction of independent bijective local linear maps extending one whole-chart map.
- `AlgebraicGeometry.Proj.gradedModuleChart_basisComparison_fixed_generators`, node
  `lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-generators`:
  generation of principal-open sections by whole-chart restrictions.

This is a decomposition, not a completed proof. Relative to the repository, one upper hole
is closed and two strictly smaller holes are added: syntactic net -1. The theorem still depends
on `sorryAx` through these two open lemmas; zero of the one original theorem is proved using
only the three allowed axioms. No claim of positive ledger progress is made. The maintainer's
pinned sorry ledger remains the authority for closure-wide counts.

## No longer needed

No repository module or dependency node is pruned. The original proof dependencies
`lem-weil-pbc-proj-basic-open-intersection` and `lem-weil-pbc-spec-module-tilde-sections`
are retained transitively: chart intersection under both geometric nodes, and tilde sections
under the normalized-comparison node. The item's new direct dependencies are precisely
those two nodes. The rejected sandbox-only compatibility module/node is removed; it was
never a repository dependency and is not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's compatibility theorem was false: arbitrary bijective local linear maps need
not commute with restriction. For example, for the structure sheaf on an affine-line chart of
Proj Q[X,Y], take identity on the whole chart and multiplication by 2 on its proper principal
open D(Y/X). Both are linear bijections, but restriction of 1 gives 2 on one side and 1 on the
other. Thus bijectivity cannot be the only hypothesis on the family. The previous report
also described a whole compatible core construction that its Lean statement did not provide.
Both copied new docstrings invoked `hcanonical` although their declarations omitted it.
The repaired lemmas retain this hypothesis and state only their actual geometric steps.

Mathlib's `span_eq_top_of_isLocalizedModule` provides the abstract algebraic generation fact;
it does not supply the required geometric identification of restriction with localization.
`PresheafOfModules.naturality_apply` assumes a presheaf morphism, so using it to construct one
here would be circular. Local chart-comparison consumers also import this item and cannot
provide an acyclic shortcut.

## New nodes

`lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-core` records independent
principal-open comparisons normalized by one whole-chart additive map. It asserts no
naturality between two proper principal opens.

`lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-generators` records only a span
equality for source sections, with no comparison map or naturality conclusion. Both nodes
include exact Lean signatures, provenance, proof steps, completed Loogle/LeanFinder and grep
searches plus the recorded unavailable LeanSearch attempt, and the
original chapter and unit. No change record is needed: no existing signature, definition,
visibility or public import was changed.

## Second reading by M4

1. Compared the delivered item with the repository using diff and a byte comparison of its
   theorem signature: identical. Existing docstrings and the local scalar instance are unchanged.
   Only proof imports and the theorem proof differ. The two new statements have no existing
   repository version. Verdict: pass after repair.
2. Compiled all three files locally with lcompile.py, without errors or warnings. Inspected every
   definition and scanned for forbidden constructs. The only two sorries are the exact named
   geometric theorem bodies listed above. Scratch-copy #print axioms checks and the delivery
   probe check the dependency axioms. Verdict: valid conditional reduction, with the two
   explicitly documented open lemmas; no axiom-free completion is claimed.
3. Rejected the arbitrary-family compatibility statement by the characteristic-zero example
   above. Repaired normalization and retained canonical scalar restrictions. Checked zero
   localization, empty and nilpotent charts, r=1, and arbitrary principal presentations: both
   corrected statements apply without finite-generation or nonempty-open hypotheses. Each has
   a source, a full proof in words and a matching node. Independent leanfinder, loogle and grep
   searches found only the component Mathlib tools described above. LeanSearch was also
   attempted but returned Internal Server Error; its unavailability is recorded without a verdict. Neither lower statement
   restates the original theorem: one constructs local maps without naturality, the other
   describes generators without any target sheaf. Verdict: pass as a decomposition.
4. The proof uses the original chart-intersection and tilde-localization route in the lower
   lemmas and proves the algebraic naturality step. No imported repository module becomes
   unused, and the No longer needed section accounts for all old proof dependencies.
   Inspected dag/units/sk-thm-reduction.json: this node is below the unit's realized statement
   and steps; none of those steps is bypassed or changed. Verdict: pass.
5. Checked exact new Lean signatures against lean.statement in the new nodes; proof_deps is
   the union of each node's step uses. The item's node now names normalized local comparison
   and generation, followed by an elementary span-induction step matching Lean. New nodes
   include the required created, blueprint, status, source, search, chapter and unit records.
   Verdict: pass after replacing the false compatibility node.

Second reading changed the invalid split into normalized local comparisons plus generation,
proved naturality by span induction, restored the canonical-map hypothesis in new lemmas,
and rewrote the node records and report to disclose the decomposition and net hole count.
Sources checked directly: [Stacks 01M4](https://stacks.math.columbia.edu/tag/01M4),
[01M7](https://stacks.math.columbia.edu/tag/01M7),
[01MB](https://stacks.math.columbia.edu/tag/01MB), and
[01HV](https://stacks.math.columbia.edu/tag/01HV).

The final local set compiled without warnings; scratch-copy axiom checks for all three theorems
reported only propext, Classical.choice, Quot.sound and the documented sorryAx.
