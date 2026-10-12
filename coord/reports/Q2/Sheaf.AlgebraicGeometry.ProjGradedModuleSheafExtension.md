## What changed

Replaced the sole hole in `AlgebraicGeometry.Proj.gradedModuleSheaf_extension` by a
compiling proof with its original signature. Proved ring restriction compatibility
pointwise using Mathlib's `awayToSection_apply`, homogeneous-localization injectivity,
and `IsLocalization.ringHom_ext`. Transported chart modules along `basicOpenIsoAway`,
proved semilinearity over actual structure-sheaf restrictions, and supplied the positive
homogeneous basis, product intersections and finite refinement from
`standardOpenProperties`. Applied indexed basis extension, then proved the displayed
scalar formula and unique compatible isomorphism by constructing the linear family
`beta.symm`, using its universal property, and translating uniqueness through `beta`.

Split the remaining finite chart gluing, indexed basis extension and affine-local
quasi-coherence arguments into three new statement modules, each with its own node,
source and proof in words. The whole delivery compiles using lcompile.py. No existing
statement or definition changed. No data definition chooses an arbitrary unproved witness:
all sheaf witnesses are eliminated inside the proof of the existential theorem.

## Proved and sorry left

Closed: `AlgebraicGeometry.Proj.gradedModuleSheaf_extension`
(node `lem-weil-pbc-proj-graded-module-sheaf-extension`), 1 of 1 original holes.
Its proof is a decomposition, not an axiom-free proof of the whole theorem. The private
helper `AlgebraicGeometry.Proj.ringRestriction` is proved with no direct hole.

Added holes, exactly three:

- `AlgebraicGeometry.Proj.gradedModuleChart_gluing`,
  node `lem-weil-pbc-proj-graded-module-chart-gluing`.
- `AlgebraicGeometry.Proj.gradedModuleChart_quasicoherent`,
  node `lem-weil-pbc-proj-graded-module-chart-quasicoherent`.
- `TopologicalSpace.Opens.exists_sheafOfModules_from_indexed_basis`,
  node `lem-weil-pbc-sheaf-of-modules-from-indexed-basis`.

Each is the whole proof of one public theorem in a new module. The main module contains
no sorry. Holes closed minus holes added in this delivery is -2 before closure accounting.
The three new statements are strictly parts of the argument: a finite equalizer statement,
a generic topological extension theorem assuming gluing, and quasi-coherence of an
already-given chart-identified sheaf. None asserts the original combined conclusion.

## No longer needed

Removed direct proof imports from the main module:
`Sheaf.Algebra.Module.GradedModuleAwayRestriction`, `Sheaf.RingTheory.CoverModuleExact`,
`Sheaf.Topology.SheafOfModulesFromBasis`, `Mathlib.AlgebraicGeometry.Modules.Tilde`.
These are still needed below the new intermediate nodes; no global module pruning is
claimed. The parent node no longer directly uses `lem-weil-pbc-graded-module-away-restriction`,
`lem-weil-pbc-cover-module-exact`, `lem-weil-pbc-sheaf-of-modules-from-basis`,
`lem-weil-pbc-proj-basic-open-intersection`, `lem-weil-pbc-spec-module-tilde-sections`,
or `pqf-def-coherent` as proof steps. Each remains in the appropriate child's plan.
No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The basis-extension interface takes a set of opens, whereas this chart system indexes
positive homogeneous denominators and allows multiple representatives of one open.
The indexed-basis helper states precisely the missing transport glue, from the existing
basis extension, without any graded-module or quasi-coherence content. Its proof was
attempted in Lean; the remaining obstacle was dependent transport across equal opens,
so the unfinished proof is replaced by the required whole-theorem hole.

The source files are absent at the repository's `literature/stacks-project/` path on this
machine. Read the available copies `/home/ubuntu/c1-stacks-review/constructions.tex`
(labels lemma-standard-open, definition-structure-sheaf, lemma-proj-sheaves,
lemma-standard-open-proj, lemma-proj-scheme) and
`/home/ubuntu/c1-stacks-review/sheaves.tex` (labels lemma-extend-off-basis-module and
lemma-restrict-basis-equivalence-modules). The new nodes retain the canonical project
source paths. Searches: LeanFinder for graded sheaves returned ring-only results;
Loogle for Proj and Opens.IsBasis returned chart/topology results; grep found no matching
module theorem. LeanSearch failed with Internal Server Error and is recorded unavailable.

Edge cases checked mathematically: empty Proj; nilpotent denominators and empty charts;
the empty finite cover (unit ideal forces a zero ring/module); repeated indices in the
basis; an empty indexed basis on the empty space; and the zero principal generator in
the quasi-coherence comparison. No statement is believed false. The indexed theorem's
identity/composition laws already force restriction between equal opens to be invertible;
it requires no extra bijectivity assumption.

## New nodes

`lem-weil-pbc-proj-graded-module-chart-gluing` in
`Sheaf.AlgebraicGeometry.ProjGradedModuleChartGluing` formalizes the finite Cech equalizer
for the prescribed restriction maps, including the empty cover. Its remaining proof
uses the original localization comparisons, their uniqueness and the unit-ideal criterion.

`lem-weil-pbc-proj-graded-module-chart-quasicoherent` in
`Sheaf.AlgebraicGeometry.ProjGradedModuleChartQuasicoherent` concerns an already given
sheaf and its chart identifications. It follows the principal-open/tilde comparison of
Stacks 01MB, independently of existence or uniqueness of the extension.

`lem-weil-pbc-sheaf-of-modules-from-indexed-basis` in
`Sheaf.Topology.SheafOfModulesFromIndexedBasis` handles duplicate representatives of basis
opens and exposes only the extension and morphism universal property needed here.
It reduces to the existing basis-extension theorem by choosing one index per open,
with representative transports determined by the restriction maps. No change records.

## Second reading by Q2

1. **Statements unchanged.** Compared the delivered extension module with the repository version; the target declaration and all existing declarations retain their signatures byte for byte. The three added theorem statements are new, and no definition was changed.

2. **Proof checks.** Compiled all four delivered Lean modules with `lcompile.py --all`. The extension theorem has no `sorry`; the only remaining holes are the three named split theorems. No forbidden declarations or hollow definitions occur. Scratch-copy `#print axioms` checks show only `propext`, `Classical.choice` and `Quot.sound` for the private ring restriction helper, and those plus `sorryAx` for the extension and the three split statements. The main theorem therefore remains dependent on open statements, as reported above.

3. **Split statements.** Checked the indexed-basis theorem against the existing set-indexed basis extension theorem and the Stacks basis-extension lemmas; duplicate representatives are handled by identity/composition transport, and empty finite covers are included. Checked chart gluing against the standard-open and localization statements; it is strictly the finite equalizer subproblem. Checked quasi-coherence as a theorem about an already-given sheaf with chart identifications; it does not restate existence or uniqueness. Searches found no existing declaration duplicating these statements.

4. **Pruning and route.** The main proof follows the unit route: structure-sheaf restriction compatibility, chart finite gluing, indexed basis extension, uniqueness, then quasi-coherence. The direct imports removed from the parent are now imported by the split helper modules where their proofs require them. The indexed-basis node depends on the existing basis-extension node; chart helper proof dependencies and step citations were repaired during this reading.

5. **DAG agreement.** Verified the parent and three child nodes against the Lean declarations, including proof steps and `proof_deps`. The unit record is unchanged and its realized route is preserved. No change record is required.

Changes made in this reading: corrected helper imports, repaired child step citations and dependency unions, removed an unused helper import, and added this review section. No mathematical statement or proof body was changed. Rechecked empty Proj, nilpotent denominators, zero modules, empty finite covers, duplicate indices and the empty indexed basis; none gives a counterexample. Independent LeanFinder searches used finite localization equalizers, duplicate-index basis extension and quasi-coherent homogeneous localizations; results were ring charts, generic sheaf morphism extension and presentations, with no exact match. The upstream Twist module explicitly leaves the arbitrary graded-module construction unimplemented. The Loogle query with `IsIso` was rejected as an unknown identifier and was not treated as a successful negative search. Closing the three substantial remaining subproblems is beyond a quick repair.
