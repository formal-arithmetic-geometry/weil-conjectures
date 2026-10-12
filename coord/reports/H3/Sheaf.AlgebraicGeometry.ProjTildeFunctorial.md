## What changed

Proved `AlgebraicGeometry.Proj.tilde_functorial` in
`lean/Sheaf/AlgebraicGeometry/ProjTildeFunctorial.lean`, with its signature unchanged.
The proved private helpers `away_exists_fraction`, `localized_map_smul`, and
`tilde_chart_map_exists` construct the chart maps and extend them with Mathlib's
basis morphism equivalence. The main proof proves uniqueness, composition, identities,
and the stalk fraction formula. Added the proof-only import
`Mathlib.Topology.Sheaves.SheafCondition.Sites`. Updated the existing node's proof,
proof dependencies, and proof origin to describe this route. No new modules or nodes.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Proj.tilde_functorial`
(node `lem-sc-p1-proj-tilde-functorial`). No `sorry` remains in the delivered module;
no holes were added or split off. All three private helpers are fully proved.
The proof uses the existing stated theorem `AlgebraicGeometry.Proj.standardOpenProperties`,
which remains an upstream dependency with its own existing hole. This delivery does
not claim the entire transitive proof closure is sorry-free.
Local single-file compilation passes without warnings. The delivery dry run supplies
local axiom probes, server compilation, and mechanical preflight.

## No longer needed

Removed proof-only imports `Sheaf.Algebra.Module.GradedModuleAwayRestriction` and
`Sheaf.Topology.SheafOfModulesFromBasis`. Their corresponding proof dependency nodes
`lem-weil-pbc-graded-module-away-restriction` and
`lem-weil-pbc-sheaf-of-modules-from-basis` are not used by this proof: ordinary Mathlib
localized linear maps and the general Mathlib basis morphism equivalence suffice.
The theorem `gradedModuleSheaf_exists` of
`Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists`
(node `lem-weil-pbc-proj-graded-module-sheaf-exists`) is also not used in the proof:
its relevant chart/stalk data are already explicit hypotheses. Its public import
remains because it supplies the existing statement's definitions and types.
Thus these nodes are removed from this node's proof dependencies; their modules may
remain in the targets' closure through other paths, including the retained public import.
Retained `ProjStandardOpenProperties`: its basis and homogeneous inclusion relation
are both used. This is below the blueprint unit level; no realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned stalk argument implicitly treats the denominator as positive-degree.
The compiled argument avoids this issue by representing an arbitrary stalk element
on a positive-degree basis chart first, proving compatibility with the ordinary
localized linear map, then applying its fraction formula at the originally specified
denominator. This proves the degree-zero case as well. No statement or definition changed.
The large graded-restriction and module-basis-extension existence statements are
unnecessary for functoriality of sheaves whose chart data are already given.

## Second reading by H3

1. **Statements unchanged.** Compared the delivered module and node with the repository versions. The public theorem signature is byte-for-byte unchanged; no definitions or hypotheses were altered.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no warnings or `sorry`. The proof contains no forbidden declarations. The private helpers are fully proved; the only imported open theorem is `standardOpenProperties`.
3. **Split statements.** No new public statements or nodes were added. The helper lemmas are private implementation details, so no split-off holes or nodes are needed.
4. **Pruning and route.** Verified that the proof uses ordinary localization maps, `standardOpenProperties`, and Mathlib basis extension. The removed proof-only imports are not referenced. The unit route remains represented by the standard-open and sheaf-morphism-on-basis dependencies recorded in the node.
5. **DAG agreement.** Checked the node proof steps and `proof_deps` against the implementation. The node records the pruned dependencies and the degree-zero-safe stalk argument. The theorem docstring was corrected to describe the actual route.

Changed the theorem proof docstring to match the implemented localization, basis-extension, uniqueness, and stalk arguments; no Lean statements or new holes were introduced.
