## What changed
The second reading replaced the first worker's conjunction-component split with a reduction
through the existing `module_cohomology_isZero_of_cech_vanishing`. The unchanged target
`module_pushforward_injective_acyclic` now obtains Čech vanishing for the pushforward,
applies that criterion, and uses a general cohomology-to-derived-sections comparison.
The two new helper modules are `ModulePushforwardInjectiveCechVanishing` and
`ModuleSectionsAcyclicOfCohomologyVanishing`, each under `lean/Sheaf/AlgebraicGeometry/`.
The first worker's two helper modules and node files were removed before delivery.
The existing public imports, declaration signature and docstring are unchanged.
New imports of the target are plain proof-only imports. No statement/definition change
record is needed. The parent node now records the actual two-step reduction.

## Proved and sorry left
`AlgebraicGeometry.Scheme.Modules.module_pushforward_injective_acyclic`: its own proof
is closed, using the existing Čech criterion and two new strictly intermediate statements.
This is a partial proof delivery: the axiom audit still includes `sorryAx` through the
open dependencies; it is not a complete axiom-free proof of the target.

Exactly two new named statements retain `:= by sorry`, with full sourced docstring proofs:
- `module_pushforward_injective_cech_vanishing`, node
  `lem-weil-pbc-module-pushforward-injective-cech-vanishing`;
- `module_sections_acyclic_of_cohomology_vanishing`, node
  `lem-weil-pbc-module-sections-acyclic-of-cohomology-vanishing`.

The existing imported `module_cohomology_isZero_of_cech_vanishing` remains open upstream.

## No longer needed
Removed direct proof imports from the target:
- `Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic`;
- `Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives`;
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`;
- `Sheaf.AlgebraicGeometry.TensorPullback`;
- `Sheaf.CategoryTheory.SiteCechComplex`.

The first three remain imported in the intermediate modules where their mathematical
proof plans need them; the last two remain available transitively as appropriate.
None is asserted globally unreachable from all targets. The old parent proof dependencies
no longer used directly by its Lean proof are:
- `def-sc-zariski-site`;
- `def-pc-module-pullback`;
- `def-weil-pbc-site-cech-complex`;
- `lem-weil-pbc-module-injective-open-cover-cech-acyclic`;
- `pqf-def-cohomology`;
- `def-weil-sheaf-of-modules-category`;
- `lem-weil-pbc-scheme-modules-enough-injectives`;
- `def-sp-left-exact-additive`;
- `def-sp-injective-resolutions`;
- `lem-weil-pbc-module-open-restriction-injectives`;
- `lem-weil-pbc-module-restriction-open-immersion-colimits`;
- `def-sp-acyclic`;

These dependencies are retained indirectly through the helper nodes where required.
The Čech criterion remains a direct proof dependency. No unit realization node is removed.

## Where the brief, the DAG or earlier work was wrong
The first worker's split merely separated the two conclusions; its right-acyclicity
sketch did not assume or establish positive cohomology vanishing. Its nodes had empty
proof dependencies, prose in `lean.statement`, inherited unrelated search records, and
a mismatch between the right-acyclicity node id and docstring. A `letI` before `sorry`
also violated the whole-proof requirement and emitted a linter warning. The parent
node was not updated to agree with the Lean reduction. All these faults are repaired.
The library Čech criterion already provides the cohomology part once Čech vanishing is
supplied, so no new theorem repeating that cohomology conclusion is needed.

## New nodes
`lem-weil-pbc-module-pushforward-injective-cech-vanishing` states Tag 01EX (1),
matching the precise hypothesis of the existing Čech criterion. Its proof identifies
inverse-image Čech complexes and invokes the already stated injective Čech vanishing.

`lem-weil-pbc-module-sections-acyclic-of-cohomology-vanishing` isolates the generic
Tag 01E1 (2) comparison: a module with vanishing cohomology on all opens is acyclic
for each module-valued sections functor. This is not specific to pushforwards.
Both nodes have verbatim Lean signatures, complete proof steps and their dependency
unions, source records, and three kinds of fresh searches. Leansearch was unavailable
(Internal Server Error), recorded honestly; leanfinder, loogle, and grep succeeded.
No change records were added.

## Second reading by U2
1. Compared the target file with the repository using diff and a byte comparison of
   the full declaration signature. Verdict: identical signature, no definition changed,
   and no existing declaration removed. The final diff changes only proof imports and
   the proof. The two new statements are intermediate lemmas, not target replacements.
2. Compiled all three modules in import order with lcompile.py: no errors or warnings.
   Inspected every delivered file: no forbidden declaration/attribute, no hollow
   definition, and exactly two sorries, both the whole proofs of named public theorems.
   Scratch-copy `#print axioms` on all three declarations showed only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` from the explicitly open statements.
   Verdict: a valid partial reduction, not a fully completed target.
3. Read both intermediate statements and their natural-language proofs against
   https://stacks.math.columbia.edu/tag/01EX and
   https://stacks.math.columbia.edu/tag/01E1. Checked zero modules, identity morphisms,
   empty opens (including empty covers), and p=1. Inverse image respects arbitrary
   unions and finite intersections; scalar restriction preserves additive groups;
   restriction of injective resolutions gives the required derived-sections comparison.
   Searched with fresh wording using msearch.py (leanfinder, loogle, grep, attempted
   leansearch), and rg in both source roots. Verdict: true intermediate statements;
   no existing declaration closes either precise missing comparison. The current
   injective Čech lemma is insufficient by itself without the inverse-image comparison.
4. Read the target from the top. The existing Čech criterion is now applied directly,
   and the cohomology vanishing is reused in the sections comparison. Removed direct
   imports not needed by this reduction and listed every old direct proof dependency
   omitted from the parent. Read dag/units/sk-thm-p1.json: this node is below the unit's
   realized statement and steps, and this refactoring keeps the original Čech route.
   Verdict: no unit route bypass; no realized node is pruned.
5. Read all three node files against the final Lean. New lean.statement records are
   verbatim signatures; new proof_deps equal the union of step uses; parent proof and
   proof_deps match the calls in the Lean proof. Both new nodes have the parent's
   chapter/unit, proper created records, source, blueprint ancestry, and fresh searches.
   Verdict: DAG and Lean agree, with no parent statement or stmt_deps changed.

Changed during second reading: replaced the vacuous component split by Čech-criterion
and general derived-sections reductions; repaired docs, metadata, searches and report;
removed unused direct proof imports and the linter-producing partial sorry proof.
