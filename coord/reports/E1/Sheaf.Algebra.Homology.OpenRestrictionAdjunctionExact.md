## What changed

Proved `AlgebraicGeometry.open_restriction_adjunction_exact` in
`Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`, with its signature unchanged.
The shorter route specializes the existing
`SheafOfModules.localizedModule_adjunction_exact` to the category of opens of X.
The proof establishes that the covering precoverage generates the original
Grothendieck topology, then transports the general theorem to X.sheaf. The ring
sheaf, restriction and extension-by-zero functors agree definitionally with the
ones in the item. No definitions, instances or public imports changed.

Added the proof-only import `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`.
Updated the item's node proof, proof dependencies and proof origin to this route.
The unit `sk-thm-picard-duality` has no realized statement or step pointing to this
node; the higher route still obtains the exact adjunction it requires.

Local single-file compilation passed without warnings. The import-direction check
confirmed the added dependency is acyclic. The final delivery dry run also checks
server compilation and preflight.

The general ringed-site construction is Stacks [03DI](https://stacks.math.columbia.edu/tag/03DI),
and its exactness is [03DJ](https://stacks.math.columbia.edu/tag/03DJ).
The local literature checkout is absent on this machine, so these two official
source pages were read online. The existing theorem's statement includes all five
required conclusions and uses the same concrete functors.

## Proved and sorry left

Proved `AlgebraicGeometry.open_restriction_adjunction_exact`
(node `lem-sc-derived-open-restriction-adjunction-exact`): 1 of 1 original sorries.
No sorry remains in the delivered module; no new theorem or sorry was added.

The imported existing theorem `SheafOfModules.localizedModule_adjunction_exact`
(node `lem-pur-site-restriction-module-adjunction-exact`) is still sorry in the
library. It is the next dependency, rather than a newly created restatement.
Thus this delivery closes the item's proof from an existing broader statement;
it does not claim the full transitive axiom closure is sorry-free.

## No longer needed

Removed all three former proof-only imports:

- `Sheaf.Algebra.Homology.ModuleStalkExact`
- `Sheaf.Topology.AbelianOpenExtensionByZeroStalks`
- `Sheaf.Topology.PresheafModuleStalkFunctor`

Removed these nodes from the item's proof dependencies:

- `lem-weil-pbc-module-stalk-exact`
- `def-weil-pbc-exact-sequence`
- `def-weil-pbc-module-stalk`
- `lem-weil-pbc-stalk-sheafification-space`
- `lem-sc-topological-extension-by-zero-stalks`

The module-sheafification and extension-presheaf definitions remain needed to
identify the concrete functors. Both existing public imports remain needed by
the statement. The removals concern this item's proof; no claim is made that
other targets cannot reach these modules by other paths.

## Where the brief, the DAG or earlier work was wrong

The old stalkwise plan is valid but unnecessary: the already stated localized
ringed-site theorem includes this ringed-space case. Its hypotheses hold for the
covering precoverage of the topology of opens, and the proof supplies the
non-definitional topology equality explicitly. No hypothesis on X or U is added,
including in the empty-open or whole-space cases.

The existing declaration docstring describes the old stalkwise plan; the proof's
inline comments and the updated DAG record the actual shorter route. The general
site node is used as a tool from another unit because it already states exactly
the general module adjunction and exactness required here. No unit statement or
unit proof step is bypassed.


## Second reading by E1

1. Compared the delivered Lean module and node with the repository versions.
   The existing theorem signature is byte for byte unchanged; no definition,
   instance, public import, or target statement changes. The only module changes
   are its proof and proof-only imports. Verdict: pass.
2. Independently compiled the module with lcompile.py, without errors or warnings.
   Scanned for sorry and forbidden declaration mechanisms: none occur. A scratch
   copy with `#print axioms AlgebraicGeometry.open_restriction_adjunction_exact`
   reports exactly propext, Classical.choice, Quot.sound, and sorryAx. The latter
   is expected from the existing open localized-module theorem, as disclosed
   above. No new axiom or hollow definition is introduced. Verdict: pass with
   that existing transitive proof obligation explicitly retained.
3. No statements were split off or added, so no new nodes, duplicate helpers,
   or disguised restatements require review. Read the imported theorem in full:
   it is genuinely more general (arbitrary suitably covered small sites), and
   all five conclusions use the same functors. Its hypotheses hold for the
   topology-of-opens precoverage. Empty U, full U, and empty X require no extra
   assumption or case split. Verdict: pass.
4. Read the specialization and topology transport from the target downward;
   the two topology inequalities use the existing Mathlib lemmas directly.
   Searched lean/Sheaf for localized adjunction and extension-by-zero routes;
   found no shorter already proved generic ringed-space theorem. The three
   removed imports and all five removed proof dependencies are listed under
   No longer needed. Both public imports supply the statement's constructions;
   the new import is proof-only. Checked sk-thm-picard-duality.json: its realized
   fields are statement=[] and steps=[[]], so this below-unit reduction bypasses
   no recorded realized node. Verdict: pass.
5. Checked that only proof, proof_deps, and proof_origin changed in the node,
   and that proof_deps is exactly the union of step uses. The recorded topology
   equality, theorem specialization, and definitional identification agree with
   the Lean proof. No new node is needed. Verdict: pass.

Second reading changed only this report, adding the independent checks and
axiom result. The proof and DAG required no repair.
