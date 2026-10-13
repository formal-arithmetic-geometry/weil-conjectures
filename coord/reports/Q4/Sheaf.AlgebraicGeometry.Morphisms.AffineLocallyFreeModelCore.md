## What changed

Proved `AlgebraicGeometry.Scheme.exists_affine_locally_free_model_core` with its
signature unchanged. The proof imports the existing finite-presentation extension
module and affine-section finite-presentation theorem.
Repair of return X-16cf1: removed the duplicate private transport theorem.
A proof-only `import all Sheaf.AlgebraicGeometry.PerfectNoetherianCohomology`
makes its existing private `finitePresentation_overEquiv_inverse` available,
and the core theorem applies it directly. No dependency interface is changed.
The node records use of that module's transport helper, not its main cohomology theorem.
The proof applies extension with the ambient structure sheaf and zero morphism,
then composes the restriction comparison, extension isomorphism, and equivalence counit.
The node now records these proof dependencies. No new modules or nodes are delivered.
Import pruning is recorded in `coord/changes/AffineLocallyFreeModelCore-imports.md`.
The sole direct importer already publicly imports Stalk and needs no adaptation.
Validation: the repaired item compiled with lcompile.py in 17.9 seconds,
exit 0, without warnings. The duplicate-statement/import-pruning check passed (exit 0). The delivery
tool rebased onto the current sheaf-dag and printed OK for commit 03b8c5fec3;
only the fresh second reading remains. The final dry run also enables the
server compilation requested by the return entry. Prior second-reading conclusions have been
removed because they apply to the returned proof; a fresh second reading is needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_affine_locally_free_model_core`
(node `new-affine-locally-free-model-core`). One of one item holes closed;
zero holes added or split off. No `sorry` remains in the delivered module.
The existing extension theorem and its own dependencies are used as library results;
this delivery does not claim to close their remaining transitive holes.

## No longer needed

Removed the redundant private import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`, already
publicly imported for the statement. There were no original proof-dependency nodes
or modules to prune. Also removed the duplicate public `Mathlib.AlgebraicGeometry.Modules.Sheaf` import
and unused `Mathlib.Algebra.Category.ModuleCat.Stalk` import. The explicit import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` is unnecessary:
FiniteDescent already exposes it through public imports.
The duplicate private `isFinitePresentation_overEquiv_inverse` declaration is
removed; its proof is now supplied by the existing imported theorem.
No double-dual or boundary-depth construction is needed for this extension-only core;
those belong to the parent depth-two model argument.

## Where the brief, the DAG or earlier work was wrong

The returned delivery overlooked the existing private theorem. Lean's
`import all` permits direct reuse, so no duplicate helper or visibility change
is necessary. The landing refusal is repaired by that reuse.

The original one-step node had no proof dependencies, although finite-presentation
extension is already stated and proved in
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension` (Tag 01PI).
The source Tag 0G41(2) reduces extension to that theorem. Using the structure sheaf
as ambient module and zero morphism instead of the zero ambient module has the same
extension consequence. Finite sections follow from the existing FiniteDescent result,
without building another affine module identification.
The extension theorem is used as a generic tool from another unit, preserving this
unit's extension step. No unit route or target statement changes.
Empty W, W = top, the zero sheaf, and the zero ring require no exclusions: the
compactness, extension, and equivalence statements apply uniformly.

## Second reading by Q4

1. Interface: PASS. Diffed the delivered Lean module and node against the repository.
   The sole existing theorem signature is byte-for-byte identical; no definitions,
   hypotheses, conclusions, or visibility changed. Only its proof and imports changed.
   The public-import pruning has the declared change record; the direct importer
   independently publicly imports Stalk. No target statement changed.
2. Proof: PASS. Compiled the current delivered file and ran the sandbox --all check
   with lcompile.py, exit 0 without warnings. Scanned the delivered module: no sorry,
   axiom, unsafe, opaque, implemented_by, extern, or data definition. A freshly regenerated
   scratch copy prints axioms [propext, sorryAx, Classical.choice, Quot.sound] for
   exists_affine_locally_free_model_core. The reused private transport lemma prints only
   [propext, Classical.choice, Quot.sound]. The remaining sorryAx is transitive library
   debt, not a hole added by this delivery. Existential H is a proof witness, never
   stored as arbitrarily chosen data in a definition.
3. Split statements: PASS (none). No new statements, modules, nodes, or lower holes
   were added. Read the actual extension, affine-sections, and transport statements;
   each supplies precisely the property used. Empty W, W = top, zero P, and the zero
   base ring do not invalidate compactness or the equivalence argument, and no
   nonemptiness or nonzero assumption is hidden in the proof.
4. Route and pruning: PASS. Independently searched lean/ for inverse-equivalence
   finite-presentation transport and locally free extension declarations. The proof
   already reuses the existing private transport lemma rather than duplicating it;
   no shorter complete extension theorem was found. The three added imports are
   proof-only. No old proof_deps exist to prune; all removed imports are reported.
   Read sk-prop-input-spreading and the parent depth-two model node: this is the
   finite-presentation extension subargument, not a replacement for the double-dual
   boundary-depth argument. Its generic extension tool preserves that route.
   The unit's existing empty realized arrays are unchanged; no unit realization is
   removed or claimed to have been supplied by this proof.
5. DAG: PASS. The changed proof steps record compactness, inverse-equivalence
   transport, extension, finite affine sections, and the three-isomorphism comparison,
   matching the Lean proof. proof_deps is their union and proof_origin gives the
   extension source. The cohomology-module dependency explicitly records use of its
   proved private transport helper, not its main theorem. Other node fields and the
   Lean statement record remain unchanged; there are no new-node fields to audit.

Second-reading changes: regenerated the stale scratch axiom probe (which still
contained the removed duplicate helper), recompiled the current sandbox module,
and appended this independent review. No repair of the delivered Lean proof or
DAG was necessary. Closed one item hole, added zero holes, split off zero statements.

The unchanged direct importer also compiled locally against the sandbox overlay,
exit 0 without warnings (52.5 seconds). It publicly imports Stalk independently.
