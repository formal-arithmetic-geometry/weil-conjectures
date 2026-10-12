## What changed

Proved `AlgebraicGeometry.Scheme.Modules.etaleTensorUnitRestriction_equation` in
`Sheaf.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation`, preserving its signature,
visibility, docstring, and both public imports. No definitions or interfaces changed.

The proof follows the existing node's adjunction calculation. Three local calculations
identify normalized composition followed by the structure map, compute sections of
unit naturality, and transport along the site-arrow relation. The final proof evaluates
the resulting equality of additive homomorphisms at the supplied section.

The composition and transport calculations are proved directly here by the adjunction and
unit equations. The sections calculation is first proved for an arbitrary left adjoint and
its characterized structure map, then
specialized to tensor pullback. A generic top-open restriction identity prevents the
compiler from unfolding the concrete tensor construction while rewriting `map_id`.
All five private helpers are proved; none adds a hole or new public API.

Local compilation passed without errors or warnings in 7.3 seconds. The argument has
no nonemptiness, characteristic, or affine assumptions; inverse image of top is top
also for the empty scheme. Equality elimination handles identity and composite arrows.

Searches: LeanFinder for tensor pullback structure-sheaf section restriction returned
structure-sheaf comap and scheme pullback lemmas, with no direct result. Loogle for
`unitToPushforwardObjUnit` returned its definition, its adjunction characterization,
and its evaluation lemma. Mathlib grep found the same declarations in PullbackFree.
Local `rg` found the proved lifted naturality theorem and its private calculations.
Specializing its lifted conclusion directly led to costly section conversions, so the
unlifted adjunction calculation is proved directly here instead.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.etaleTensorUnitRestriction_equation`
(node `lem-sc-etale-tensor-unit-restriction-equation`).

No sorries remain in the delivered module. No holes were added or split off.
The private helpers `tensorStructureMap_comp`, `topRestriction_id`,
`structureMapSectionsOfAdjunction`, `tensorStructureMap_sections`, and
`tensorStructureMap_restriction` are all proved.

## No longer needed

None. Both original public imports are needed by the statement and definitions it uses.
The proof keeps the existing DAG dependencies and route. It does not import the lifted
sheaf module `Sheaf.AlgebraicGeometry.EtaleStructureSectionsEquiv`, the sections-sheaf
condition, or quasi-coherent descent: none is needed for this pointwise restriction
identity. Those were not original imports, so no module is claimed as newly pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement correction. The existing proof plan is realized
without new nodes. Direct rewriting on the concrete tensor module exceeded the compiler
time limit; generalizing the section calculation to an arbitrary left adjoint and proving
top-open restriction for an arbitrary module resolves this without changing definitions.

The first worker's dry run was blocked by the delivery tool, before compilation/preflight:
`deliver3.py` line 65 imports `refuse_missing` from `tools/import_cycles.py`, but that
module does not export the name (`ImportError: cannot import name 'refuse_missing'`).
The worker has neither modified nor bypassed the tool. The sandbox proof and report
were ready for a retry. The second reader retried the tool successfully: the import mismatch has been repaired externally.

## Earlier second reading (a previous round; superseded)

The proof was reread after local compilation. The public theorem statement and
imports are unchanged; all five helper calculations are private and proved. The
module compiles successfully with `lcompile.py`, and no new sorry or axiom is
introduced.

Change record: `coord/changes/etale-tensor-unit-restriction-equation-proof.md`.

## Earlier second reading (a previous round; superseded)

1. **Unchanged public contract — pass.** Compared the entire delivered module with
   the repository using `diff -u`, and compared the existing theorem's signature
   byte for byte. Its signature, visibility, docstring and two public imports are
   identical. Only proved private helpers, proof configuration and the proof body
   are added. No definition or existing statement changes; no forced adaptations.
2. **Kernel proof — pass.** Independently compiled the delivered module using
   `lcompile.py`: exit 0, no warnings or errors. Compiled a scratch copy with
   `#print axioms` for all five private helpers and the public theorem: each uses
   only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Checked the
   source for forbidden declarations and attributes: none. No new definitions,
   data chosen from existence, or holes occur.
3. **Split statements and edge cases — pass.** No split-off statements or new
   holes. Read every helper: composition is derived by adjunction injectivity;
   section compatibility is unit naturality plus the defining structure-map
   equation; equality transport eliminates the site relation. The top-open map
   is the identity for every scheme, including the empty scheme. The proof has
   no extra hypotheses and applies to identity and composite arrows. Independent
   Loogle search for `"homEquiv_naturality"` returned the standard adjunction
   naturality lemmas, which supply steps rather than the whole equation. Local
   and Mathlib searches found the already-noted lifted naturality theorem and
   private calculations; none supplies an accessible unlifted direct theorem.
4. **Shortest route, imports and unit — pass.** Read the proved lifted theorem
   `etaleStructureSectionsEquiv_naturality` and its helpers. The delivered direct
   calculation avoids its sheafification and ULift conversions and keeps only
   the two original public imports, both needed by the theorem's signature.
   There are no unused old proof dependencies: the normalized restriction data
   and the adjoint structure-map characterization are both used. No modules
   are newly pruned. Read `dag/units/sk-prop-cd.json`: its realized fields are
   untouched; this below-unit restriction calculation bypasses no unit step.
5. **DAG agreement — pass.** Read the item's node and both proof dependencies,
   their Lean declarations and definitions. The existing node already describes
   precisely this composite-adjunction, transport and top-section calculation;
   its `proof`, `proof_deps` and `proof_origin` need no change. There are no new
   nodes or statement changes.

Second reading changed no Lean: the proof is correct as delivered. Added this
review and corrected the report's obsolete tool-blockage wording. The delivery
is one hole closed out of one, zero holes added and zero split off. The private
helpers remain proved implementation details; the supplied change record
explains the static check's command/interface classification.

## Second reading by A3

1. **Public contract — pass.** `diff` against the repository shows that the theorem's
signature, visibility, docstring, and two public imports are unchanged. The added
declarations are private proof helpers, so no exported interface changed.

2. **Proof and axioms — pass.** `lcompile.py` compiles the module without errors or
warnings. The source has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`; the proof uses only the permitted adjunction and category-theory
lemmas. The existing scratch axiom check reports no `sorryAx` for the theorem or its
five helpers.

3. **Statements and edge cases — pass.** No statements were split off and no holes were
added. The helper equalities are direct consequences of adjunction unit naturality,
the structure-map characterization, and equality transport. The top-open restriction
is the identity, including for the empty scheme; identity and composite arrows require
no extra hypotheses.

4. **Route, imports, and pruning — pass.** The proof follows the node's composite
adjunction calculation and retains the unit route. Both public imports are needed by
the theorem or its definitions, and no unused import or old proof dependency was
removed. The direct unlifted calculation is shorter than passing through the lifted
sections equivalence.

5. **DAG agreement — pass.** The node statement and proof dependencies match the Lean
declaration and proof. The unit record is untouched, and no new node or change record
is needed beyond the existing proof-only record.

Second reading changed only this report section; no Lean source, statement, definition,
or DAG file was changed.
