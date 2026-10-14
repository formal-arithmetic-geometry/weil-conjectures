## What changed

Repaired reviewer X-5b556 point A by completing the review packet in
`coord/changes/affineModelStageHomEquation-import-pruning.md`. It now embeds 29
unchanged original source and node snapshots with SHA-256 hashes, including the
current original `AffineModelComparisonOfBottomModels`, the cited dependency
sources and records, and the complete `affineModel_scalarConjugation_nat` proof.
The original direct importer compiled unchanged against the delivered item overlay
in 7.6 seconds with no warnings. Every snapshot hash matches the repository.
This repair changes documentation only; no dependency source is adapted.

Proved `AlgebraicGeometry.affineModelStageHomEquation_of_coherent_objects` from the
supplied object triangles and the already proved `affineModel_scalarConjugation_nat`.
The existing statement is unchanged. Five private helpers provide exact-value
isomorphism pinning and equations for the named Hom transports; all are proved.
The pinned data are determined by a proved equality to the supplied isomorphism,
not selected from an unproved existence assertion. No shared definition is changed.

The direct application exceeded the kernel heartbeat budget. The local equations
keep the stage arrow and the comparison construction separate during conversion.
This implementation compiled in 15.5 seconds before import pruning, with the
60-second limit unchanged. The node proof records the actual calculation.
The public import-pruning record is
`coord/changes/affineModelStageHomEquation-import-pruning.md`;
the sole direct importer retains the removed module through its limit-Hom import,
and the textual import-pruning check passed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affineModelStageHomEquation_of_coherent_objects`
(node `lem-pc-affine-model-stage-hom-equation-of-coherent-objects`).
No sorry remains in the item; no holes were added or split off.
The five private helpers are `exists_iso_value`, `pinnedIso`, `pinnedIso_eq`,
`homMap_pinned` and `stageMap_asHomMap`; all are sorry-free.

## No longer needed

Removed the unused public import
`Sheaf.AlgebraicGeometry.AffineModelComparisonDataFromHomEquations`, replacing it
with the statement dependency `Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons`.
This proof does not use the constructor theorem
`affineModelComparisonData_of_hom_equations` or its node
`lem-pc-affine-model-comparison-data-from-hom-equations`.
That module remains needed elsewhere; this is local import pruning, not a claim
that it leaves the entire targets' closure.
All three planned proof-dependency nodes are retained. The existence theorem for
coherent objects is not applied because coherent objects are supplied as a parameter.
The unit's realized statement and steps are empty; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned packet omitted original sources needed on the reviewer machine for
direct-importer compilation and dependency comparison. Point A is repaired by
embedding the complete originals in the delivered change record, so they travel
with the review packet even when the reviewer clone lacks those files.

No statement error was found. The named scalar-conjugation API suffices
mathematically, but direct conversion unfolds the explicit comparison construction
and causes kernel timeouts. The proved local transport equations and equal pinned
comparison avoid that cost without changing any shared definition or statement.
The imported modules initially awaited publication in the last green build;
compilation proceeded once the normal refresh supplied them.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The theorem
   statement and all existing declaration signatures are byte-for-byte
   unchanged; only the proof, helper lemmas, author line, and documented import
   pruning differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The
   file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
   `extern`. The pinned helper is determined by an explicit equality, and the
   five helpers are fully proved. Verdict: pass.
3. Checked the split-off statements and DAG node. No new public theorem or
   node was added, and the existing node's statement remains unchanged. Its
   proof and proof dependencies now match the calculation in the module.
   Verdict: pass.
4. Reviewed the proof route and imports. The route uses the existing coherent
   object comparisons and scalar conjugation theorem, with local definitional
   transport equations to avoid expensive conversion. The removed constructor
   import is recorded in the change record; no other import was removed.
   Verdict: pass.
5. Checked the unit record and report against the implementation. The unit's
   realized route is unchanged, and the documentation identifies the exact
   theorem proved and the absence of remaining holes. Verdict: pass.

Changed nothing during this second reading; the delivered proof and import
pruning were already correct.

## Second reading by U2

1. Compared the sole delivered Lean module with the repository original, and
   mechanically compared the entire existing theorem signature before `:= by`:
   byte-for-byte identical. All universes, diagram/cocone parameters, affine and
   derived-category instances, arbitrary chain map and conclusion are retained.
   No shared definition or external module is adapted. The public import change
   is explicitly declared in the change record. Recomputed all 29 embedded
   snapshot hashes and compared their complete bytes with the repository: all
   match. Verdict: pass.
2. Compiled the item with `lcompile.py`, including the sandbox output refresh:
   success without warnings (15.3 seconds on the refresh). Compiled a scratch
   copy of the complete source with `#print axioms` for all five private helpers
   and the original theorem. The existence helper has no axioms, the pin and its
   equality use only `Classical.choice`, and both transport helpers and the
   theorem use only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
   Text scan finds no sorry or forbidden declaration/attribute. In particular,
   `pinnedIso` chooses from the proved assertion `t = e`, which determines its
   exact value; it does not select arbitrary data from an unproved existence.
   Verdict: pass.
3. No split-off statement, new public theorem, new node or new hole exists.
   Read each private helper: existence is witnessed by the supplied isomorphism,
   its equality is `choose_spec`, Hom transport rewrites by that equality, and
   stage transport is definitional. These arguments cover identity arrows, zero
   complexes/rings, and coincident objects without additional assumptions. The
   full induced two-label category retains arbitrary maps between coincident
   models. Verdict: pass.
4. Read the existing scalar-conjugation theorem and its naturality, scalar
   reassociation and inverse-cancellation proofs in
   `AffineModelCoherentObjectComparisons`, and the scalar-extension and Hom
   transport definitions. The delivered proof supplies exactly the two
   `m.hstage` triangles and the full natural comparison `m.θ`; it never applies
   the still-open coherent-object existence theorem. A fresh search of the
   affine-model conjugation API confirms the existing theorem is the direct
   route, also used by the limit-Hom sibling. The sole import is a genuine
   statement dependency. The removed constructor import and its unused node
   are reported; all three original proof-dependency nodes remain used. The
   unit `sk-thm-picard-semicon` has empty realized statement and step lists, and
   this local naturality calculation bypasses no unit route. Compiled the
   unchanged sole direct importer `AffineModelComparisonOfBottomModels` against
   the freshly compiled delivered overlay: success without warnings, 7.5
   seconds. Its other imports retain the removed constructor interface.
   Verdict: pass.
5. Compared the delivered and original node JSON: only `proof` and
   `proof_origin` differ. The proof description follows the actual transport
   rewrites and application of `affineModel_scalarConjugation_nat`; its three
   `proof_deps` match the coherent comparisons, scalar-extension definition and
   Hom transport used. The statement, Lean statement record, unit, blueprint
   and statement dependencies are unchanged. The report accurately records one
   original hole closed and zero holes added. Verdict: pass.

Changed only this report by appending the independent second reading and fresh
verification evidence. No proof, signature, import, node or change-record repair
was needed.
