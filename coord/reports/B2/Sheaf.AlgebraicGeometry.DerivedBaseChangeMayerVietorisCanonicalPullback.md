## What changed

Repaired reviewer X-9a7b8 point 6: restored
`lem-pc-derived-mayer-vietoris-direct-image-boundary` to the canonical pullback node's
`proof_deps`, matching proof step 2 and the use of `schemeMV_directImage_boundary`.

Applied the returned-delivery repair. The copied helper block was removed, and the proof-only
import was changed to `import all Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial`.
The canonical boundary naturality step rewrites with `canonical_boundary_eq` and then reuses
`canonicalMV_spec`. The public target statement is unchanged.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.mvCanonicalBoundary_pullback`.
Also proved the new, strictly smaller single-open identity
`AlgebraicGeometry.derivedBaseChange_open_transpose`.
Holes added: none. Holes left in either delivered module: none.
This is one of one original holes closed, not a decomposition into postponed statements.

## No longer needed

The local copied helper declarations and their supporting proof machinery are no longer needed:
`derived_map_surjective_local`, `computation_naturality`,
`open_comparison_naturality_local`, `concrete_map_local`, `representativeBoundary`,
`representativeBoundary_naturality_local`, and `transport_boundary_square_local`.
The import `Sheaf.AlgebraicGeometry.DerivedMayerVietorisDirectImageBoundary` is no longer needed;
its role in the earlier delivery is replaced by the proof-only `all` import of
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial`.
The direct-image boundary node remains needed by `schemeMV_directImage_boundary`; only its
redundant direct import was removed.


Compared with the repository baseline, the actual removed direct import is
`Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle`.
Every old proof dependency absent from the new target node's `proof_deps` is:

- `lem-pc-derived-functor-termwise-split-ses-triangle`
- `lem-pc-kinjective-mayer-vietoris-exact`
- `lem-sc-kinjective-quasi-iso-comparison`
- `lem-weil-pbc-complex-ses-triangle`
- `def-pc-rf-mv-base-change-components`
- `lem-pc-ringed-spaces-derived-pullback-composition`
- `lem-sc-derived-k-injective-restrict-open`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`

These are no longer direct steps of this node's proof; some remain transitive
requirements of reused declarations. No whole-library unreachability is claimed.
The second reading additionally removes the duplicate private
`precomp_rightAdjoint_injective` from the new module and reuses the existing one
through `import all Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenRestriction`.
Its imports of `DerivedBaseChangeOpenUnit` and `DerivedOpenRestrictionUnitIso`
are redundant through that import and are removed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery retained copied helper declarations and claimed that an auxiliary witness
made them distinct. The reviewer correctly rejected that duplicate-statement workaround. This
repair removes the copied block and uses the existing `canonicalMV_spec`; the DAG first proof
step and dependencies now record that route.

## New nodes

The existing split node `lem-pc-derived-base-change-open-transpose` is used through
`Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenTranspose`; its signature and proof are retained, with the copied generic helper replaced by reuse.
The proof-command change record `coord/changes/mvCanonicalBoundaryPullbackProofCommands.md`
remains part of this repaired delivery.

## Earlier second reading (a previous round; superseded)

The repaired module compiles. Its public theorem statement and declaration signatures are
unchanged. The helper block is absent, `canonicalMV_spec` is the reused naturality dependency,
and the DAG proof text and dependency list match the implementation.

## Earlier second reading (a previous round; superseded)

1. The delivered module was diffed against the repository version. The public theorem signature is unchanged; only proof-local helpers, proof imports, and proof commands differ. Verdict: pass.
2. The module compiles with `lcompile.py`, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the proof uses only existing declarations and proved private helpers. Verdict: pass.
3. The canonical boundary pullback statement is unchanged and the split open-transpose statement is a strict single-open mate identity, documented by its node and source. No duplicate target restatement was found. Verdict: pass.
4. The proof follows the unit route through canonical Mayer--Vietoris naturality, direct-image boundary comparison, and the single-open transpose lemma. The proof-only `all` import is required; removed copied helpers and the obsolete boundary import are pruned. Verdict: pass.
5. The DAG proof and `proof_deps` match the implemented route, including `lem-pc-derived-base-change-open-transpose`; the unit realization is preserved. Verdict: pass.

Changed during this second reading: no Lean declarations or statements. The report records the checks above; the repaired proof already removed the copied helper block and retained only the canonical naturality route.

## Second reading by B2

1. Compared both delivered files with the repository baseline. The original public
   theorem signature is byte for byte identical (checked by extracting the text
   from `theorem` through `:= by`). Its public import and definitions are unchanged.
   The new module has no existing repository counterpart. Verdict: pass.
2. Compiled both modules with `lcompile.py`; scanned for forbidden declarations and
   holes. Scratch copies print the axioms of both public theorems. All helpers are
   proved, and no definitions or arbitrary existence witnesses are introduced.
   Verdict: pass within the open upstream dependency closure.
3. The new theorem is a boundary-free, shift-free single-open identity, strictly
   part of the argument, and is itself proved. Checked empty/top opens, zero maps,
   and repeated covering opens: the same adjunction equations apply without a
   nonempty or distinctness assumption. Independent Loogle and LeanFinder searches
   found generic adjunction naturality but no exact derived open mate theorem;
   repository search found a verbatim copied private cancellation helper, now
   removed and reused from its original module. Verdict: pass after repair.
4. Read the proof from the target down: transposition reduces it to existing
   canonical boundary naturality, direct-image boundary comparison, and the proved
   single-open identity. The remaining imports supply signatures or used proofs.
   The report now lists every old dependency removed from the target proof plan.
   `dag/units/sk-thm-picard-semicon.json` has empty `realized.statement` and step
   lists; no realized node is bypassed or changed. Verdict: pass after repair.
5. Compared node proof steps and dependency unions with the Lean calls. The
   direct-image boundary node is present, and the single-open node lists its
   three unit identities and construction dependencies. The new node has source,
   searches, creation, blueprint, chapter, unit, and Lean records. Updated its
   Lean statement to the actual multiline signature and its proof text to record
   reuse of the existing helper. Verdict: pass after repair.

Changed in this reading: removed one copied private helper and two redundant
proof imports, added the proof-only `all` import needed to reuse that helper,
corrected the new node's Lean statement/proof description, and completed the
hole accounting and baseline pruning list. No existing statement changed.

Axiom results: scratch `#print axioms` for both public theorems reports exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is inherited
from open declarations below this delivery; neither delivered file has a hole.
Thus the original hole is closed locally, while full axiom closure remains open.
The delivery tool also probes every declaration, including private helpers.
