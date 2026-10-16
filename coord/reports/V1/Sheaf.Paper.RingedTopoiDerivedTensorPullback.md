## What changed

Repair of reviewer X-9eb8b point B2: restored `lean.note` verbatim from the reviewed
baseline, ending "The old module is imported and its declaration remains available; no
mathematical statement or other node field is changed." No other node field is changed by
this repair. The retirement remains documented in this report and the change record.
The sandbox node preserves the shared baseline's subsequent attachment to
`Sheaf.Paper.ProEtaleCanonicalTensorPullback` and its current proof route; these
concurrent updates are not rolled back by the repair.

Retired the unused `SheafOfModules.ringedTopoiDerivedTensorPullback` declaration from the
item module. A whole-library `rg` search and `tools/downstream.py --uses` find no use of
that name outside its own declaration. Its node already attaches to the stronger
`SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback` in
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback`.

The item module remains as an import shim: its three public imports and module docstring
are retained. Removed its three unused proof-only imports. No other Lean file changes.
In particular, U1's canonical module is untouched. The node's `lean.note` is restored to
the baseline as requested by B2; its canonical attachment, statement and proof route stay
unchanged by this repair.

Change record: `coord/changes/withdraw-unused-derived-tensor-pullback.md`.

## Proved and sorry left

Proved 0 of 1 original holes; pruned the unused hole
`SheafOfModules.ringedTopoiDerivedTensorPullback`. This is retirement of an unused
declaration, not a proof or a decomposition. Added 0 holes. The item module leaves no
`sorry` and no declaration. No other file's holes are modified or introduced.

The stronger, already-existing canonical comparison remains the obligation of node
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`; its proof is not claimed here.

## No longer needed

Retired declaration: `SheafOfModules.ringedTopoiDerivedTensorPullback`.
Removed proof imports: `Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.Algebra.Homology.KFlatTelescopeClosure`, and
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.

The item module remains needed as an export shim for its current direct public importer,
`Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`. It is not claimed pruned as a module.
This importer does not invoke the retired theorem. Its import is preserved. The canonical
module is not a current direct importer; the earlier report incorrectly listed it.

No DAG node is deleted or detached. The existing node already points to the canonical
module, which retains its K-flat, tensor-descent, module-adjunction and ordinary-tensor
route. No further module or node is claimed pruned. The unit's statement and all three
realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The brief describes the old existence-only theorem as an active proof obligation. In the
current library it has no caller, and its DAG node was already reassigned to the stronger
canonical theorem on 2026-10-15. The old theorem is redundant; its module is still needed
for public dependency forwarding. There is no mathematical objection to either statement.
No target statement or target definition changes.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes — pass.** I compared the delivered module with the
   repository version and checked the whole-library references. The only declaration change
   is the explicitly recorded retirement of `SheafOfModules.ringedTopoiDerivedTensorPullback`;
   public imports and all other signatures remain unchanged.
2. **Proof validity — pass.** The delivered import shim compiles with `lcompile.py`, contains
   no declarations, `sorry`, or forbidden constructs, and introduces no axioms. The canonical
   theorem attached to the item node remains in its existing module and is unchanged.
3. **Split statements and searches — pass.** No split-off statement or new node is added.
   The retired theorem has no callers outside its own old declaration, and the existing node
   continues to point to the stronger canonical theorem rather than restating the retired API.
4. **Pruning and route — pass.** The three proof-only imports are removed and documented as
   unused. The public imports are retained because downstream modules use this file as an
   export shim. The unit's realized route and canonical proof dependencies are unchanged.
5. **DAG agreement — pass.** The node's statement, proof, dependencies, and canonical Lean
   attachment are unchanged; only its note records the retirement. No new node or unit route
   is required.

I changed only this second-reading report section after review; no Lean proof or statement was
   altered.

## Second reading by V1

1. **Signatures and accidental changes — pass.** I diffed the delivered module against the
   shared repository version. The only Lean interface change is the declared retirement of
   `SheafOfModules.ringedTopoiDerivedTensorPullback`; the three public imports, module
   documentation, and all other files are unchanged. The DAG node was checked against the
   shared version and retains its current canonical module attachment and proof route.
2. **Proof validity — pass.** I compiled the item with `lcompile.py` and compiled the sandbox
   import set with `lcompile.py --all`; both succeed without errors. The shim contains no
   declarations, `sorry`, axioms, unsafe code, or other forbidden constructs. The retired
   theorem is not claimed as proved, and no new theorem or definition is introduced.
3. **Split statements and searches — pass.** No split-off statement or node was added. A
   whole-library search and the downstream-use check found no caller of the retired theorem
   outside its own declaration. The existing node points to the stronger canonical theorem,
   so the retirement does not restate or weaken the target.
4. **Pruning and route — pass.** The three proof-only imports removed from the shim are unused
   after retirement and are listed under `## No longer needed`. The public imports remain
   because `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback` exports through this module.
   The unit record and all realized proof steps remain unchanged.
5. **DAG agreement — pass.** The node's statement, dependencies, proof steps, and
   `proof_origin` agree with the current canonical Lean declaration. No node fields were
   changed by this reading; the retirement is recorded only in the change record and this
   report.

I changed only this report by adding the required second-reading section; no further Lean or
DAG edits were needed.
