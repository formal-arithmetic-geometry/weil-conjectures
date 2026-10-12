## What changed

Completed the proof of `AlgebraicGeometry.etaleCoproduct_embedding_points` directly.
The proof constructs an equivalence between geometric points of the coproduct and the
sigma type of algebra embeddings, proves bijectivity by coproduct factorization, and
checks equivariance under the Galois action. No new imports were required.
The second reader removed the redundant explicit Limits import.

## Proved and sorry left

`AlgebraicGeometry.etaleCoproduct_embedding_points` is proved. No `sorry` remains in the
delivered module. Closed hole: `AlgebraicGeometry.etaleCoproduct_embedding_points`.
Holes added: none.

## No longer needed

Removed explicit import: `Mathlib.AlgebraicGeometry.Limits`, already available
through the retained public import. No library module is pruned: Limits remains
reachable transitively. The repository node already had empty `proof_deps`, so
there are no old proof-dependency nodes to list as pruned. Previously drafted
intermediate action/equivalence artifacts were never repository dependencies and
are not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt described the proof as a composition of two intermediate theorems,
but the target module already contains a complete direct proof. Those intermediate
artifacts were removed from this delivery.

## Earlier second reading (a previous round; superseded)

1. The delivered declaration has the same statement as the repository version byte for
   byte; the proof only constructs the equivalence and its equivariance, so no visible
   interface was weakened or strengthened. Verdict: pass.
2. The module compiles cleanly with `lcompile.py`; it contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`. Its declaration depends only on
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. No split-off statements were added. The direct construction is elementary and does
   not duplicate a Mathlib or existing library theorem. Verdict: pass.
4. The proof uses the coproduct and spectrum API directly. `Mathlib.AlgebraicGeometry.Limits`
   is proof-only and is now a plain import; no other import was removable. The stale
   intermediate equivalence/action dependencies were removed from the node metadata.
   Verdict: pass.
5. The node proof now records the direct construction and has no nonexistent proof
   dependencies; the unit record is unaffected because this node has no realized unit
   step. Verdict: pass.

Changed the Mathlib import visibility, updated the node's proof/proof_deps metadata to
match the actual proof, and added this second-reading record.

The import visibility change is recorded in `coord/changes/EtaleCoproductEmbeddingPoints-import.md`.


## Second reading by J1

1. Compared the delivered Lean file with the repository using `diff` and checked
   the existing theorem signature byte for byte: identical. No definition or
   declaration visibility changed. The explicit import removal is recorded in
   `coord/changes/EtaleCoproductEmbeddingPoints-import.md`; its declarations are
   already publicly available transitively. Verdict: pass.
2. Compiled the delivered theorem locally and a scratch copy with `#print axioms`:
   only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, forbidden trust
   escape, or hollow definition occurs. The inverse equivalence chooses from a
   proved bijection, whose inverse is uniquely determined. Verdict: pass.
3. No new statements or split-off holes exist. Read the bijection and equivariance
   arguments in full. Empty indexing gives no point in the coproduct and thus no
   source geometric point; singleton indexing gives the affine correspondence.
   No finiteness assumption is smuggled into the proof. Verdict: pass.
4. Searched Mathlib's coproduct and residue-field API, the local étale modules,
   and Loogle with `"sigmaMk"`. The existing `sigmaMk`, `sigmaι_eq_iff`, open-immersion
   lift and `Spec.homEquiv` are the direct route; no exact replacement was found.
   Removed the redundant Limits import after a successful scratch compile.
   Compiled the unchanged direct importer `EtaleFieldPointFunctorEssSurj` against
   the delivered module. Old `proof_deps` is empty; no module pruning is claimed.
   The node is absent from every unit's realized fields; inspected `sk-prop-h2`,
   whose realized fields are empty, so its route is unchanged. Verdict: pass.
5. Compared both node records: only `proof` and `proof_origin` differ; the three
   recorded steps match construction, bijectivity, and equivariance. Empty
   `proof_deps` is correct, with the geometric action retained as a statement
   dependency and through the public functor import. No new nodes. Verdict: pass.

Changes in this second reading: removed the redundant explicit Limits import,
updated its change record, and corrected the report to count one hole closed,
zero holes added, and no library modules pruned. The Lean proof was left intact.
