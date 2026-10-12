## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.exists_open_etale_subsheaf_final_factorization`.
The proof forms the supremum of the open images of all étale objects carrying a section,
uses `Scheme.Hom.isOpenMap` for étale morphisms, and proves the converse by pulling back
those objects and gluing their sections with `Presheaf.IsSheaf.amalgamateOfArrows`.
Monicity gives subsingleton section types. The proof-only imports
`Mathlib.AlgebraicGeometry.PullbackCarrier` and `Mathlib.CategoryTheory.Sites.Limits`
were checked and removed; the latter APIs are re-exported by the remaining imports.

## Proved and sorry left

The declaration `exists_open_etale_subsheaf_final_factorization` is proved. No `sorry` remains
in the delivered module, and no new theorem or `sorry` was added.

## No longer needed

The proof does not import or use a separate support or stalk lemma. The DAG dependency
`lem-weil-pbc-etale-morphism-open-map` is realized directly by Mathlib's
`Scheme.Hom.isOpenMap` and its étale instances; it remains a proof dependency. No Sheaf
dependency module is needed.

## Second reading by S3

1. **Declarations unchanged.** Compared the delivered module with the repository version;
   the definition and theorem signatures are byte-for-byte unchanged. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`. An axiom probe reports only
   `propext`, `Classical.choice`, and `Quot.sound` for every declaration. Verdict: pass.
3. **Statements and searches.** The theorem is exactly the node statement after unfolding
   `etaleSubsheafFactorization`; the private helper is a strict subsingleton step, not a
   restatement. Local Mathlib searches found no existing support-open theorem. Verdict: pass.
4. **Route and pruning.** The unit route is preserved: the proof uses the open-map Mathlib
   match and the sheaf gluing API. Both tested redundant proof-only imports were removed;
   `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` remains necessary for `isOpenMap`.
   Verdict: pass.
5. **DAG agreement.** The existing node's `proof`, `proof_deps`, and `proof_origin` agree
   with the implementation; no split-off nodes or change records are needed. Verdict: pass.

Changed only the proof and its imports, and corrected this report to record the actual
pruning.

## Where the brief, the DAG or earlier work was wrong

The brief's planned construction is mathematically correct, but the implementation can use
Mathlib's `ofArrows_mem_smallEtaleTopology_iff`, pullback carrier surjectivity, and sheaf
amalgamation directly. No statement was changed.
