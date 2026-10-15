## What changed

Removed the two top-level private helper theorems from the delivered module. Their proofs are now local `have` declarations inside `CategoryTheory.truncationCouple_exact`, specialized to the target category `B`, while the target theorem continues to use `CategoryTheory.truncation_raw_exact` from `Sheaf.CategoryTheory.TruncationRawExact`.

## Proved and sorry left

`CategoryTheory.truncationCouple_exact` is proved with no `sorry` left. No new theorem or node was added.

## No longer needed

The proof removes the proof-only imports `Sheaf.CategoryTheory.ExactCouple`,
`Sheaf.CategoryTheory.KInjectiveBridge`, `Sheaf.CategoryTheory.KInjectiveComputes`,
`Sheaf.CategoryTheory.TruncationTriangle`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
and `WeilConjectures.Algebra.Homology.ExactCouple.Basic`. The public imports
`Sheaf.CategoryTheory.TruncationCouple` and
`Mathlib.Algebra.Homology.ShortComplex.Exact` remain required by the statement,
and `Sheaf.CategoryTheory.TruncationRawExact` supplies the theorem used by the
proof. The old proof dependencies
`lem-weil-pbc-truncation-triangle`, `lem-weil-pbc-derived-direct-image-triangulated`,
`def-sp-kinjective-bridge`, `lem-sp-kinjective-computes`,
`lem-sp-grothendieck-enough-injectives`, `lem-sf-derived-homology-long-exact`, and
`def-sp-exact-couple` are no longer used; the node now records only
`lem-sp-truncation-raw-exact` and `def-sp-truncation-couple`.

## Where the brief, the DAG or earlier work was wrong

The returned delivery still declared `exact_transport_local` and `reindex_hom_local` as top-level theorems. The import-prune check correctly rejected these because their statements duplicate private helper theorems already present in `Sheaf.CategoryTheory.TruncationRawExact`, even though the names differed. The repair keeps the transport arguments as local proof terms and reuses the existing public theorem `truncation_raw_exact`.

## New nodes

None.

## Second reading by C4

1. **Delivered module versus repository.** I compared the delivered module with
   the repository version. The theorem signature and docstring are byte-for-byte
   unchanged; only proof-only imports and the proof body changed. Verdict: pass.

2. **Compilation and proof status.** `lcompile.py` compiles the module without
   errors or warnings. The axiom scratch file reports only `propext`,
   `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.

3. **Statements and duplicate checks.** The target statement is unchanged. The
   proof uses the existing `CategoryTheory.truncation_raw_exact` declaration and
   local transport facts; no new public statement or node is introduced. Searches
   for the helper patterns found only the existing Mathlib transport lemmas and
   the raw theorem. Verdict: pass.

4. **Pruning and route.** The proof is a direct reduction to
   `lem-sp-truncation-raw-exact`, then unfolds the truncation-couple definition and
   transports the two index-equality cases. The six unused proof-only imports and
   seven unused old proof dependencies are listed above, and the node's `proof`,
   `proof_deps`, and `proof_origin` now match this route. The unit remains
   `sk-thm-properbasechange`; its realized fields are unchanged. Verdict: pass.

5. **DAG and report consistency.** The copied item node changes only stage-3-owned
   proof fields, with the dependency union matching its three proof steps. No
   split-off theorem, node, or change record is needed. Verdict: pass.

I changed the report to enumerate the complete pruning, updated the item node to
record the actual raw-exactness reduction, and retained the compiling proof
unchanged after that metadata repair.
