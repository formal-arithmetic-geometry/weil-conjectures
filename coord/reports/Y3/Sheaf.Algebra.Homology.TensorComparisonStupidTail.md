## What changed

Replaced the proof of `CochainComplex.quasiIso_tensor_of_stupid_tail` with a complete
mapping-cone argument. The proof chooses a K-flat resolution of the one-term complex
`B[0]`, proves tensor comparisons using K-flat whiskering, identifies tensoring a mapping
cone with a mapping cone, and applies the distinguished triangle of the degreewise split
stupid-tail sequence. Added proof-only imports for the K-flat resolution instance,
acyclic-cone criterion. The degreewise-split triangle API is already available through
the original K-flat import; its redundant direct import was removed in second reading.

## Proved and sorry left

Hole closed (1): `CochainComplex.quasiIso_tensor_of_stupid_tail`.
Holes added (0): none. No `sorry` remains in the item or is added by this delivery.
This is a proof of 1 of 1 original holes, not a decomposition.

## No longer needed

The original plan's abstract derived-functor, derived cohomology ladder, natural
transformation, and five-lemma dependencies are not needed by the mapping-cone proof;
the following original proof dependencies are pruned:

- `lem-weil-pbc-complex-ses-triangle` (Mathlib derived short-exact triangle);
- `lem-pc-mixed-tensor-kflat-quasi-iso`
  (`Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso`);
- `lem-pur-left-derived-from-kflat-class`
  (`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`);
- `lem-weil-pbc-commshift-nattrans-triangle-morphism`
  (`WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`);
- `lem-weil-pbc-derived-cohomology-ladder` (Mathlib homological functor ladder);
- `lem-weil-pbc-five-lemma` (Mathlib abelian five lemma).

None had been imported by the original module, so no original import lines were removed.
Second reading removed the redundant proof-only import
`Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`, which the existing
K-flat import already supplies. This does not prune the degreewise-split triangle node: its
Mathlib declaration is used by the proof.
These are dependencies pruned from this item's proof, not a claim that no other target
path reaches their modules. The proof uses the
existing source declarations for K-flat resolution, tensor mapping-cone comparison,
K-flat whiskering, and the degreewise-split distinguished triangle.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was substantially more general than necessary. A direct cone proof
reduces the statement to the K-flat resolution of `B[0]` and the split stupid-tail
triangle, so its abstract derived-category ladder is redundant.

The theorem signature and all public imports are unchanged. Four private helpers are fully
proved. Compilation is clean, and `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. Zero rings, zero complexes, and negative k require
no additional hypotheses; all degree cases are handled by the split-sequence construction.
The K-flat resolutions used in the proof come from proved ordinary-module source instances,
not from choosing witnesses of an unproved existence theorem. The source instance creates
proof-local resolution data only; no public construction or definition is added.

For accurate bookkeeping, the DAG now cites the homotopy degreewise-split triangle and
acyclic two-out-of-three leaves, plus the existing cone and tensor-cone nodes and the
ordinary-module K-flat definition. It records the exact fully proved source APIs used for
ordinary-module resolution and triangulated tensor; it does not use the sheaf-specific
resolution or mixed-tensor declarations.

## Second reading by Y3

1. **Interface: pass.** Compared the whole delivered module and node with the repository
   using `diff`. The only existing declaration's signature is byte-for-byte identical,
   and all five public imports are unchanged. The added declarations are four private
   proved lemmas. Parsed JSON comparison confirms that only `proof`, `proof_deps`, and
   `proof_origin` change; the mathematical statement and recorded Lean signature do not.
   No definitions or change records are added.
2. **Proof: pass.** Compiled locally with `lcompile.py`, without errors or warnings.
   A scratch copy with `#print axioms` for the theorem and each private helper reports
   exactly `propext`, `Classical.choice`, and `Quot.sound` for all five. There are no
   remaining sorries or forbidden declarations. Read both resolution choices against
   the proved `ModuleCat.hasFunctorialFlatResolution` and K-flat left-derivability
   instances: these are proof-local choices from proved existence, with no public data
   construction and no arbitrary witness from an unproved theorem.
3. **Split statements: pass (none).** No new public statement or hole is split off.
   Read all four private helpers. The tensor-exchange lemma uses cancellation of
   quasi-isomorphisms in the commuting square in both directions; the cone helper uses
   the existing total-tensor cone isomorphism. The splitting proof covers n < k,
   n = k, and n > k and therefore also negative k, zero modules, and the zero ring.
   Repeated semantic search with “quasi-isomorphism tensor comparison closed under
   extensions of complexes using K-flat resolutions” found only flat-module exactness
   and Tor results, whose hypotheses do not supply this theorem; repository and
   Mathlib truncation searches found no replacement for the constructed splitting.
4. **Route and pruning: pass after import cleanup.** Read the unit record
   `dag/units/sk-thm-picard-duality.json`: this auxiliary node is absent from its
   `realized` statement and steps, and the reduction changes no unit realization or
   chapter route. The cone argument is below the unit level and uses proved source
   APIs instead of the old abstract derived-comparison ladder. Every one of the six
   removed original `proof_deps` appears in `## No longer needed`. Removing the two
   retained new imports in scratch copies fails respectively at resolution existence
   and the cone criterion; removing the direct DegreewiseSplit import compiles cleanly.
   Removed that redundant import; all new imports are proof-only.
5. **DAG: pass.** Read the five dependency nodes and their recorded source/Mathlib
   declarations. The node's `proof_deps` equals the union of the steps' `uses` and
   follows the actual tensor-exchange, cone, degreewise-split-triangle, and acyclicity
   proof. In particular the triangle dependency's Mathlib match includes the precise
   homotopy-category theorem used here. The ordinary-module resolution and triangulated
   tensor source APIs are explicitly identified in the proof text and `proof_origin`.
   No new nodes or statement changes need records.

Changes in second reading: removed the redundant proof-only DegreewiseSplit import;
replaced the theorem's obsolete ladder-proof docstring with the actual cone proof;
made the closed/added-hole counts explicit and completed the pruning and review report.
No proof term, signature, or mathematical node statement was changed.
