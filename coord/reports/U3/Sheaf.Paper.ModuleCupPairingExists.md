## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_moduleCupResolutionPairing` in
`Sheaf.Paper.ModuleCupPairingExists`, with its existing signature unchanged.
The existing Godement pairing supplies integer-indexed augmented flasque complexes.
Private, fully proved helpers restrict the complexes and quasi-isomorphisms to natural
degrees, construct the bilinear section pairing, and verify restriction, signed Leibniz
(including both equality transports), and the degree-zero augmentation identity.
A concrete comparison map to an existing injective resolution is constructed with
`InjectiveResolution.descOfQuasiIso`; flasque acyclicity and
`Functor.quasiIso_map_of_rightAcyclic_nat` prove that it computes cohomology.
The existential Godement data is eliminated inside the theorem, never selected into a
public definition. No arbitrary unresolved witness is used to define an object.

Replaced the direct LongExactSequence and PlusHomology imports with the proof-only
`WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` import. All public imports,
existing definitions and public signatures are unchanged. Updated the item's node's
proof and proof dependencies to record the actual implementation, including the
already proved tensor additivity declaration. The unit's route is preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.exists_moduleCupResolutionPairing`
(node `lem-sc-module-cup-pairing-exists`). The item's module contains no `sorry`.
Added 0 holes and split off 0 obligations. Every private helper is proved.
The proof uses the existing `moduleCup_godement_pairing` obligation
(node `lem-sc-module-cup-godement-aw`); it does not claim the transitive closure is
axiom-free. `moduleCup_flasque_acyclicity` and the acyclic-resolution comparison
are already proved in the current library.

Local compilation succeeds without warnings. The mandatory delivery dry run checks
compilation, declaration/axiom probes, import cycles and delivery preflight.

## No longer needed

Removed direct imports:
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`:
  no derived-category-plus comparison is needed; the natural-degree comparison suffices.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`:
  its long exact sequence is not used directly. It remains a transitive dependency of
  `RightDerived.Acyclic`, so this removal does not claim global pruning of that module.

The supplementary proof import
`Mathlib.Algebra.Homology.Embedding.TruncGEHomology` was tested and removed because the
needed declarations are already public transitive imports of the Godement interface.
No original proof-dependency node is discarded: all six still supply the data,
cohomology definitions, injective resolution and acyclic comparison used by the proof.
No conclusion about reachability from other targets is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempts were blocked by missing compiled ModuleCupResolutionData and
ModuleCupFlasqueAcyclicity imports. Those imports are now available: the original module
and the completed proof both compile. The earlier attempts also left local compiled
dependency artifacts in .lbuild; these were removed before the final dry run, so
verification uses the published shared baseline without a dependency overlay.

The Leray node's primary Lean module is LongExactSequence, but its natural-degree
acyclic comparison is in RightDerived.Acyclic. Importing that module is necessary;
PlusHomology is unnecessary. The source tensor-summand differential lemma carries
unused global triple-tensor hypotheses, so the proof uses its underlying proved
Mathlib mapBifunctor differential formulas directly, requiring no monoidal-closure
choices or new supporting statements. No statement error or interface change was needed.

## Second reading by U3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof and proof-only imports changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The proof uses only the existing open Godement obligation transitively. Verdict: pass.
3. Checked split-off obligations and searched the library and Mathlib; no new statements were added, and the proved theorem is the existing target statement. Verdict: pass.
4. Reviewed the proof route and imports. The natural-degree restriction and acyclic comparison follow the stated plan; unused PlusHomology, LongExactSequence, and supplementary truncation imports were removed. Verdict: pass.
5. Compared the DAG node with the Lean proof and confirmed the unit route remains represented. The node records the implementation and dependencies used. Verdict: pass.

Changed only the proof implementation, proof-only imports, and corresponding DAG proof metadata; no statement or definition change was needed.
