## What changed
Proved `AlgebraicGeometry.Etale.etale_mayerVietoris_comparisons` directly from existing natural isomorphisms. The original declaration signature and docstring are unchanged. Added the proof-only import `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory` for the exact-functor single-degree comparison; the existing public imports supply the statement's cohomology and classical right-derived functors.

The proof first compares classical right-derived functors with the homology of the total derived functor using the upstream degree-zero comparison and bounded/unbounded compatibility. At X it identifies evaluation with global sections. For an arbitrary open W it identifies evaluation with restricted global sections, derives the composite using preservation of K-injective complexes from the exact extension-by-zero adjunction, and moves the exact restriction past the degree-zero embedding. It then specializes to U, V, and U intersection V.

## Proved and sorry left
Proved the sole original theorem `AlgebraicGeometry.Etale.etale_mayerVietoris_comparisons` (1 of 1). No local sorry remains; no statement is split off. Local compilation of the complete proof passed without warnings. A scratch copy with `#print axioms AlgebraicGeometry.Etale.etale_mayerVietoris_comparisons` reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed
The following old proof dependencies are replaced by the existing natural comparison and composition interfaces:
- `lem-weil-pbc-module-sheaves-enough-injectives`: use existing Grothendieck-abelian instances instead of this separate theorem.
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`: no separate degree-zero calculation is needed.
- `lem-weil-pbc-dplus-injective-representative`: already encapsulated in the proved upstream degree-zero comparison.
- `lem-weil-pbc-etale-restriction-injectives`: use the exact extension-by-zero adjunction to preserve K-injective complexes directly.
- `def-sp-injective-resolutions`: no explicit resolution is constructed in this proof.
No existing imports were removed. These dependencies are pruned from this node's route, not asserted globally unreachable. Removed both unlanded component-pair declarations and their proposed nodes from the sandbox.

## Where the brief, the DAG or earlier work was wrong
The first worker's conjunction assembly left all mathematical comparisons sorry-backed, omitted the existing theorem's docstring, did not update the original DAG node, and gave the proposed pair statements no complete natural-language proofs. Its search missed the proved upstream functor-level comparison `singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso`, bounded/unbounded compatibility, and total derived composition interfaces. These suffice to close the theorem without new interfaces.

## New nodes
None. The proposed first-pair and second-pair nodes were removed before delivery.

## Second reading by F2
1. Compared the delivered module with the repository module: the sole existing theorem signature is byte-for-byte unchanged, and its original docstring is restored. No definition or target statement changed. Both extra pair declarations were removed.
2. Compiled the complete proof locally with no errors or warnings. No `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` occurs in the delivered module. The scratch axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. No split-off statement survives. Searched independently using leanfinder (total derived cohomology versus classical evaluation), loogle (`CategoryTheory.Sheaf.Γ, "iso"`), msearch grep (single-degree comparison and terminal sections), and repository rg. Used existing upstream results rather than restating them.
4. Followed the target downward, replacing the pair placeholders with existing natural comparison isomorphisms. Both public imports support expressions in the unchanged signature; the added exact-functor import is proof-only. The five old proof dependencies no longer directly used are listed above. The node is below the unit level and is absent from `dag/units/sk-thm-p1.json`'s `realized` entries; the chapter and unit routes are unchanged. The construction works uniformly for n = 0, empty/full opens, coinciding opens, and non-covering pairs, with no covering premise introduced.
5. Updated the original node's proof steps, proof_deps (their exact union), and proof_origin to match the actual natural-isomorphism proof. Removed both proposed new nodes, so no new-node validation remains. Statements, statement dependencies, and unit/chapter metadata are unchanged.

Changes made during this second reading: replaced the entire pair-based reduction by a complete proof; restored the original docstring; removed the two pair statements and their nodes; added one proof-only import; corrected the original node and this report. The theorem is axiom-clean, not merely reduced to remaining statements.
