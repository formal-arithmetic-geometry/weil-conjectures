## What changed

Proved `AlgebraicGeometry.derived_open_shriek_adjunction` in
`Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction`, with its signature unchanged.
Replaced the proof-only import of
`Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors` by
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
The existing underived exact adjunction induces a termwise homotopy adjunction;
the two `mapDerivedCategoryFactorsh` isomorphisms give commuting localization squares.
Mathlib `Adjunction.localization` then constructs the required derived adjunction.
Updated the theorem's proof explanation and the node's proof, proof_deps and proof_origin.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.derived_open_shriek_adjunction`
(node `lem-sc-derived-open-shriek-derived-adjunction`).
No holes remain in the delivered module and no holes were added or split off.
This proof uses existing library results; it does not claim the transitive library
is sorry-free. The termwise adjunction and localization machinery are already proved.
The module compiled cleanly with the prescribed lcompile.py command.

## No longer needed

Removed import `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors` and removed
proof dependency `lem-pc-derived-adjoint-functors`.
The proof no longer needs the general essentially constant ind/pro diagram route:
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`,
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`,
`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`,
`Sheaf.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors`, and
`Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`
are not needed through this item's former proof import. Other targets may still use them.
The exact-functor factorization and abstract-derived-category dependencies are retained.
No public imports were removed, and no definitions or statements were changed.

## Where the brief, the DAG or earlier work was wrong

The planned route through everywhere-defined derived functors was unnecessarily general
for two exact functors. Mathlib's localization theorem gives the adjunction directly.
The source-library `Adjunction.mapDerivedCategoryAdjunction` also exists, but requires
additional resolution and monoidal instances absent from this statement; it was not used.
The unit `sk-thm-picard-duality` has no realized nodes for its statement or steps, and
this replacement leaves the open-shriek adjunction and the unit-level route intact.
Searches: leanfinder returned the general derived adjunction and exact-functor
factorizations; loogle found `CategoryTheory.Adjunction.localization`; rg of Mathlib,
WeilConjectures and Sheaf found the proved termwise adjunction and its existing DAG node
`lem-weil-pbc-termwise-adjunction-homotopy`. No new nodes were necessary.

## Second reading by S3

1. Signature and visibility: PASS. Compared the complete delivered module with the
   repository by diff and checked the theorem signature byte for byte through `:= by`.
   Its parameters, universes, typeclass hypotheses and conclusion are identical.
   Only the proof, its explanation, and one plain proof-only import changed.
   No definition or public import changed; no change record is needed.
2. Proof and axioms: PASS. Independently compiled the delivered module with lcompile.py
   (exit 0, no warnings). A scratch copy with `#print axioms` shows exactly
   `propext`, `Classical.choice`, `Quot.sound` for
   `AlgebraicGeometry.derived_open_shriek_adjunction`, and also for
   `CategoryTheory.Adjunction.mapHomotopyCategory`,
   `CategoryTheory.Functor.mapDerivedCategoryFactorsh`, and
   `CategoryTheory.Adjunction.localization`. In particular the delivered theorem
   does not depend on `sorryAx`. Scanned the module: no remaining sorry, custom axiom,
   unsafe/opaque declaration, extern or implemented_by; no new data definition.
   Choosing the underived adjunction is justified by its proved existence theorem.
3. Split statements and edge cases: PASS, vacuous. There are no new statements,
   no split-off holes, and no restatement of the goal. The argument is uniform in
   the open U, including the empty open and the whole space: termwise adjunction
   and exact-functor localization require no nonemptiness or proper-open assumption.
4. Route, imports and pruning: PASS. Read the termwise adjunction construction,
   Mathlib exact-functor factorization and localization theorem. Independently
   searched with loogle for `CategoryTheory.Adjunction.localization` and rg for
   extension-by-zero adjunctions and `mapDerivedCategoryAdjunction` in the library.
   The latter generic derived-functor theorem requires extra monoidal/resolution
   instances, so the direct localization route is appropriate. Each remaining
   import serves the signature or the proof; the added homotopy-adjunction import
   is plain. The only removed old proof dependency is
   `lem-pc-derived-adjoint-functors`, already listed under No longer needed.
   Checked `dag/units/sk-thm-picard-duality.json`: realized.statement and its one
   realized step are empty. This node-level replacement retains the stated
   derived-open adjunction and changes no unit or chapter route.
   The listed downstream modules are bypassed on this item's former proof route;
   global unreachability is for the maintainer's import-closure ledger to decide.
5. DAG agreement: PASS. Compared the node JSON: only proof, proof_deps and
   proof_origin differ. The uses union equals proof_deps. Its four dependencies
   match the underived exact adjunction, existing termwise adjunction, Mathlib
   exact-functor factorization, and derived-category localization used in Lean.
   No new nodes need validating. The statement and Lean attachment are unchanged.

Second-reading changes: added this independent review and its explicit axiom evidence
and pruning qualification. No Lean or node repairs were necessary. Closed one hole,
added zero holes; this is a proof, not a decomposition.
