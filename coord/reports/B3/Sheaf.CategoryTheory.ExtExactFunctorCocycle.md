## What changed

Proved `CategoryTheory.InjectiveResolution.ext_mapExactFunctor_cocycle` in
`Sheaf.CategoryTheory.ExtExactFunctorCocycle`, without changing its statement or visibility.
The proof uses Mathlib's Ext roof and exact-functor formulas, checks the cocycle numerator
at degree zero, and uses the augmentation homotopy to identify the inverse denominators.
The node's proof now records this calculation. No new imports, statements or modules.
A declaration-local transparency option supports the canonical single-complex identifications.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.InjectiveResolution.ext_mapExactFunctor_cocycle`
(node `lem-weil-pbc-ext-exact-functor-cocycle`). No holes added or left.
This is a proof from Mathlib, not a decomposition into unproved statements.
The proof works uniformly in degree zero and for zero cocycles and zero precomposition.
Single-file compilation is clean; the delivery dry run checks the axiom probe.

## No longer needed

No imports removed: both public Mathlib imports are needed by the statement.
The planned dependency `lem-weil-pbc-kinjective-hom-derived` is unnecessary:
its bijectivity theorem, and a separate proof via K-injective targets, are not used.
Mathlib's `DerivedCategory.Q_map_eq_of_homotopy` directly localizes the supplied homotopy.
No Sheaf or WeilConjectures proof-dependency modules are imported or needed.
Retained `lem-weil-pbc-ext-via-injective-resolution`, through its Mathlib Ext roof formula.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned appeal to K-injective morphism bijectivity was
unnecessary; invertibility of the augmentations and functoriality suffice.
Searches through leanfinder, loogle and grep found the constituent Mathlib formulas,
but no theorem already giving the cross-category cocycle calculation.

## Second reading by B3

1. Compared the complete delivered module with the repository module using `diff -u`.
   The sole existing declaration's signature, universes, hypotheses (including both
   cocycle equations and the augmentation homotopy), conclusion, visibility and
   docstring are byte-for-byte unchanged. Only its proof and a declaration-local
   elaboration transparency option were added. No definitions or change records.
   Verdict: pass.
2. Read the roof calculation and compiled the module locally through `lcompile.py`
   (5.3 seconds, no warnings or errors). A scratch copy with `#print axioms
   CategoryTheory.InjectiveResolution.ext_mapExactFunctor_cocycle` compiled in
   5.6 seconds and reported exactly `propext`, `Classical.choice`, `Quot.sound`.
   No `sorry`, forbidden declaration, or data construction occurs in the delivery.
   The choice `hφ.some` selects a supplied homotopy only inside a proof; it does
   not define data from an unproved existence theorem. Verdict: pass.
3. No statements were split off or added, so there are no new statement/docstring/
   node obligations. Independently searched leanfinder for naturality of the Ext
   cohomology-class equivalence under exact functors, loogle for `mapExactFunctor`
   with `Cocycle` (no hits), and grep for Ext constructor and single-cocycle map
   formulas. Read Mathlib Injective/Ext, Ext/Map and the exact-functor comparison
   identities. They provide the constituent formulas, not this whole comparison.
   Checked degree zero: the source-single component remains α;L(a);φ⁰ with no
   positive-degree hypothesis; zero a or α gives zero on both sides by additivity.
   There is no assumption that L preserves injective objects. Verdict: pass.
4. Read Stacks 06XR(1) and 01F8, the retained Mathlib-leaf node
   `lem-weil-pbc-ext-via-injective-resolution`, the pruned Mathlib-leaf node
   `lem-weil-pbc-kinjective-hom-derived`, and `dag/units/sk-thm-p1.json`.
   The proof uses the former's roof formula, then localizes the supplied homotopy
   directly rather than invoking the latter's morphism bijectivity. The numerator
   equality follows by `from_single_hom_ext`; the denominator equality follows by
   naturality and cancellation of the mapped quasi-isomorphism. Both public imports
   are needed in the statement: the resolution equivalence and `mapExactFunctor`.
   The sole removed old proof dependency is listed under No longer needed; no
   imported module is removed. Neither dependency pruning nor this tool calculation
   replaces any node in the unit's `realized` statement or steps. Verdict: pass.
5. Compared the delivered node JSON with the repository node: only `proof`,
   `proof_deps`, and `proof_origin` changed. Its three steps agree with the Lean
   reduction, denominator and component calculations; the retained dependency is
   the Mathlib Ext/resolution leaf actually used. Its statement and verbatim Lean
   statement record are unchanged. No new nodes. Verdict: pass.

Second reading changed only this report by adding the independent review and
explicit axiom results. No repair to the Lean proof or DAG was needed.
