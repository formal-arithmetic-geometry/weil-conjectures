## What changed

Completed `AlgebraicGeometry.Scheme.structureSheafCohomologyPullback_comp_apply`
without changing its statement or any definition. Used two proved private adjunction helpers and the existing proved theorem
`CategoryTheory.Abelian.Ext.exactFunctorCompositionComparison`, then completed the
Yoneda-product calculation. Added a proof-only import of
`Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`. The second reader
removed the duplicate private Ext induction and its MapBijective import.
Updated the existing node's proof to describe the actual argument. Cached the
sheafification, abelian-category and Ext instances locally to avoid repeated
expensive instance synthesis; the complete file compiles within the 60-second limit.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.structureSheafCohomologyPullback_comp_apply`
(node `lem-sc-structure-sheaf-cohomology-pullback-composition-pointwise`).
Both remaining private adjunction helpers are proved. No holes added; no `sorry` remains in the delivery.
This is a proof, not a decomposition.

## No longer needed

No original imports or existing dependency nodes were removed. Removed the first
attempt's proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`
when replacing its private Ext induction with the existing composition comparison.
No claim of a globally pruned module is made: the removed import was absent from
the repository baseline. The abandoned sandbox
node `new-structure-sheaf-pullback-comp-hom` is unnecessary and was removed from this
undelivered attempt. No new module or map-level functoriality assumption is needed.

## Where the brief, the DAG or earlier work was wrong

The previous report described a map-equality split equivalent to the pointwise goal;
that would merely repackage the original hole. It was also stale relative to the
actual sandbox Lean, which still ended in `sorry`. This delivery completes the direct
argument instead. The earlier constant-comparison calculation needed normalization
of composite-functor objects before simplifying identities.


## Second reading by S2

1. **Unchanged interface: pass.** Compared the only delivered Lean module with the
   repository using `diff`. The existing declaration
   `AlgebraicGeometry.Scheme.structureSheafCohomologyPullback_comp_apply` has a
   byte-for-byte identical signature: arbitrary composable morphisms of schemes,
   arbitrary degree n and class x, and exactly the original pointwise equality.
   No definition or public import changed. The two new helpers are private.
2. **Proof and axioms: pass.** The original attempt compiled cleanly in 34.5 seconds;
   the shorter final proof compiled cleanly in 30.8 seconds through `lcompile.py`.
   The file contains no `sorry`, forbidden declarations or hollow definitions.
   A scratch copy prints the axioms of both private helpers, the public theorem,
   and the reused Ext comparison theorem; only the permitted standard axioms occur.
   The definitions used by the proof are the original explicit pullback construction;
   no arbitrary witness is selected from an unproved existence theorem.
3. **Split-off statements: pass, none.** No public theorem, node or hole was split
   off. The private helpers express adjunction composition and constant comparison
   coherence and have complete proofs. Their identity-adjunction cases reduce to
   ordinary composition and the unit identity; no nonzero-degree or nonempty-scheme
   hypothesis was added. The Ext comparison handles every degree, including zero.
4. **Shortest route and pruning: repaired.** Searching `lean/Sheaf`, upstream Ext
   modules and pinned Mathlib by `mapExactFunctor`, naturality, composition and
   `leftAdjointUniq` found the proved library composition comparison, which exactly
   supplies the original private Ext helper's needed isomorphism case. Replaced the
   induction by that theorem and removed the MapBijective import. Retained the two
   direct adjunction calculations: the existing constant pullback coherence theorem
   is for the small etale site and different coefficients, not these Zariski sheaves.
   Both final imports are used; the definition import supplies the public signature,
   and the comparison import is proof-only. The sole old proof dependency remains
   used and `## No longer needed` accounts for the removed sandbox import. Read
   `dag/units/sk-prop-av-cube.json`: this node does not realize a unit statement or
   step (its `realized` arrays are empty). No unit-level route is bypassed or changed.
5. **DAG agreement: repaired, pass.** The node's first step now names the reused
   Ext composition comparison node. Its remaining steps describe the two proved
   adjunction helpers and the final Yoneda-product calculation. `proof_deps` is
   exactly the union of the steps' `uses`: the original pullback definition and the
   existing Ext comparison node. `proof_origin` records the explicit coherence
   argument. All other node fields retain their original values, and no new nodes
   or change records are required.

Second-reading changes: removed `ext_comparison`, replaced its application by the
proved library theorem, replaced the associated proof-only import, synchronized
`proof` and `proof_deps`, and updated this report. One original hole closed, zero
holes added; this is a proof rather than a decomposition.
