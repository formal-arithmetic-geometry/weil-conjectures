## What changed

Proved `CategoryTheory.Triangulated.TStructure.fixedPair_postnikov_identifications` in
`Sheaf.CategoryTheory.Triangulated.FixedPairPostnikovIdentifications`, with all public
signatures and the four existing functor definitions unchanged. Added proved private helpers
for canonical equivariant counits/units, adjunction factorizations, interchange, shift
cancellation and reflection of underlying isomorphisms. No chosen data comes from an
unproved existence theorem.

Upper and lower absorption use Mathlib's invertibility of a truncation applied to the
counit/unit, followed by naturality for the normalization. Interchange uses the two lifted
adjunction factorizations and the canonical pentagon's uniqueness. Shift cancellation uses
`Functor.map_shiftFunctorCompIsoId_hom_app`. Cohomology formulas unfold from transport;
Mathlib aisle-preservation instances and the shift lemmas prove heart membership.

Updated the existing node's proof, proof_deps and proof_origin to this route. Replaced
three public imports by the modules defining the notions actually used, and added a private
`import all` of Mathlib's truncation module to inspect its unexposed canonical interchange.
The import change is recorded in `coord/changes/p2-fixed-pair-postnikov-imports.md`.

Validation: the complete theorem compiled through lcompile.py with no sorry. The delivery
runs compilation and the declaration axiom probe again. Tested normalization at the actual
canonical maps, not merely existence of some isomorphisms. The argument works for every
integer including zero and negative degrees, and requires neither boundedness nor
inverse t-exactness beyond the retained original hypotheses. It introduces no
triangulated structure on fixed pairs. Zero current downstream Lean modules require adaptation.

## Proved and sorry left

Closed one of one original holes:
`CategoryTheory.Triangulated.TStructure.fixedPair_postnikov_identifications`
(node `lem-pod-fixed-pair-postnikov-identifications`). All eight conjuncts are proved.
Zero holes left, zero holes added, zero split off. All new private helpers are fully proved.

## No longer needed

Removed imports:

- `Sheaf.SecDeligneLaumonA1.FixedPairTruncationOrthogonality`: its existentially quantified
  lifts do not identify their functors with the specific canonical transports in this file.
  The needed maps and two adjunction factorizations are proved directly in short private helpers
  using the normalized comparisons and existing Mathlib adjunction maps. Removed
  `lem-a1-fixed-pair-truncation-orthogonality` from this node's proof dependencies; it remains
  a statement dependency for the description of the canonical lifts.
- `Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`: the canonical comparisons
  and normalization equations used here are already proved in
  `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`.
  The node `lem-pod-texact-truncation-comparison` is still used for these normalized comparisons;
  this proof needs no aggregate theorem asserting their other compatibilities.
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`: only the heart predicate
  and Mathlib's truncation adjunction infrastructure are needed, so import Mathlib's Heart
  directly. The truncation portion of `lem-weil-heart-short-exact-triangles` is still used;
  none of its homological-functor, kernel, cokernel or short-exact-sequence results is needed.

Absorption needs no additional intermediate nodes: Mathlib's
`isIso_truncLE_map_truncLEι_app` and `isIso_truncGE_map_truncGEπ_app` provide invertibility.
Heart membership needs no separate interchange argument. No module is withdrawn or deleted;
these imports are unnecessary for this proof, not claims of global unreachability.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was found. The original DAG's absorption constructions
were longer than necessary given the existing Mathlib API. Its heart-membership step can use
the direct aisle-preservation instances. The original theorem docstring retains the original
seven-step plan; the updated DAG records the implemented simplifications.

Mathlib's `truncGELTIsoLTGE` is a public definition with an unexposed body. A private
`import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE` is needed to identify
its hom with `truncGELTToLTGE`; ordinary importing alone does not permit this reduction.
This is a module-visibility issue, not a mathematical gap, and no Mathlib file was changed.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
