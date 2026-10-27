## What changed

Proved `AlgebraicGeometry.scheme_theoretic_union` in
`Sheaf.AlgebraicGeometry.SchemeTheoreticUnion`, preserving its exact signature and both public
imports. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` to reuse the proved affine
pullback lemma `Scheme.IdealSheafData.isPullback_subschemeCover_map`.

The proof constructs the union from the intersection ideal, identifies its support with the
support of the product using equality of radicals, and factors each original closed immersion
using the universal property of closed immersions. The theorem docstring and its existing DAG
node now describe this argument. No definition, statement, or consumer changes are needed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.scheme_theoretic_union`
(node `lem-weil-pbc-scheme-theoretic-union`). Proved 1 of 1 sorries; zero split off, zero added,
and zero left in the item. This is a complete proof, not a decomposition.

The complete module compiled successfully through `lcompile.py`, with no errors or warnings.
All proof ingredients come from proved Mathlib declarations and the existing proved source
pullback lemma. The statement includes empty schemes and identical or nested closed subschemes;
the ideal, radical, support and lift arguments require no nonemptiness or distinctness assumptions.

## No longer needed

No existing imports were removed, and no modules were withdrawn.

The proof no longer uses `lem-weil-pbc-affine-open-spec-points` or
`lem-weil-pbc-zero-locus-ideal-intersection`: equality of radicals reduces the support calculation
to Mathlib's global `support_mul` (the existing Mathlib-leaf node
`lem-weil-pbc-product-ideal-closed-subscheme-union`). It also needs no affine-cover argument
from `def-pc-scheme`; that node remains a statement dependency. The removed nodes are omitted
from this node's proof dependencies only; no claim is made that other consumers can prune them.

The quasi-coherent ideal intersection and closed-subscheme construction, the kernel-support
image calculation, and the ideal-inclusion factorization remain used through their recorded
Mathlib declarations. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or repair was found. The original affine-local proof plan is valid, but its
pointwise prime-spectrum argument can be replaced by the existing global radical/product
support identities. The affine pullback clause is already proved in the adopted source library,
so it does not require any new intermediate theorem.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
