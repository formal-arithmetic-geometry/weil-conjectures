## What changed

Filled all four theorem proofs in
`lean/Sheaf/AlgebraicGeometry/FrobeniusDetailed.lean`, preserving every declaration's
signature, visibility, docstring, and all definition bodies and imports.

`specGaloisMap_over` uses contravariant Spec functoriality and `AlgEquiv.commutes`.
`galoisMap_inverse` proves the composition and identity equations for Spec of algebra
automorphisms in the over category, then applies `baseChangeMap_comp` and
`baseChangeMap_id`. `galoisMap_projections` uses the existing base-change projection
lemmas. `galoisMap_affine` cancels the affine comparison isomorphism, applies pullback
extensionality, and checks the two tensor inclusions. These are the arguments already
recorded in the declaration docstrings; the node has no numbered proof dependencies
and no unit route to change.

Searched the source library and Mathlib for coefficient actions and affine pullback
comparisons. The existing proved argument in
`WeilConjectures.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity` supplies the
same tensor-inclusion calculation; no import of its stronger transitivity theorem is
needed. LeanFinder returned tensor base-change tools but no direct statement;
Loogle did not recognize `pullbackSpecIso`. The local Mathlib source supplies the
pullback comparison equations. Search calls are recorded in `searches.jsonl`.

The completed module compiles through `lcompile.py`. A separate sandbox copy with
`#print axioms` checks all six declarations and reports only `propext`,
`Classical.choice`, and `Quot.sound`. No line exceeds 100 characters.

## Proved and sorry left

Closed 4 of 4 original holes, all attached to
`def-weil-frobenius-detailed`:

- `WeilConjectures.FiniteFieldDatum.specGaloisMap_over`.
- `WeilConjectures.FiniteFieldDatum.galoisMap_inverse`.
- `WeilConjectures.FiniteFieldDatum.galoisMap_projections`.
- `WeilConjectures.FiniteFieldDatum.galoisMap_affine`.

No holes remain and no holes or split-off statements were added. The existing
`galoisMap` and `geometricFrobenius` definitions now also have no sorry axioms.

## No longer needed

None. No imports removed and no existing nodes or modules pruned. Both existing
public imports supply the original statement interface, including the finite-field
datum and its geometric fibre and the geometric field Frobenius. The proofs use no
additional modules, and no new dependency on a holed theorem is introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The node is a definition node with empty
`proof` and `proof_deps`; the four existing theorem docstrings already describe the
complete elementary proofs. The affine proof works for arbitrary commutative
algebras, including the zero ring; the inverse and projection proofs require no
nonemptiness, affineness, or finite-type assumptions on the model.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
