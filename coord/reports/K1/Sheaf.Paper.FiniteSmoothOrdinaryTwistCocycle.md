## What changed

Replaced `ordinaryTwistCocycle`'s hole by the root normalization argument and induction
on the ordered shifted tensor power. The proof first composes the root maps using
their power equations and the monic kernel inclusion. The Tate-line universal
property identifies their ordinary adjuncts on generators. Exact degree-zero
adjunction composition then gives the derived comparison equation. Compatibility
of adjunction mates with shifts supplies the shifted root factor.

The zero tensor-power case follows from binary tensor compatibility and the existing
scalar left-unit laws. The successor case is a proved categorical calculation using
tensorator naturality, the induction hypothesis and the shifted root equation.
The statement, all its binders, and all coefficient comparison definitions are unchanged.
All six files passed single-file compilation within 60 seconds; the item took 32.5
seconds. Temporary profiling options have been removed.

The remaining binary scalar/tensor compatibility is isolated in
`Sheaf.Paper.QuotientScalarTensorComposition`. It concerns arbitrary pairs of derived
objects, with no root map, root generators, tensor power, smooth morphism, purity map
or geometric transport. It is a genuine structural step of the original argument,
not the original cocycle with its hypotheses renamed.

## Proved and sorry left

- Closed the original hole in
  `AlgebraicGeometry.Etale.FiniteSmoothPurity.ordinaryTwistCocycle` (one original hole).
- Added one hole in
  `AlgebraicGeometry.Etale.FiniteSmoothPurity.quotientScalarTensorComp`, with its source,
  full representative proof in words and a matching new node.
- The item module has zero holes. The six delivered modules together have one hole.
  This is a decomposition, not a net decrease in holes. All private helpers are proved.

## No longer needed

The original planned proof dependencies
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and
`lem-asd-etale-finite-twist-pullback` are not used as proof steps here. In particular,
no finite-twist pullback theorem is required: the comparison record already supplies
the actual root map, its power equation, its generator normalization and its derived
normalization. The existing exact-adjunction and root-line universal-property APIs
handle the root factors directly. The new binary tensor step states precisely the
remaining structural coherence instead of introducing a general ringed-topos setup.
This does not assert that those modules are unused elsewhere in the library or absent
from transitive public imports of the unchanged coefficient definitions.

No existing module is withdrawn. The unit's realized statement and proof route stay.
The proof needs no pullback comparison, purity-source cocycle or compact-support map.

## Where the brief, the DAG or earlier work was wrong

The item's old node included the argument for the second conclusion of its parent,
namely the purity-source cocycle. That belongs to the sibling item and is not part of
this theorem. The updated proof record describes only the actual root-tensor cocycle.

The relevant reusable exact degree-zero insertion-composition and shift-mate helpers
already exist. They remove the need to reconstruct derived root coherence on K-flat
representatives. Binary scalar/tensor coherence remains a separate genuine step;
Mathlib searches found ordinary scalar associators and generic adjunction identities,
but no theorem for these particular normalized derived tensor comparisons.

## New nodes

`lem-pur-scalar-single-map-adjoint-insertion`,
`lem-pur-finite-smooth-root-derived-normalization`,
`lem-pur-finite-smooth-root-derived-composition` and
`lem-pur-finite-smooth-zero-twist-composition` are proved. They package the generic
exact single-object adjunction calculation, its root-record specialization, the
unshifted root-composition argument and the transported unit calculation in separate
modules. The specialized derived
conversions are therefore checked once and kept out of the tensor induction's
compilation unit. The proofs were first improved by sharing categorical endpoints
in abstract lemmas and using the existing cached scalar insertion interface.
No shared definition was changed and these extra files add no holes.

`lem-pur-quotient-scalar-tensor-composition` records the binary compatibility square
for the canonical quotient scalar associator and the normalized tensor comparisons.
The proposed representative proof covers equal indices, zero rings, empty schemes
and unbounded derived objects, and does not assume that coefficient quotients are flat.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteSmoothOrdinaryTwistCocycle": "01e8971c6db69c0f8a4fd3a72d94bc09808d1a52", "Sheaf.Paper.FiniteSmoothRootDerivedComposition": "48ac395e7206beda0e02c8d2a3a2ce64c74cb1f3", "Sheaf.Paper.FiniteSmoothRootDerivedNormalization": "9ae5728b9dc2c3824021fdc9b8078f3de7765dfc", "Sheaf.Paper.FiniteSmoothZeroTwistComposition": "977ca70f19937987172305171dc090e9b98c3539", "Sheaf.Paper.QuotientScalarTensorComposition": "6bd14ac195c1726f83c73a5ff347a398ceedae1c", "Sheaf.Paper.ScalarSingleAdjointInsertion": "0e5bd5aa2e38aa1a0c538f3083666cca12e08e77"}, "results": {"Sheaf.Paper.FiniteSmoothOrdinaryTwistedCocycles": {"hash": "682e723d4caeb2eb01015ad15bd6503584d239c8", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T04:03:35+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
