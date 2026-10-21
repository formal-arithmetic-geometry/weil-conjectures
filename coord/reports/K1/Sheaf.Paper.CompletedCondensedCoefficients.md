## What changed

Filled `AlgebraicGeometry.ProEtale.completedCondensedIntegral` and
`AlgebraicGeometry.ProEtale.completedCondensedPadicIntegral` in
`Sheaf.Paper.CompletedCondensedCoefficients`. The private helpers construct the
specified compact quotient towers, transport them through the relative profinite
test functor and Yoneda, and lift their limit property to ring objects. The finite
constant comparisons are constructed explicitly so their transition naturality is
proved. Scheme pullback preservation follows from the existing monoidal compositor
and the normalized cones. Existing public signatures and definitions are unchanged.

Proof imports added: `Sheaf.Paper.FiniteDiscreteCondensedRing`,
`Sheaf.Paper.FiniteDiscreteSchemeRing`, and
`Mathlib.Topology.Algebra.Ring.Compact`. The integral-limit and finite discrete
modules are imported with `all` to reuse their existing private comparison APIs.
The node proof is updated to describe the specified quotient-tower implementation.
The new private instance registrations and elaboration settings are documented in
`coord/changes/completed-condensed-integral-proof-instances.md`, as requested by
the delivery preflight. They change no existing mathematical interface.

## Proved and sorry left

Closed the two original holes:
- `AlgebraicGeometry.ProEtale.completedCondensedIntegral`.
- `AlgebraicGeometry.ProEtale.completedCondensedPadicIntegral`.

No holes added or split off; no `sorry` remains in the delivered module.

## No longer needed

No modules are withdrawn. No public imports are removed. The integral proof uses
the underlying-set and representable pullback comparisons of
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` directly, rather than
transporting its chosen spectral-integer completion through a separate ring
identification. Its module and the unit's representing-scheme route remain used.
The p-adic specialization uses the same construction with `toZModPow` directly,
so no additional equivalence between a chosen finite subextension and the base
field is required. The existing rational, algebraic-closure and scheme pullback
proofs remain in place.

## Where the brief, the DAG or earlier work was wrong

The existing integral detail theorem is stated for a chosen coefficient-extension
integer ring and its maximal-ideal tower, whereas this item specifies the inherited
integer ring and powers of a supplied uniformizer. Its reusable representation
comparisons avoid an unnecessary transport through that different encoding. The
p-adic formula can use the standard ZMod tower directly. Both are the same
representing-scheme argument as the blueprint, with the specified reduction maps.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
