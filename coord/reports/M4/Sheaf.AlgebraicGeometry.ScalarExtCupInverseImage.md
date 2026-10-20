## What changed

Restored `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` from its current
quarantine archive and repaired its duplicate-declaration import failure. Its
public import and the complete signature of `scalarExtCup_inverseImage` are
unchanged, including all universes, hypotheses, coefficient maps and degrees.

Replaced the proof import of
`WeilConjectures.AlgebraicGeometry.ScalarExtCupInverseImageFirst` by
`Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison`. The first-factor proof
is adapted from the upstream module as three proved private helpers:
`rightUnitTransport`, `unitComparison`, and `firstTransport`.
The final Yoneda-composition calculation still uses the existing second-factor
theorem and now uses the private first-factor proof. The source library is untouched.

Updated the item's node proof, proof dependencies and proof origin to describe
the actual proof. No data construction or mathematical statement changed.
Change record: `coord/changes/M4-scalar-ext-cup-inverse-image-restoration.md`.

Validation: the repaired file compiled in 29.8 seconds through `lcompile.py`.
`#print axioms AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
A textual comparison confirms the complete public theorem signature is verbatim
that of the quarantine archive. The identities apply uniformly in degree zero,
for zero coefficient maps, zero sheaves, and empty schemes.

## Proved and sorry left

This is a zero-hole repair: the archived module had zero `sorry`s, and the
restored module has zero. Holes closed: none (0 of 0). Holes added: none (0).
No statements split off. The restored theorem
`AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage` and all three new
private helpers are completely proved; its printed axiom list contains no
`sorryAx`. No existing proof was replaced by a hole.

## No longer needed

The item's proof no longer imports
`WeilConjectures.AlgebraicGeometry.ScalarExtCupInverseImageFirst` or depends on
`lem-sc-scalar-ext-cup-inverse-image-first` as a separate theorem: its unit and
first-factor coherence argument is proved privately using the generic recorded
Ext identity comparison. The upstream first-factor declaration remains intact,
with its original proof, signature, attributes and public imports. No module is
withdrawn or claimed to be globally pruned.

Both retained imports are used: local field-linear operations supply the public
statement and its definitions, and `ScalarExtCupInverseImageSecond` supplies the
second-factor theorem. The generic Ext identity comparison import is private.
No unused proof import remains. No unit route is changed.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined, not absent because its statement is unused. Its current
rework entry records a name collision on `externalCupCoefficients`: importing the
upstream first-factor theorem loads upstream field-linear operations alongside
the existing local operations. Those copies have the same mathematical API, but
Lean cannot load both declarations in one environment. Importing the generic
identity comparison and proving first-factor coherence privately repairs the
failure without changing definitions or public interfaces.

The old node proof required the upstream first-factor theorem as an import;
the revised node records its actual, privately proved argument instead.
The current unit's realized route is preserved. Quarantined parents, including
`ScalarCupPullbackNaturality`, retain their statements and node dependencies;
none is withdrawn. Their other rework obligations remain their own items.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
