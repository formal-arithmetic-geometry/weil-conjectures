## What changed

Proved `WeilConjectures.PurStrictScalar.compositionProper` in the assigned module.
The proof identifies `compositionTower` with the canonical composite-adjunction
comparison, inverts the restriction/proper-image cocycle, and applies mate pasting.
The new modules `Sheaf.Paper.StrictScalarTowerAssociator` and
`Sheaf.Paper.StrictProperRestrictionComposition` prove
`scalarTowerAssociator_normalization` and `properRestriction_composition`, respectively.
The item imports the latter only for its proof. Their restriction compositors
are actual exact localizations of the ordinary identity-on-sections isomorphisms.
No existing signature, definition, instance, public import, or exported attribute changed.

Validation: both new modules compiled, and the final assigned module compiled
successfully through `lcompile.py` in 50.4 seconds. Debugging profiler options
were removed. The final source has exactly the two unchanged `sorry` bodies.

## Proved and sorry left

Closed one of the item's three original holes:
`WeilConjectures.PurStrictScalar.compositionProper`.
Added zero holes. Both new public theorems and their private helpers are proved.
The two unchanged holes are
`WeilConjectures.PurStrictScalar.compactSupportStrictScalarComposition` and
`WeilConjectures.PurStrictScalar.compactSupportStrictScalarIdentity`, both attached
to `lem-pur-compact-support-strict-scalar-composition`.

## No longer needed

No existing import or module is withdrawn. Removed the planned parent proof
dependency `lem-weil-pbc-diagram-kflat-replacements`
(`Sheaf.Algebra.Homology.DiagramKFlatReplacements`): proper composition uses the
normalized restriction square, so it needs no K-flat pullback/scalar-square
calculation. That module may still serve other users and is not withdrawn.
All other original dependencies are retained for the existing proofs and the
unfinished strict support clauses. The blueprint unit and its route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan for the proper clause needlessly passes through derived
pullback and K-flat tensor generators: the actual `proper` map in the library is
already the mate of the inverse `properRestriction`. Its whole-complex unit
normalization is enough to prove the needed cocycle directly. The proof also
shows that properness of the morphism is unnecessary for this particular clause,
as its existing signature already permits.

A concrete conversion between `unitCompatible` and `unitNormalized` took 99 seconds
in kernel checking even though its elaboration was quick. A private generic
predicate-conversion lemma keeps that conversion abstract. The categorical
composition argument is likewise proved for abstract functors before specialization.
The profiled complete cocycle file compiled in 15.1 seconds, with kernel checking
under one second. The original shared definitions are unchanged.

## New nodes

`lem-pur-strict-scalar-tower-associator` records the constructive ordinary and
derived restriction compositors and proves that the localized ordinary tensor
associator is their canonical scalar-adjunction conjugate. It uses the existing
proved generic exact-localization result and the cochain Hom formula.

`lem-pur-strict-proper-restriction-composition` records the coefficient-restriction
cocycle. Ordinary sectionwise identity gives its source square; normalized square
pasting and naturality give the derived equation. This is independent of
compactifications, reductions, arithmetic selections and finite-Tor inputs.
No change record is needed: all existing statements and definitions are unchanged.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
