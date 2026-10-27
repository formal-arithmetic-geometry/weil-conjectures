## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.finiteClopenBetaSiteTransport`
with the ordinary-sheaf open-adjunction calculation. The theorem's signature,
including its arbitrary commutative coefficient ring and arbitrary morphism p,
is unchanged.

The proof reuses the proved generic mate calculation from
`FixSiteOpenExchangeSheaf` through a proof-only `import all`. Its finite-coefficient
wrappers cannot be applied directly. Fully proved private helpers establish the
same canonical open-unit normalization and inverse-image square compatibility
for arbitrary coefficients, using the existing canonical constructions and
`comparison_square_component_of_commRing`. A separate forward-base-change unit
lemma avoids repeatedly expanding the concrete Kan-extension construction.
Finally, postcomposition and cancellation of comparison isomorphisms give the
specified inverse-beta equation. The DAG proof and proof dependencies record this
calculation. No other existing module is modified.

## Proved and sorry left

Validation: the complete module compiled through `lcompile.py` in 16.5 seconds.
The profiling options used to diagnose a costly witness conversion have been removed.

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.finiteClopenBetaSiteTransport`
(node `lem-cbc-finite-clopen-beta-site-transport`).

No sorry remains in the item. No sorry is added, and no statement is split off.
All new private helpers have complete proofs. The argument covers empty opens,
identity maps, the zero sheaf and the zero ring without extra hypotheses.

## No longer needed

The proof does not use `cor-cbc-derived-extension-zero-base-change` or its module
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`: there is no derived
localization, identity coherence or pasting calculation in this ordinary-sheaf
statement. The ordinary etale base-change map and its unit normalization suffice.
Similarly, the proof uses the ordinary map from
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange`,
not the derived wrapper in
`Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.
These modules are not withdrawn and may still be required by other parents.
The original public imports are preserved for importer compatibility.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is valid, but its derived finite-coefficient dependencies
are unnecessarily strong for this ordinary-sheaf theorem. The proved
`fixSiteOpenExchangeSheaf`, `fixSiteOpenExchangeSquare` and
`openComparison_unit_normalization` wrappers assume `[Finite Λ]`, while this
item's existing statement has no such assumption. Their underlying mate and
section calculations work for arbitrary coefficients; the private helpers prove
that version without changing shared signatures or weakening the item.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
