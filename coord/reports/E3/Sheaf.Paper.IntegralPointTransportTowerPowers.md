## What changed

Proved `WeilConjectures.IntegralPointTransportTower.inverseLimitComparison_existsUnique`.
The comparison is the adjunction mate of `constantInverseComparison`, whiskered by scalar
restriction and followed by `derivedRestrictionComparison`. A proved private categorical helper
shows this mate is invertible: its maps on hom sets are composites of fully faithful functor
bijections, adjunction bijections, and an isomorphism. Essential surjectivity and Yoneda finish
the argument. Counit naturality gives exactly the existing normalization; the adjunction
bijection gives uniqueness.

Added proof imports of `Mathlib.CategoryTheory.Adjunction.Mates` and all of
`Sheaf.Paper.IsomorphismScalarQuotientChainSquares` to reuse its existing private equivalence
proof. Updated the owning node's proof and dependencies. Validation: the full edited module compiled through `lcompile.py` in 32.5 seconds.

Existing public declarations,
definitions, theorem signatures and public imports are preserved. No shared consumer is edited.

## Proved and sorry left

Closed 1 of the item's 5 holes:
`WeilConjectures.IntegralPointTransportTower.inverseLimitComparison_existsUnique`.
Added no holes and no split-off statements.

Four holes remain, all attached to `lem-trf-integral-point-transport-tower-powers`:

- `WeilConjectures.IntegralPointTransportTower.ordinaryTransport_existsUnique`
- `WeilConjectures.IntegralPointTransportTower.restrictionComparison_existsUnique`
- `WeilConjectures.IntegralPointTransportTower.sectionsLimitComparison_existsUnique`
- `WeilConjectures.integralPointTransportTowerPowers`

The proved comparison uses the existing, still unproved restriction-comparison declaration,
as authorized by stage 3. This is a partial proof delivery with no decomposition.

## No longer needed

None. No imports, modules or nodes are withdrawn. The inverse-limit comparison itself needs
no Roos-coordinate calculation, but the remaining main theorem still uses the planned
point-system and Roos dependencies, so those dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No statement correction. For the inverse-limit comparison, invertibility follows already from
the inverse-image equivalences and the constant-tower comparison. The explicit counit
normalization makes a separate Roos calculation unnecessary for this auxiliary theorem.
The owning node now records this categorical proof. The unit route is preserved.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
