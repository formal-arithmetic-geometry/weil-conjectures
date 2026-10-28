## What changed

Proved `finiteFreeScalarDerivedComparison_beta_normalized` by assembling two
strictly smaller named substeps. The construction substep provides a normalized
beta comparison at every scheme, and the pullback substep proves the displayed
pullback equation for any supplied normalized beta. Added proof-only imports for
those two sibling modules. The three modules compile in import order.

## Proved and sorry left

The assigned declaration `finiteFreeScalarDerivedComparison_beta_normalized` is
proved from the two split-off statements. Two strictly simpler theorem holes remain:

- `finiteFreeScalarDerivedComparison_beta_construction`, node
  `new-sfb-finite-free-scalar-derived-comparison-beta-construction`;
- `finiteFreeScalarDerivedComparison_beta_pullback`, node
  `new-sfb-finite-free-scalar-derived-comparison-beta-pullback`.

Closed 1 of 1 original sorries; added 2 named sorries as a decomposition. No sorry
occurs in a definition.

## No longer needed

No planned proof dependency was removed. The two new substeps use the stated
K-flat resolution, restricted K-flat tensor identification, site-derived tensor
descent, and K-flat scalar comparison normalization. No existing declaration or
module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof step combines the representative construction, its ordinary
augmentation normalization, and pullback descent into one large obligation. Those
are independent strict substeps, so the delivery records them as separate named
statements and proves the assigned theorem by a real conjunction assembly. The
assigned target statement and the unit route are unchanged.

## New nodes

- `new-sfb-finite-free-scalar-derived-comparison-beta-construction`: normalized
  beta existence and augmentation normalization, stated in
  `Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaConstruction`.
- `new-sfb-finite-free-scalar-derived-comparison-beta-pullback`: pullback naturality
  for a supplied normalized beta, stated in
  `Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaPullback`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaConstruction": "8349c0225a21bb7c48591087b0e84a4072002ca9", "Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaNormalization": "6b03055e38a3adaf4d1af04b3a070afeb4eab17f", "Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaPullback": "f79bf77f64d72568cf32c1d8bdbfec4fd71cef0e"}, "results": {}, "time": "2026-10-28T10:30:52+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
