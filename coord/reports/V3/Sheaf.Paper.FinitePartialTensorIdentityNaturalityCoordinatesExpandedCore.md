## What changed

Proved `WeilConjectures.finitePartialTensor_identityNaturality_coordinates_expanded_core`
with its statement unchanged, using the existing public import
`Sheaf.Paper.FinitePullbackTensorFixedCoordinates`.

A proved private helper establishes joint naturality of `tensorCoordinates` from
`Equivalence.unitInv_naturality`. The main proof bundles the coefficient comparisons,
the published bifunctorial upper-star tensor comparison, and the inverse pullback
comparison into natural transformations on the product category. The existing
`pullbackTensor_fixed_coordinates` identifies their components. Their two naturality
squares compose to give the required equation. No geometric assumptions, identity
normalization, projection laws, or new comparison choices are introduced.

The item's DAG proof and proof dependencies now record this explicit argument and
its use of `lem-sf-finite-pullback-tensor-fixed-coordinates`. Local irreducibility attributes keep the already specified partial tensor and comparison
objects abstract during the main calculation; this reduced the profiled compile from
63 seconds to 33 seconds without changing definitions or their downstream visibility.
No shared definition,
public signature, declaration name, or import was changed.

Searches through msearch (LeanSearch, LeanFinder, Loogle, grep) and the local library
found the generic naturality APIs, especially `Equivalence.unitInv_naturality`,
`NatTrans.naturality`, products, whiskering, and uncurrying; no shorter specialized
lemma was found. The library's fixed-coordinate expansion supplies the needed
component formula. The proof uses the same naturality calculation on zero objects
and empty schemes: it only composes functorial maps and isomorphisms.

## Proved and sorry left

Closed 1 hole:
`WeilConjectures.finitePartialTensor_identityNaturality_coordinates_expanded_core`
(node `lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded-core`).
Added 0 holes. There are no remaining `sorry` declarations in the delivered module.
The private helper `tensorCoordinates_naturality_both` is fully proved.

## No longer needed

None. No imports were removed, no nodes or modules were withdrawn, and the original
fixed-coordinate definition dependency is still used. No further split is needed.
The existing upper naturality modules remain callers of the unchanged theorem.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG plan was mathematically correct but omitted the explicit
joint tensor-coordinate naturality proof and the product-category packaging needed
to implement it. The delivery records and proves these steps, rather than splitting
this already repeatedly split obligation again. The unit's route is unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinatesExpandedCore": "6591746ce0df5f28237b975c45df8618d39631cd"}, "results": {"Sheaf.Paper.FinitePartialTensorIdentityNaturalityCoordinatesExpanded": {"hash": "484981ae76565c1e2f05db549b6df61e845a2810", "status": "OK"}}, "seconds": 169, "time": "2026-10-28T14:26:57+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
