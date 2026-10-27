## What changed

Restored `Sheaf.Paper.PointQuotientTowerHomotopy` from the quarantine path recorded
in `coord/rework.tsv`. Preserved its public interface and five existing proofs.
Completed `WeilConjectures.PointQuotientTower.coherentSource` from a normalized
comparison of strict towers before sections and localization, and K-flatness of
restriction along the completed coefficient isomorphism. The derived assembly
uses the actual universal counit and the exact-functor localization factors;
the canonical isomorphisms compose to the required gamma, whose homomorphism is
definitionally the specified literal composite.

The item publicly re-exports `Sheaf.Paper.PointQuotientTowerData`, containing its
unchanged definitions, and `Sheaf.Paper.PointQuotientTowerCoherentSource`, containing
its completed comparison theorem. Its five previous proofs and their two private additive instances stay in the item.
The comparison module adds proof-only access to the already proved canonical
counit helper in `Sheaf.Paper.AdicCoefficientDatum`, and imports
`Sheaf.Paper.PbcIsoRestrictionKFlat` and
`Sheaf.Paper.PointQuotientTowerStrictComparison` only for its proof. The former
proves K-flat transport by ordinary scalar extension along the inverse isomorphism,
uniqueness of left adjoints, and an isomorphism of total tensor complexes. The
latter isolates the remaining balanced-map comparison before localization.

Folding the derived-functor constructions and respecting their transparency
reduced unfolding, but profiling still showed 18.3 seconds checking the new theorem
and 37.3 seconds in final validation; the combined file took 77 seconds. After
these definition-level improvements, the self-contained definitions and canonical
comparison were extracted into the two modules above to meet the per-file limit.
All original public imports, signatures, bodies of definitions, and attributes
are preserved.

Validation: `lcompile.py --all` accepted all five modules, with no errors or
warnings and every individual compile passing the 60-second gate. All five
existing theorem bodies compare verbatim with the quarantine archive.

The local elaboration changes and extraction are recorded in
`coord/changes/E4-point-quotient-derived-proof-context.md`.

## Proved and sorry left

The archived item had one hole. Closed its original hole in
`WeilConjectures.PointQuotientTower.coherentSource`; no sorry remains in the item.
Added and proved `AlgebraicGeometry.Scheme.pbcIsoRestriction_isKFlat`
(node `lem-trf-pbc-iso-restriction-kflat`).

One new hole remains:
`WeilConjectures.PointQuotientTower.strictPresentationComparison`
(node `lem-trf-point-quotient-tower-strict-comparison`). It concerns only the
normalized isomorphism of ordinary strict towers, for every complex; it makes
no claim about sections, the derived coherent tower, or its universal counit.

This is a decomposition of one original hole into one strictly earlier hole,
not a net hole reduction. The five prior proofs remain intact. No hole was added
inside any definition.

## No longer needed

No existing public or proof import was removed. No module is withdrawn. All
existing proof dependencies remain needed by the retained proofs or constructions.
Removed the obsolete tool-use approval `lem-weil-proetale-isomorphism-inverse-image`
from the item's node: the existing quasi-isomorphism proof uses
`lem-pur-coefficient-pullback-exact` instead, as its proof steps already record.
This does not claim that the former module is unused elsewhere.

## Where the brief, the DAG or earlier work was wrong

The first preflight required separate DAG attachments for both extracted modules.
Added those nodes and updated the parent route; no source proof changed for this
packet repair. Corrected the data node signature metadata to exclude its definition
body, as required by the preflight signature parser. Added the missing LeanSearch search kind for the two original new
nodes after its advisory identified the omission.

The item was absent from `lean/` because it was quarantined, not withdrawn. Its
archived source already compiles against the current server dependencies. The
quarantine row records an import failure through `SfP1ChartExchange`; no change
to that dependency was needed here. The original remaining step bundled the
ordinary normalized comparison with K-flat transport and a derived assembly.
The new nodes separate these mathematical tasks without changing the statement
or bypassing a unit route (`sk-d-weil` has no realized steps for this item).

## New nodes

`lem-trf-pbc-iso-restriction-kflat` states K-flat preservation under restriction
along an arbitrary coefficient-sheaf isomorphism on a scheme's pro-etale site.
Its proof uses the existing ordinary-extension K-flat theorem and the canonical
inverse restriction equivalence. No termwise-flatness hypothesis is required.

`lem-trf-point-quotient-tower-strict-comparison` states only the ordinary
coefficient-presentation isomorphism of complexes of whole strict towers,
normalized on local pure tensors. It is precisely the first part of the source's
coherent-source argument, before the independent derived counit calculation.
Zero and unbounded complexes, and identity coefficient isomorphisms, satisfy
the stated balanced-map argument. Neither new statement duplicates the full item.

`def-trf-point-quotient-tower-data` attaches the unchanged extracted tower
constructions and the existing comparison predicate.
`lem-trf-point-quotient-tower-coherent-source` attaches the completed extracted
coherent-source theorem. These two nodes record the existing parent implementation
after the file split; they introduce no additional mathematical assertion or hole.
The parent proof now cites them. Extraction and local proof settings are recorded
in `coord/changes/E4-point-quotient-derived-proof-context.md`.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
