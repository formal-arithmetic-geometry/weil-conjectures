## What changed

Replaced the proof of `WeilConjectures.podReindexingIdentityCompatibility` without
changing its signature, its public import, or any shared definition. Added private
proof imports of `PodIdentityLimit`, `PodIdentityTensorRoos`,
`PodIdentityDerivedFactors`, `SfIntegralConstructibleTriangulated`, and the private proof
API of `IntegralOperationsWellDefined`.

The main proof now derives the limit equation on arbitrary systems by localization
from a strict restricted-tower equation and a proved Roos-coordinate calculation.
It identifies the two normalized Roos models by their values on K-injective
resolutions. A general adjunction argument derives the reduction equation from
the limit equation using Unit. The tensor equation is proved on good
representatives using Model and naturality of the completed-tensor comparison,
then transported to all constructible inputs using good localization.

Added six modules. `PodIdentityRestrictedTower` proves the section calculation
using the actual coefficient restriction functor, casts, system-unit normalization,
and the identity-site maps. `PodIdentityRoosMap` proves the generic product and
mapping-cocone calculation using both coordinates. `PodIdentityTensorTower` states
the remaining strict finite-tensor calculation separately from the derived proof.
Local irreducibility attributes prevent expansion of large operation definitions;
no global attributes or definitions change.

Validation: all seven modules compile in import order. The final item compile
was clean at 51.4 seconds; the current limit proof compiled at 54.2 seconds.
Every delivered file is below the 60-second limit.

## Proved and sorry left

Closed the original hole in `WeilConjectures.podReindexingIdentityCompatibility`
(node `lem-pod-reindexing-identity-compatibility`) by a complete Lean proof from
the stated model laws and the strict-tower lemmas.

Added and proved `WeilConjectures.podIdentityRestrictedTower`
(node `lem-pod-identity-restricted-tower`) and
`WeilConjectures.podIdentityRoosMap` (node `lem-pod-identity-roos-map`).

Also proved `WeilConjectures.podIdentityLimit` (node `lem-pod-identity-limit`)
and `WeilConjectures.podIdentityTensorRoos` (node `lem-pod-identity-tensor-roos`).
These contain self-contained parts of the original proof, with no new holes.

Also proved `WeilConjectures.podIdentityDerivedFactors`
(node `lem-pod-identity-derived-factors`), sharing the generic derived-category
factor argument between the limit and tensor proofs.

One new hole remains: `WeilConjectures.podIdentityTensorTower`
(node `lem-pod-identity-tensor-tower`). Its proof is exactly `by sorry`.
It concerns only the strict finite tensor tower on good complexes, assuming only
QuotientGenerators, Generators, and the section identity. It has no reduction,
limit, derived tensor comparison, constructibility, or derived localization in
its conclusion. Its docstring and node give the generator-and-sheafification proof.

Thus this is one original hole closed and one strictly smaller hole added: a
decomposition, not a claim of a net hole reduction. No other holes are added.

## No longer needed

No original import is removed and no module is withdrawn. All five original DAG
proof dependencies remain used. The new proof does not use Counit to derive the
reduction identity: Unit, the limit equation, and adjunction naturality suffice.
It does not separately prove identity equations for every finite derived
reduction, nor assume finite evaluations are faithful. The quotient-generator
calculation is needed only inside the strict tensor-tower lemma.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The plan overstates what is needed for the
adjunction step: the unit compatibility alone suffices. The concrete restriction
API is expressed with cast section identifications, so the restricted-tower proof
also needs functoriality of those identifications and the system-unit section
formula; these are proved directly from the existing construction.

## New nodes

`lem-pod-identity-restricted-tower` records the proved identity on the restricted
strict tower. Its only model hypothesis is RestrictedGenerators; system-unit
normalization comes from its defining theorem.

`lem-pod-identity-roos-map` records the proved generic Roos compatibility. Its two
coordinate hypotheses, together with the product comparison and naturality of an
ordinary identity isomorphism, imply equality of whole cochain maps.

`lem-pod-identity-tensor-tower` records the remaining strict tensor-generator
calculation. It is one part of the original tensor argument, before applying Roos,
localization, representative Model, and transport to arbitrary inputs.

The original node's proof, proof dependencies, and proof origin now follow the
Lean proof. No change record is needed: no other existing module or node changed.

`lem-pod-identity-limit` records the proved total-limit part of the original
identity theorem; its module contains the normalized-Roos uniqueness and
localization argument. `lem-pod-identity-tensor-roos` records the proved passage
from the strict tensor tower to the whole cochain comparison. These self-contained
proved parts were placed in separate modules after local irreducibility improved
the large definitions and profiling still showed the combined file exceeded the
compile limit. No compile limit or heartbeat limit was raised.

`lem-pod-identity-derived-factors` records the proved evaluation formula for the
derived identity at Q(K). Its module imports only the existing ExactFunctor source
API. This replaces duplicate private proofs in the limit and tensor modules.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodIdentityDerivedFactors": "e54c13275d614385dc272dca4d21f69a53f10c62", "Sheaf.Paper.PodIdentityLimit": "5fd3febb87c2c398c484d5a7247d9093861d1341", "Sheaf.Paper.PodIdentityRestrictedTower": "ab90838eb607144896f868cf3cbefdc675bdfa3f", "Sheaf.Paper.PodIdentityRoosMap": "7684380c2d39668706f5c3df64867cadc8aa7303", "Sheaf.Paper.PodIdentityTensorRoos": "8e44a6bfcc20f3b6f3988031a10682959429e10a", "Sheaf.Paper.PodIdentityTensorTower": "ba5e727431d76da436adcca13959b2eac00da81b", "Sheaf.Paper.PodReindexingIdentityCompatibility": "42d7bbfaf7232c238b4eac8d45cd787925d439c5"}, "results": {"Sheaf.Paper.PodReindexingTensorFamilyIdentityComposition": {"hash": "a0e22bc2a1edada26de7b50c444b3da25be15ae9", "status": "OK"}}, "seconds": 55, "time": "2026-10-28T11:04:53+0800", "transitive": 0, "version": 1}
```

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
