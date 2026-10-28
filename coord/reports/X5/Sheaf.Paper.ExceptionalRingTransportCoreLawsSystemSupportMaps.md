## What changed

Repaired the returned batch-pair failure against G7's landed delivery
`296120256`. Current `TransportCoreData.reductionF` is a definition derived from
`realizeF`, rather than a structure field. Removed the obsolete `reductionF :=`
assignment from `conjugateSystemF`, retaining its transported `realizeF` and
`evaluationF`. Updated the construction docstring and its node's proof step to
match this interface. No declaration signature changes in this repair.

Marked `exceptional_transport_core_system_support_map` as `STATEMENT-DISPUTED`,
while retaining its original signature, docstring, and one-hole body verbatim.
The datum record does not require its `F` field to be a strictly normalized support
functor. I read the required object theorem, its node, `TransportCoreData`, the
post-functor construction, the system support assembly, the unit record and latest
unit text, and Zheng Construction 5.25 (pp. 36-37). The paper constructs operations
and comparisons; it does not identify every independently chosen representative
strictly.

Added `Sheaf.CategoryTheory.FunctorObjectConjugation`, using Mathlib's `copyObj`
and `isoCopyObj`, with the explicit fully faithful `comparisonNormalizer` and its
strict functor equality theorem. Added `TransportCoreData.conjugateSystemF` and
its object/map formulas in the item. The adjunction and each affected comparison
are transported explicitly, so this is a genuine datum for the exact original
hypotheses. Added two conditional obstruction theorems: one rules out uniqueness
even by heterogeneous equality, and the other specializes to the exact support
map equation. They assume an explicit nonnaturality witness; they do not assert
that such a witness exists for every possible input.

Added `systemSupportFunctor`, `normalizeSystemF`, and the proved strict support
identity for that concrete update. This is a constructive correction for a chosen
support comparison isomorphism and object identifications. The original theorem
about every arbitrary datum remains disputed; no weaker theorem replaces it.

Updated the item node to record the invalid inference and the proved correction.
New declarations are recorded on three new nodes. The new public import is needed
in the datum-update bodies and normalization signatures. No existing downstream
module or adopted source-library file is delivered.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Holes split off: 0.
The remaining hole is
`WeilConjectures.ExceptionalIntegralScalar.exceptional_transport_core_system_support_map`
on `lem-sf-exceptional-ring-transport-core-system-support-law-maps`.
It remains `by sorry`, with the new dispute annotation.

Six new theorems are proved:

- `CategoryTheory.Functor.copyObj_comparisonNormalizer_comp`;
- `WeilConjectures.ExceptionalIntegralScalar.TransportCoreData.conjugateSystemF_obj`;
- `WeilConjectures.ExceptionalIntegralScalar.TransportCoreData.conjugateSystemF_map`;
- `WeilConjectures.ExceptionalIntegralScalar.not_unique_system_map_of_conjugation`;
- `WeilConjectures.ExceptionalIntegralScalar.not_forall_system_support_map_of_conjugation`;
- `WeilConjectures.ExceptionalIntegralScalar.TransportCoreData.normalizeSystemF_support`.

The four new data declarations (`comparisonNormalizer`, `conjugateSystemF`,
`systemSupportFunctor`, `normalizeSystemF`) have complete bodies with no `sorry`.
This delivery is a proved normalization/obstruction partial result, not a claim of
positive net hole progress. The exact support-formula obstruction retains the
existing object theorem in its statement; the more general heterogeneous-map
obstruction and normalization construction do not use that theorem.

Repair validation: compiled the current main `TransportCoreData` (13.6 s), G7's
reduction-law module (7.8 s), the object-support module (6.5 s), the repaired item
(11.6 s), and its unchanged sole direct importer (7.6 s), in import order together
with the generic helper. All six files compiled without errors or warnings.
The four unchanged dependency/importer copies were removed after checking.
The prior temporary axiom probe established that the generic normalization
construction and theorem use only `propext`, `Classical.choice` and `Quot.sound`.
The transport-specific results inherit `sorryAx` through existing dependencies;
no new proof hole or axiom is introduced. The probe is not delivered.

## No longer needed

No existing import, dependency node or module is withdrawn. The public object
comparison import remains necessary to state the unchanged original theorem.
The original data node remains needed through it. The unit's statement and route
are untouched, and no upstream declaration is removed.

The first local version reimplemented functor conjugation. The LeanSearch result
`Functor.copyObj`/`isoCopyObj` replaced that code before delivery. No duplicate
conjugated functor definition, proof-dependency import of an unrelated support-law
module, or further split-off obligation is delivered.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the object component supplies equality of object representatives,
not naturality of those identifications. `TransportCoreData` leaves `F` arbitrary
within its isomorphism class, with its adjunction and comparisons stored as data.
An arbitrary objectwise conjugation keeps those hypotheses valid and preserves the
literal objects, but changes a map whenever the supplied family is nonnatural.
The proved obstruction gives the exact conditional contradiction, rather than
assuming that isomorphic functors must have equal map functions.

The missing repair is to construct/require the chosen normalized datum, or to use
a specified support natural isomorphism and its naturality. Merely adding the map
law as a datum field would repackage this obligation and is not done here.
`normalizeSystemF_support` exhibits the concrete datum update once the genuine
support comparison and object identifications are supplied. Proving the existence
of that comparison for the original geometric data, and reconciling the parent
law package with a constructed normalized datum, are not silently claimed complete.

The object theorem is held by Y8 in the current server records; it is not modified.
The current queue lists this item as proof work. The return for branch head
`5303952ac0c` identified the obsolete `reductionF` field assignment against G7's
newer data interface; this repair removes that assignment. No zero-hole/no-op
shortcut was used.

## New nodes

`lem-sf-functor-comparison-normalization` records the explicit fully faithful
normalizer and its strictification theorem, in the new generic module. Its proof
maps the conjugate through the inclusion, uses the preimage equations and
`NatIso.naturality_1`, and applies `Functor.ext`. All bodies are complete.

`lem-sf-exceptional-system-support-conjugation-obstruction` records the concrete
datum conjugation, the definitional object/map formulas, and the two conditional
obstruction theorems. It transports every dependent datum field and uses only
faithfulness and equality of the displayed right-hand expressions to derive the
contradiction. All bodies are complete.

`lem-sf-exceptional-system-support-explicit-normalization` records the prescribed
support composite, its concrete datum normalization, and strict support equality
for that constructed datum. It assumes a genuine comparison isomorphism and does
not assert it follows from mere object equality. All bodies are complete.

Change record: `coord/changes/exceptional-system-support-map-normalization.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.FunctorObjectConjugation": "8a6cd2da5327712afa87ed840dc22e98d4307616", "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportMaps": "6c7fdaf498c74f65288c2d1b182a73c3f21a7a2c"}, "results": {"Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupport": {"hash": "6d2bef3e85c92b3628d5f2106f8e229088731001", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T15:42:53+0800", "transitive": 0, "version": 1}
```

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
