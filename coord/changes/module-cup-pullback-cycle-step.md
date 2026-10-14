# moduleCup_pullback_cycle_step restoration and proof

## Reason

Repair both points of the returned delivery. Restore the withdrawn module and its
DAG node with the two original public theorem signatures. Replace the proof's use
of the broader pullback-naturality theorem by the existing computing-resolution
maps and explicit kernel-cycle constructions.

The required cup-product import formerly failed in the non-module batch probe due
to duplicate anonymous local instance names in ModuleCupNaiveDerivedCompatibility
and GlobalTensorPullbackMonoidalNormalization. This was reproduced locally; naming
all anonymous instances in the former module fixed it. During this repair the same
fix landed independently in bbf7d9a0cc (Q4). The sandbox upstream edit was removed.
The delivery uses the landed moduleCupCompatibility instance names and includes
no edit of either upstream module. The original failed plain import now passes
against the published library, without a sandbox overlay.

## Old

The module and its node are absent from the current branch following batch
withdrawal. The return records two declarations with the signatures retained
verbatim in the restored source: moduleCup_pairing_exists and
moduleCup_pullback_cycle_step. The former is proved; the original split source
had a sorry for the latter. Later returned attempts applied
moduleCup_pullback_naturality to the two represented input classes.

## New

Both public theorem signatures and visibility are retained exactly.
moduleCup_pairing_exists still applies exists_moduleCupResolutionPairing.
moduleCup_pullback_cycle_step takes computing pairings P,E and their three maps
from moduleCup_pullback_resolution_maps. Surjectivity of each computing class map
lifts the given input classes to P; Leibniz constructs their paired cocycle; the
three additive cochain maps transport those cycles and preserve the pairing.
The two IsModuleCupProduct characterizations and the three class equations prove
the conclusion. All three private helpers are proved; there is no new sorry.

The statement imports are ModuleCohomologyCupProduct, ModulePullbackTensor and
ModuleCohomologyFMap. The latter replaces the broader public
ModuleCohomologyFMapFunctorial import, whose theorems this proof does not use.
ModuleCupPairingExists and ModuleCupPullbackResolutionMaps are proof-only imports.
The former proof-only CechCupPullbackCompat import is removed.

The restored node describes this proof and the same unchanged Lean statement.
Its prose arrow is corrected to f:X-prime to X, matching the original Lean binder.
No target statement or mathematical definition changes. No existing source imports
the withdrawn item; no other source needs adaptation. The only upstream collision
repair is already landed independently and is not part of this delivery.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupPullbackCycleStep | K4 | Restored exact public signatures; complete resolution-cycle proof. |

A full source search found no current importer or use of either restored declaration.
The independent collision repair's direct importer ModuleCupEqualDerivedMapsClass
was also compiled unchanged against the experimental fixed instance overlay and
needed no source adaptation; its source is not delivered here.

## Status

landed 20261014T122102-L-2664772 2026-10-14 (merge of deliver/K4/Sheaf.Paper.ModuleCupPullbackCycleStep)
