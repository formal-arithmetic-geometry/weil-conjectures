## Reason

The proof fields of the existing public definitions
`CategoryTheory.Functor.mapModCoreMonoidal` and
`CategoryTheory.Mod.comapCoreMonoidal` are completed. Their data, signatures,
imports, and public interfaces are unchanged; the resulting coherence proofs
are proposition proofs only.

## Old

The ten coherence fields were `sorry` proofs in the two existing definitions.

## New

All ten coherence fields are proved by coequalizer projection extensionality
and monoidal coherence lemmas.

## Status

landed 20261020T211809-L-3503268 2026-10-20 (merge of deliver/P2/WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal)

## Users

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence`
