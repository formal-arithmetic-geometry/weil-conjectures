# AlgebraicGeometry.Scheme.derivedTensor_resolution_independent

## Reason

Prove resolution independence with the original theorem signature and the three
existing tensor definitions unchanged. The static interface check also detects
new local notation and declaration-scoped elaboration options, so this record
accounts for those proof-support commands. They introduce no public instance,
notation, definition, or changed statement.

## Old

The original theorem had proof `:= by sorry`. After `resolutionTensorMapQ`, the
original module proceeded directly to its theorem, without private helpers or
local notation. Its existing public context was:

```lean
@[expose] public noncomputable section

set_option autoImplicit false

universe w

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{w}) (A : Type w) [CommRing A]
```

## New

The public context above and all existing declaration signatures and definition
bodies are retained verbatim (apart from whitespace in the theorem signature).
The proof-support notation added after `resolutionTensorMapQ` is:

```lean
set_option hygiene false in
local notation "𝓡" =>
  (constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
    (CommRingCat.of (ULift.{w + 1, w} A))
set_option hygiene false in
local notation "𝓜" => SheafOfModules.{w + 1}
  ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj 𝓡)
```

The two private tensor quasi-isomorphism helpers use declaration-scoped
`synthInstance.maxSize 2048` and `maxRecDepth 2048`; the original theorem also
uses declaration-scoped `maxHeartbeats 800000`. All helpers are proved.
The proof chooses a second-factor resolution locally inside the proposition;
no public data are chosen from an existence theorem. Only proof imports change.
The node's proof, proof dependencies and proof origin describe this argument.

## Users

`tools/downstream.py` finds the five importers below. Its `--uses` search for
`derivedTensor_resolution_independent` finds no downstream reference, only the
original declaration. There are no changed public signatures or definitions,
so no consumer adaptation or target statement review is necessary. No module
held by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted | public interface unchanged |
| Sheaf.Paper.FieldStageOrdinaryRealization | not adapted | public interface unchanged |
| Sheaf.Paper.FieldTorAmplitude | not adapted | public interface unchanged |
| Sheaf.Paper.WeilFourierInversion | not adapted | public interface unchanged |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not adapted | public interface unchanged |

## Status

landed 20261019T005347-L-2757298 2026-10-19 (merge of deliver/M9/Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent)
