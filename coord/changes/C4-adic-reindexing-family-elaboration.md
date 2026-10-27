# WeilConjectures.AdicQbarRealization.integralRealizationAgreement

## Reason

The delivery proposed an elaboration-only repair of the unclaimed module
`Sheaf.Paper.AdicRealizationFamilyData`: file-level `set_option Elab.async false` and a
local section around `integralRealizationAgreement` with
`backward.isDefEq.respectTransparency(.types) true` and local irreducibility of
`Functor.mapDerivedCategory`, `ScalarLocalization.category`, `integralCoefficientLinear`,
`sfIntegralCoefficientLinear`, `sfIntegralConstructibleLinear`.

The repair is not forced. The published source (git blob 2ac0e0e757e) compiles in 48 s
with lcompile at load average ~80-90 (under the 60 s limit; the published build has its
compiled file), and every module of this delivery
(AdicCoefficientRingReindexing, AdicCommonPullbackIdentityUnit,
AdicIntegralReindexingDescent, AdicTensorReindexingModels, AdicReindexingCore) compiles
against the published, unchanged AdicRealizationFamilyData. The original
build-error record of the item ("bad import 'Sheaf.Paper.AdicRealizationFamilyData'") came
from the upstream NativeAdicRealizationData/NativeAdicTensorReindexing failure, which has
since been repaired, not from the elaboration time of this module.

## Old

The published `lean/Sheaf/Paper/AdicRealizationFamilyData.lean`.

## New

Unchanged: the reviewer restored the published bytes (independent review, 2026-10-28).

## Users

None affected: no change is made.

## Status

withdrawn
