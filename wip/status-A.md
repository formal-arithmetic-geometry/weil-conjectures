# Workstream A (KUN) status
## Done
- Item 1: `nonempty_iso_externalProduct_rightDerivedLowerStar` (Kunneth/Relative.lean) builds; only sorry leaf
  is `isIso_tensorBaseChangeMap` (lem-kun-0f1n, other subsection, allowed). Verified with leaf audit.
- Kunneth/Verdier.lean (NEW, compiles): `constructibleFiniteTor_tensorUnit`,
  `nonempty_iso_externalProduct_verdierDual_of_iso` (κ from α,β), `nonempty_iso_externalProduct_dualizingComplex_of_iso`
  (α for 𝟙×b ⇒ M⊠ω≅Rp_X^!M), `hasCompactification_mapOverBase_id`,
  `nonempty_iso_externalProduct_rightDerivedUpperShriek` (α, prop-trf-exceptional-kunneth: SORRY),
  `nonempty_iso_externalProduct_derivedHom` (β, prop-trf-external-hom: SORRY),
  `nonempty_iso_externalProduct_verdierDual` (κ, thm-trf-kunneth-verdier: proved from α,β),
  `hasKunnethComparisons` MOVED here from Comparisons.lean (kunnethVerdier field now proved; α,β fields use the 2 sorry thms).
- Package.lean: added import of Kunneth.Verdier. WeilConjectures.lean: added Formal, ExceptionalSmooth, Verdier.
## In progress
- Kunneth/ExceptionalSmooth.lean (NEW): α for smooth f₁,f₂ via smooth purity. Fixing kernel timeouts
  (maxHeartbeats bumps). Not imported by Verdier until it builds.
- Kunneth/Formal.lean (NEW): cor-sf-duality-pullback `nonempty_iso_verdierDual_leftDerivedUpperStar`,
  `MonoidalClosed.ihomTensorObjIso`, rem-sf-kv-formal `nonempty_iso_derivedHom_rightDerivedUpperShriek_verdierDual`,
  `kunnethVerdier_iff_verdierDual_externalProduct`, `nonempty_iso_verdierDual_externalProduct_of_isDualizable`.
  NOT YET COMPILED: blocked because BoundaryDuality/VerdierBiduality depend on
  LowerShriekCompositionCoherence.lean (other workstream; kernel deterministic timeout at line 63).
## Remaining / dead ends
- Full α, β need the support-dimension dévissage (closed immersions via localization, gluing); not feasible now.
