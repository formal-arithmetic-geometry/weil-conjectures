# f^! for E and Q̄ℓ through the rational restriction theorem

## Reason

Route audit 2026-10-25 (batch 4 C), approved by the human 2026-10-26. The ℓ-adic f^! of
`UpperShriek` (bounded constructible right adjoint of Rg_*) used, for every coefficient,
`exceptionalInverseImage_exists`, which case-splits over six coefficient kinds and pulls in the
integral and finite restriction theorems. The Q̄ℓ route of batch 4 (Poincaré) needs only sk-thm-restriction.

## New

* `Sheaf.Paper.RationalExceptionalInverseImageExistence` (new):
  `rationalExceptionalInverseImage_exists` for Λ ≅ E or Λ ≅ Q̄ℓ, from Brown representability,
  the compactification cocycle and `rationalRestrictionGlue` only.
* `EllAdicLocalizingExceptionalBounded`, `...ConstructibleCohomology`, `...Constructible`: the proofs
  take the exceptional-inverse-image data as a hypothesis (private `ExceptionalKey`); the existing
  theorems (statements unchanged) feed it from `exceptionalInverseImage_exists`, new `_rational`
  versions feed it from the rational theorem.
* `UpperShriek`: the instances for `continuousMapRingObj E` and `padicAlgClRingObj` use the
  rational versions; the `padicIntegersRingObj` instance keeps the general route.

Effect (constant walk from WeilConjectures.PoincareDuality.Poincare): `exceptionalInverseImage_exists`
is no longer reached.
