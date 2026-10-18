# Workstream B status

## New files (dir WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula/), added to WeilConjectures.lean
- ReductionLeft.lean (COMPILES): `HasProjectionFormulaOfCompactification.of_iso_left/right`,
  `isIso_derivedTensorRight_map_projectionMapOfCompactification_of_tensor` (ρ(PF_{K,L}) iso from PF_{K⊗N_X,L}).
  Hypothesis restated with `((-⊗ᴸ-(X)[A]).obj K).obj NX` (not `K ⊗ NX`) to avoid kernel slowness; recheck compiles.
- Torsion.lean (COMPILES): proper base change for torsion bounded-below objects
  (`isIso_derivedBaseChangeMap_app_of_nsmul_id_eq_zero`), geometric-point criterion
  (`isIso_leftDerivedUpperStar_map_projectionMapOfCompactification`, `..._of_forall_algClosurePoint`),
  fibre dévissage over sep. closed field (`hasProjectionFormulaOfCompactification_of_isSepClosed`, PID Λ),
  `hasProjectionFormulaOfCompactification_of_nsmul_id_eq_zero` (PF for torsion K over PID Λ).
- TorsionReduction.lean (IN PROGRESS: maxHeartbeats 2000000 set; rebuild running, log /tmp/B-tr.log; if timeout, bisect)

## Edited
- Integral.lean (NOT YET COMPILED): added `derivedCompleteIntegral_rightDerivedLowerShriek_derivedTensor`
  (sorry, target completeness; replaces removed `derivedCompleteIntegral_derivedTensor_leftDerivedUpperStar`
  + false `derivedComplete_rightDerivedLowerShriek` usage), local PID/domain instances on Shrink 𝒪_E,
  `exists_natCast_mem_maximalIdealShrink_pow`, `isIso_reductionModIdeal_pow_map_projectionMap_of_boundedConstructible`
  (proved modulo TorsionReduction), `isIso_reductionModIdeal_map_projectionMap_of_derivedCompleteIntegral` (proved).
- Rational.lean (NOT YET COMPILED): uses new target lemma; `isIso_reductionModIdeal_pow_map_projectionMap` now direct.
- DerivedComplete.lean: comment WARNING: `derivedComplete_rightDerivedLowerShriek` is FALSE in general
  (counterexample j_! of ∏ (x_n)_*(Λ/ϖⁿ), x_n → 0 in 𝔾_m ⊂ 𝔸¹). Left in place (sk-thm-transport node, other subsection).

## Remaining sorries in my area
- Integral.lean: `derivedCompleteIntegral_derivedTensor_rightDerivedLowerShriek` (source complete),
  `derivedCompleteIntegral_rightDerivedLowerShriek_derivedTensor` (target complete): blueprint argument
  (constructible ⇒ complete) fails on the étale site model (constant 𝒪_E not complete); no honest proof found.
- NO-DECL nodes (pro-étale Loc(Dctf) statements): not attempted.
- FiniteCoefficientChange.lean (lem-coef-finite-direct-image, sorry-free): ADDED to WeilConjectures.lean; build running (log /tmp/B-fcc.log).
- ProEtale/Adic/ProperBaseChange.lean: 2 sorries = thm-weil-pbc-qbar (other chapter), untouched.
