# L-weak-serre-detour-reroute (2026-10-25, L)

Decision of the human, 2026-10-25: take the agent-invented weak-Serre / torsion-cd detour off
the Lean route by rerouting its two consumers to the blueprint route. No upstream
(`WeilConjectures.*`) statement changed; no module deleted.

## L1. `properLowerStar_uniformBound_ellAdic` (EllAdicProperHeartUniformBound)

Node lem-sfb-noetherian-proper-heart-uniform-bound. Statement unchanged.

- No longer uses `exists_uniform_serreHeart_bound_of_isProper` or
  `exists_uniform_lowerTail_bound_of_isProper`; the imports of QcqsProperSerreHeartBound,
  QcqsProperHullTailBound and LocalizingClosureCtfEqualsBc are dropped.
- New route: a fibre-dimension bound d (`exists_fibre_dimension_bound` and field-extension
  invariance of dimension), the constructible bound 2d+1 for O_F, F and Qbar, the inclusion
  of the weak Serre coproduct closure in the ind-constructibles, and filtered continuity.
- The blueprint lemmas were stated over a finite-type k-scheme with char p>0, while the
  upstream statement only has a Noetherian base. In each of them the base field only made
  the source Noetherian. Each now has a Noetherian form, and the old statement is a one-line
  wrapper of it, so no existing statement changed:

| module | new declaration |
|---|---|
| IntegralProperReductionModel | `integralProperReductionModel_of_isNoetherian` |
| IntegralProperReductionBound | `integralProperReductionBound_of_isNoetherian` |
| IntegralProperConstructibleHeartBound | `integralProperConstructibleHeartBound_of_isNoetherian` |
| ProperHeartBoundRational | `isZero_higherDirectImage_rational_of_isProper_of_isNoetherian`, `isZero_higherDirectImage_padicAlgCl_of_isProper_of_isNoetherian` |
| IntegralExtHomContinuity | `integralExtHomContinuous_of_isNoetherian` |
| IntegralIndConstructibleHeartClosure | `integralIndConstructibleHeartClosure_of_isNoetherian` |
| CoefficientFiniteDescentObjects | `coefficient_finite_descent_objects_of_isNoetherian` |

  The integral completeness step uses `internal_integral_direct_image_limits` and
  `internal_integral_residue_criterion` directly, instead of
  `integralProperDirectImageAndFormulas` (char p). ProperHeartBoundTorsion and
  ProperHeartBoundLattice are not needed on this route and are unchanged.

## L2. `refinementMap_isIso` (CompactificationCoherenceCocycle)

Node det-sf-comp-coherence-cocycle; statement change recorded on the node.

- `refinementMap_isIso` is now the argument of clause (2) of `localizingRefinement_coherence`
  (proper/open interchange, sums, localizing closure, open-closed detection), copied into
  this module as `boundaryVanishing_of_dense` and `refinementMap_isIso`. The import of
  QcqsProperOpenBoundaryVanishing (and the unused CondensedSupportDerivedLocalization) is dropped.
- Density: clause (2) is stated for dense c and d. Its proof uses density only of the
  refining compactification d. The cocycle needs invertibility only for refinements d -> c with
  d dense (the first clause and the comparison construction), so c stays arbitrary and the
  cocycle statement is not restricted. Restricting c to dense compactifications would have
  changed the conclusion that every caller uses.
- `compactification_coherence_cocycle`, `refinementMap_isIso` and `refinementComponent_isIso`
  take the standard k hypotheses: `(k) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]`, X and Y over k, separated, of finite type and quasi-compact, and
  f a k-morphism. The conclusion is unchanged.
- Callers adapted (pass `k`, build the Fact instances from `CharP` where needed):
  RestrictionLocal, RationalAffineAdjunctionCalculus, LocalizingLowerShriekComposition,
  NonrationalLocalizingLowerShriekComposition, RationalP1Triangle, BrownExceptionalAdjoint,
  ExceptionalInverseImageExistence, DetSfCompBaseChangeDefs.
- DetSfCompBaseChangeDefs: `detSfCanonicalCompactificationComparison`, its `_refinement`
  theorem and `detSfCompactificationRefinement_isIso` take
  `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType (Y ↘ Spec k)]`
  (and the last one the base field k); the k-structure of X is built inside from f.
- DetSfCompCompositionBaseChange: `det_sf_comp_composition_base_change` and its private
  helper take the instance binders `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`,
  implied by its hypotheses `_hkp : ringChar k = p`, `[Fact p.Prime]`, `[Fact (p ≠ ℓ)]`;
  the theorem has no callers. Lean record of det-sf-comp-composition-base-change updated.

## Effect

The modules of the detour (WeakSerreSupportedDerivedGeneration,
TorsionCdTopologicalSerreTransfer, SupportedFiniteModelScalarRigidity, ClosedTorsionRigidity*,
ProperWContractibleClosedFibreRigidity, QcqsProper*) are no longer imported by these two
consumers. They stay in the library, unused by them.
