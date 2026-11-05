# K4 purity transport status

The general relative theorem `nonempty_derivedLowerShriek_adjunction_of_smooth` is still open.
Its statement, including the original hypotheses, is unchanged. Houyi PR 2087 moved its
obligation into `exists_natTrans_upperShriek_isIso_forget_of_smooth`, which still has `sorry`.
No K4.DONE has been written.

The LEAD-authorized route B is prepared: replace the smooth dualizing-object proof in
`VerdierDual.lean` and the trivial-line Thom proof in `FourierInversion/OtherSections.lean`.
The required absolute-purity and conditional Thom proofs are now validated. The remaining
input is C4's underived cyclotomic Tate encoding. The integration patch is prepared at
`/tmp/k4-route-b-integration.patch` but has not been applied.

## Validated mathematical chain

1. Descend the existing finite-base proper trace to Weil objects, and identify its forgotten
   morphism with the geometric base-change trace. The geometric universal property lifts
   through free Weil resolutions and boundedness.
2. Use that universal property to identify the native proper exceptional unit with descent
   of the ordinary finite-base exceptional unit. The proper-point base-change theorem gives
   the required invertibility without requiring the compactification to be smooth.
3. Restrict along the open part of a compactification and use uniqueness of right adjoints.
   This identifies the native exceptional constant object with descent of the ordinary
   dualizing object. Ordinary finite-base smooth orientation then identifies it with the
   descended root-defined Tate complex shifted by twice the dimension.
4. An underived Tate encoding transports this result to the native Tate twist through the
   derived single-functor and shift comparisons. No monoidal structure on the native
   equivalence is assumed.
5. Object-level Verdier exchange, biduality, and K6's constant affine-line homotopy theorem
   compute compact constant cohomology of the affine line. Compact base change, the compact
   projection formula, and the native tensor/Tate/shift comparisons give the trivial-line
   Thom functor.

`nonempty_shriekRightAdjoint_adicConstant_iso_of_tate_encoding` and all its absolute-descent
inputs use only `propext`, `Classical.choice`, and `Quot.sound`.

The declaration-level audit of `nonempty_trivialLineThom_of_tate_encoding` visits 1789
constants, has no unavailable proof bodies, and finds exactly two direct sorry dependencies:

- K5: `AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso`.
- K7: `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_swap_localization`.

It explicitly rejects K2, the general K4 adjunction, and its PR-2087 reduction helper. The
Thom proof therefore has no circular dependence on relative smooth purity. K5 and K7 remain
sorry in this worktree and must be reported in the final DONE if this remains the dependency set.

## Remaining Tate encoding

C4's intended interface is `ProEtaleWeilSheaf.tateTwistSheafCondensedIso d ψ`, with
`ψ := ProEtaleWeilSheaf.toCondensedAdicConstantDescentIso k₀ l X`. This unit encoding is
already GREEN here. C4's finite-root, tower, trivialization, pullback, and pullback-naturality
layers are green; its integral coefficient/Weil-structure and subsequent encoding layers
remain unvalidated and have not been merged.

Concrete integral pullback/module morphism types triggered kernel timeouts. The upstream
`TateModuleUpperStar` implementation documents the solution: keep the integral coefficient
abstract until after extension to the final rational ring. This is now validated in
`SmoothPurityRationalTrivialization`: `purityRationalTateTrivialization` specializes the root
comparison with only Qbar modules in its result. It is GREEN at `3e120c984480`, log
`/home/ubuntu/u9/logs/K4-20261105T081138.log`, without a heartbeat raise or opacity.

The generic scalar Frobenius law and its coefficient-change transport are written and awaiting
validation. The six validated C4 finite-root modules have been copied unchanged from C4 commit
`fb1a1a08e329`. New local integration files `SmoothPurityTateWeilLaw`, `SmoothPurityTatePowers`,
and `SmoothPurityTateEncoding` connect them to the rational construction; these drafts are NOT
yet validated. No failing integral unit or factorization remains in the stable helper files.

## Validation

- Full absolute-purity and conditional-Thom helper audit: GREEN at `339f162b9`, log
  `/home/ubuntu/u9/logs/K4-20261105T072651.log`.
- Top-level `WeilConjectures`, complete declaration audit, and stable generic scalar helpers:
  GREEN at `24fc7af431`, 131 modules rebuilt, 34482 jobs, log
  `/home/ubuntu/u9/logs/K4-20261105T073946.log`.
- Reduced declaration-audit imports and stronger allowed-leaf guard: GREEN in
  `/home/ubuntu/u9/logs/K4-20261105T075231.log` (the accompanying concrete scalar experiment
  failed, so that batch's overall result was rc=1).

All compilation has used `ucheck`. The remaining work is to finish the actual Tate encoding,
apply the two prepared user-proof replacements, verify their modules and the final audit,
and document the general relative statement as unused by the main proof.

## PR2110 re-plan: canonical orientation (2026-11-05)

The new target is `WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`.
K4 accepted integral reconstruction/trace normalization; C4 handles normalization uniqueness and
Frobenius stability, C1 the actual Weil exceptional datum, Houyi finite/adic comparison.

The named `orientation_existsUnique` at line219 of the interface repository's
`RationalSmoothPurityCanonical.lean` is a literal sorry in an archived comment. Its `orientation`
and `orientation_eq_adic` therefore do not furnish an active proof. The active Native section uses
a normalized family on different objects. `canonicalSmoothPurityIso` from
`SmoothOrientationCoefficientFamily` is an `asIso` of a finite-coefficient map; it supplies no
integral reduction compatibility by itself.

Concrete upstream inputs found:
- `OrientationCanonical.etaleReductionSmoothOrientationIso`: prescribed finite orientations.
- `LiftMorphisms.exists_derivedReduction_map_eq`: existence from actual transition compatibility.
- `EtaleReductionConservative.isIso_of_isIso_etaleReduction_map`: invertibility from reduction1.
- `ReductionTateTwistIntegersModPow.integersModPowReductionTateShiftData`: actual finite Tate datum.
- `ReductionKummerClass.derivedExtendScalars_map_kummerδ`: coefficient compatibility of boundaries.
- `ReductionMonoidal`: tensor comparisons, naturality, unit and braiding equations.

Still required for the canonical transition equation:
1. Instantiate the finite diagonal-orientation coefficient theorem. Its `hframe`, `hε`, `hL`
   hypotheses are not theorems supplied by that declaration. The generic monoidal-supported
   coefficient interface reduces them further, but no actual constructor for coefficient reduction
   was found. Its exceptional tensor compatibility and Kummer/cup/localization compatibilities
   remain to be assembled.
2. Relate that finite coefficient comparison to the actual `finiteEtaleReading` and
   `etaleReductionUpperShriekIso` comparisons at two successive integral reductions. No theorem
   mentioning their transition compatibility was found in the source search.
3. The uniqueness theorem for arbitrary derived-complete targets requires finite shifted Hom.
   For this shifted Tate-line source it should follow from negative-Ext vanishing, not from a
   blanket claim that derived completeness makes reductions faithful.

New helpers under validation: `SmoothPurityCanonicalLift` isolates the exact transition equation
and reconstructs an invertible canonical rational orientation from it;
`SmoothPurityTraceNormalization` identifies the prescribed finite orientation equation with its
counit-trace normalization. These are conditional infrastructure, not a closed target.
