# K4 purity transport audit

The assigned declaration is not proved. Its explicit statement and inherited binders are
unchanged from `19ba966718`. Merging Houyi #2087 moved the mathematical obligation to
`exists_natTrans_upperShriek_isIso_forget_of_smooth`; that theorem still has `sorry`.
No K4.DONE is warranted by this reduction.

## What the existing condensed purity gives

`SmoothPurity/Defs.lean:450` supplies `smoothPurityIso`, and
`TraceFormula/PurityCompatibility.lean` supplies the tensor formula for arbitrary coefficients.
These are geometric purity results. The chosen unit orientation is an isomorphism, but its
definition falls back to an arbitrary isomorphism when a canonical integral lift is unavailable
(`SmoothPurity/OrientationCanonical.lean:200`). That file explicitly says existence of the
compatible canonical lift has not been formalized.

`SmoothPurity/OrientationBaseChange.lean:121` supplies an existential Tate comparison. It does
not identify that comparison with the prescribed roots-of-unity pullback. Consequently it
cannot by itself prove the square with the native scalar cyclotomic Frobenius datum.

The `SmoothPurity/FrobeniusExchange/*` modules prove scalar evaluation and compact-support
exchange equations. Their exported statements do not identify the chosen purity orientation
or trace with the specified Tate datum.

## A way around canonical-orientation equivariance

Choose the existing smooth trace over the finite base field itself. Pulling it along
`geometricFiberWeilLowerStar` produces a morphism with its canonical Weil structure.
`boundedConstructibleLowerShriekGeometricFiberWeilIso` moves compact support past that pullback.
`SmoothPurityDescendedTrace.lean` implements exactly this construction and its base-change
identity. Its source is the pulled-back, roots-defined condensed Tate complex.

This avoids asking the arbitrarily chosen geometric orientation to commute with Frobenius.
It does not yet identify the trace's source with the native Tate twist, or prove that its
adjoint is invertible after geometric-fibre pullback.

## Remaining comparisons

1. Identify the pullback of the condensed roots-defined Tate line, with canonical Weil datum,
   with `ProEtaleWeilSheaf.toCondensed.obj (WeilSheaf.tateTwistSheaf ... d).obj`. The native line
   is defined by the scalar `cyclotomicUnit ^ d`, whereas the condensed line is a limit of free
   modules on roots of unity followed by extension of scalars. Relevant starting APIs are
   `upperStarMapModTateModuleIsoUnit`, `upperStarTateTwistIso`, and
   `upperStar_map_unitToRootsOfUnitySheaf_comp_upperStarRootsOfUnityComparison`. The missing
   calculation must identify geometric Frobenius on that trivialization with the cyclotomic
   scalar, first on every finite root projection, then on the limit and after scalar extension.
2. Show the adjoint of the descended trace is geometrically invertible, using exceptional
   base change and condensed purity. The field-extension comparison is a separate issue:
   `OrientationBaseChange` assumes all four schemes are finite type over the same field, so
   its direct instantiation with the algebraic closure does not apply. The
   `ModuleObject/DualizingFieldChange/*` modules are useful for the structural morphism.
3. Extend from the unit to all coefficients by a compatible projection formula, and transport
   through `CondensedModelWeilDerived` to the native Weil category. The specified native
   tensor comparison has to be respected here.
4. Handle the unchanged theorem's nonseparated base. The condensed bounded-constructible
   comparison APIs used above require schemes separated over the field; the assigned theorem
   only assumes the morphism `f` separated and the base quasi-separated.

## Shared Sheaf route

The apparent proof in `origin/iface-start` uses unfinished primitives. In particular:

- `lean/Sheaf/WeilSheaf/CondensedTatePairEncoding.lean`,
  `condensed_tate_pair_encoding`: `sorry`.
- `lean/Sheaf/WeilSheaf/CondensedUnitPurityCounit.lean:79`,
  `condensed_unit_purity_counit`: `sorry`.
- `lean/Sheaf/Paper/RationalWeilPurityNaturalityMate.lean:861`: `sorry`.
- `lean/Sheaf/Paper/IntegralEquivarianceMate.lean:79`: `sorry`.

These cannot be imported or ported as completed proofs. The blueprint explains the intended
finite-coefficient normalization, integral reconstruction, rationalization, and descent, but
does not replace these equations in Lean.

## Validated independent constructions

All three new helper modules below and `WeilSheaf/SmoothPurity.lean` passed `ucheck` at
`b7e771038009eb21aa33c8666a4161d59f816525`. The remote logs are
`/home/ubuntu/u9/logs/K4-20261105T024557.log` and
`/home/ubuntu/u9/logs/K4-20261105T025204.log` on `ubuntu@43.131.49.250`.
The checks also rebuilt `UpperShriek.lean`. Independent modules brought in by #2087 were not
all checked; this is a partial-result branch, not a completed leaf or integration claim.

`SmoothPurityOpenImmersion.lean` proves zero Tate twist is the identity and the assigned
adjunction for open immersions, using the existing extension-by-zero adjunction. It does not
invoke general smooth purity. Neither new helper uses K2; K2's intended proof depends on K4,
so the reverse dependency must be avoided.

`SmoothPurityRootsNaturality.lean` supplies the semilinear pullback equation for a finite root
generator: the generator attached to `ζ` is sent to the one attached to `φ ζ`. It derives this
from naturality of `ΓSpecIso`, first for groups of roots, then for presheaves and sheaves.
This equation is ready to specialize to arithmetic Frobenius and its `q`-power action. The
inverse-limit comparison can then use `upperStarFreeTowerIso`,
`upperStarLimitFreeTowerIso`, and `upperStarExtendScalarsLimitFreeTowerIso` from
`TateTwist/TateModuleUpperStar.lean`. The normalization of the resulting limit map, and the
identification with the scalar native Weil line, have not been proved here.

The direct consumers of K4 are the smooth dualizing-object theorem and, via K2, the affine-line
adjunction. The latter general API permits nonseparated bases; its concrete Fourier consumers
use separated affine spaces. This observation does not authorize changing the assigned
statement.

The parallel C4 branch's `TateFrobeniusLevel.lean` at `378c9a1116` builds on
`SmoothPurityRootsNaturality.lean` and specializes the finite equation to the modular cyclotomic
character. It was read but not merged here; its visible check failed before Lean due to the
remote systemd environment. It does not yet supply the inverse-limit/native comparison.

## Route-B assembly status, 2026-11-05 06:39 +0800

The finite-base construction has now passed the remote checker through these interfaces:

- `ProEtaleWeilSheaf.toCondensedAdicConstantDescentIso`: the actual constant native Weil sheaf is the descent of the ordinary finite-base unit, with its Frobenius structure.
- `WeilComplex.finiteBaseNativeDescentUnitIso`: the corresponding native derived unit comparison.
- `WeilComplex.finiteBaseNativeDescentShiftedSheafIso` and `finiteBaseNativeDescentTateIso`: an underived sheaf encoding gives the shifted derived encoding; no monoidal property of the native equivalence is assumed.
- `CondensedRing.boundedConstructibleBaseChangeOfMap_inv_app_hom` and `bijective_map_comp_properTrace_levelwise_of_isIso`: the actual restricted base-change inverse and the proper trace in the exact-pullback coordinates used by descent.
- `WeilComplex.nonempty_upperStar_comp_shriek_iso_tensor_constant`: the compact projection formula reduces the Thom functor to the compact constant object (uses the permitted K5 leaf).
- `WeilComplex.nonempty_compact_constant_iso_of_absolute_purity`: object-level Verdier exchange and ordinary constant homotopy convert absolute purity into compact constant cohomology.

The latest completed audit is `/home/ubuntu/u9/logs/K4-20261105T063140.log` (rc=1). Its two entry failures are explicit normalization mismatches in `SmoothPurityNativeHomSingle` and `SmoothPurityDescendedProperUniversality`; fixes are queued at source `91f44c36a`. The subsequent proper-dualizing, absolute-purity, native tensor/Tate, and Thom assembly modules are drafts pending their first successful checks. They must not be treated as proved merely because their earlier interfaces are green.

C4's `tateTwistSheafCondensedIso d ψ` has the required underived encoding interface, with `ψ := toCondensedAdicConstantDescentIso k₀ l X`. C4 has validated the finite-level, tower, trivialization, pullback, and pullback-naturality layers; the remaining encoding layers are still being checked. No C4 merge or user-proof replacement has been applied on K4 yet. `/tmp/k4-route-b-integration.patch` contains the prepared replacements of the smooth-dualizing user and the trivial-line Thom user. Both avoid K2. The original general relative statement remains unchanged and open, and no K4.DONE is warranted yet.

## Additional validated interfaces, 2026-11-05 07:08 +0800

Geometric descent universality now passes: `bijective_map_comp_geometricFiberWeilDirectTrace_of_isIso` and its smooth specialization are GREEN in `K4-20261105T065604.log` (17s), with the arbitrary-coefficient lemma `geometricFiberWeilDirectTrace_universal` avoiding the concrete kernel conversion. `isIso_upperShriekBaseChange_geometricFiber_unit` is GREEN in that same log (8.6s).

The native internal-Hom comparisons `nativeHomSingleIso` and `nativeHomSourceShiftIso` are GREEN. `nativeConstructibleTensorTateIso` is GREEN in `K4-20261105T070103.log` (3.5s), and `nativeConstructibleTensorTateShiftIso` is GREEN in the ongoing `K4-20261105T070448.log` (6.6s). These validate the natural tensor/Tate comparison needed by the Thom route.

The remaining native proper-trace universality is being profiled after splitting it from the adjunction criterion. Proper-dualizing descent, absolute purity, and the final Thom assembly still await validation. C4's encoding remains separate and unmerged. The original general leaf remains open and unchanged; the user-proof integration patch has not been applied.

## Completed helper chain, 2026-11-05 07:35 +0800

The full SmoothPurityTransportAudit is now GREEN at 339f162b9, log `/home/ubuntu/u9/logs/K4-20261105T072651.log`. This supersedes the earlier pending status: proper trace descent, free Weil universality, proper exceptional unit, compactification, absolute smooth purity, shifted Tate encoding, and conditional Thom assembly all compile. `nonempty_shriekRightAdjoint_adicConstant_iso_of_tate_encoding` and all its absolute-descent inputs depend only on propext, Classical.choice, and Quot.sound. The Thom theorem additionally uses the existing native tensor and projection/Verdier results; a declaration audit is being added to enumerate its remaining leaves.

The only unimplemented integration input is now C4's actual underived Tate encoding. Its finite-level through pullback-naturality chain is green; its module scalar-extension/Weil-structure layer still has a kernel conversion timeout. The general relative K4 leaf remains open, and the prepared downstream replacements remain unapplied. No DONE yet.
