
## 2026-11-05 — initial inspection
- Read the Lean skill and performance guide; compilation will only use `ucheck`.
- Inspected Houyi #2086 and #2087. #2087 moves upper-shriek definitions out of VerdierDual and reduces our target to `exists_natTrans_upperShriek_isIso_forget_of_smooth`, still unproved.
- Merged pr/2087. Resolved import conflict by retaining both imports; resolved VerdierDual relocation conflict by accepting the moved block while retaining all current proved declarations.
- The target statement is unchanged. Need prove the new purity-map leaf, not merely report Houyi's reduction as a completed proof.
- Current plan: read blueprint transport/equivariance proof and Sheaf route, then build a reusable comparison/adjunction bridge in new modules.

## 2026-11-05 — source audit and alternate route
- Blueprint requires the Frobenius purity/counit square with the specified Tate datum, not an arbitrary geometric isomorphism.
- Shared Sheaf route does not close this missing equation: `lean/Sheaf/WeilSheaf/CondensedUnitPurityCounit.lean:79` is sorry; `Paper/RationalWeilPurityNaturalityMate.lean:861` and `IntegralEquivarianceMate.lean:79` are also sorry. `GeneralTransportBaseChange.lean:55` is sorry.
- Upstream `SmoothPurity/OrientationCanonical.lean` explicitly records that canonical integral lift existence is not formalized; `smoothOrientationOfSmooth` falls back to an arbitrary isomorphism. `smoothOrientation_baseChange` only produces an unspecified Tate isomorphism, insufficient to match `WeilSheaf.cyclotomicUnit`.
- K2 will deduce its leaf from K4, so K4 must not depend on K2.
- Alternate route under investigation: choose purity over the finite base field itself, pull its trace to the geometric fibre with its canonical Weil datum, then extend from the unit by the projection formula. This can avoid proving canonical orientation base-change for an arbitrary chosen orientation.

## 2026-11-05 — independent base case
- Added `SmoothPurityOpenImmersion.lean`: zero Tate twist is the identity; the target adjunction for an open immersion follows from extension-by-zero and the compactification comparison. This does not use the general purity leaf or K2.
- The finite-base workaround additionally needs the comparison of the actual roots-of-unity Tate line with the scalar-defined Weil Tate sheaf. The analogous Sheaf `CondensedTatePairEncoding.lean` theorem is also sorry. No such comparison was found upstream.
- First remote check will validate the open-immersion helper and the merged target module together.
- Added `SmoothPurityDescendedTrace.lean`: constructs the finite-base condensed smooth trace as an actual morphism in the derived category of condensed Weil sheaves, using the existing compact-support/geometric-fibre comparison. Its source is still the actual root-defined condensed Tate line. This is a proved construction towards the alternate route, not a replacement assumption.

BLOCKED: The available sources do not provide the comparison needed for the general Weil-level purity leaf. In upstream, `SmoothPurity/OrientationCanonical.lean:200` chooses an arbitrary orientation when a canonical integral lift is unavailable, and `OrientationBaseChange.lean:121` supplies only an existential Tate comparison. The required specified cyclotomic Frobenius comparison is not implied by either. The shared Sheaf route leaves precisely the needed maps/equations as sorry: `WeilSheaf/CondensedTatePairEncoding.lean` (`condensed_tate_pair_encoding`), `WeilSheaf/CondensedUnitPurityCounit.lean:79`, and `Paper/RationalWeilPurityNaturalityMate.lean:861`. Moreover the condensed comparison APIs assume X and Y separated over the field, while the unchanged leaf only assumes f separated. Continuing the finite-base trace workaround and validating the independent open-immersion case; do not mark K4 DONE on the basis of Houyi's reduction.

## 2026-11-05 — transport audit follow-up
- Checked the lead's FrobeniusExchange hint: those modules give scalar/operation exchange, not the missing orientation/Tate square. Recorded precise source boundaries and a continuation plan in `U9PURITYGAPS.md`.
- Verified textually that both the target statement and its inherited binder block are byte-identical to baseline.
- The first remote check is still queued; baseline completed and K6 currently occupies the shared tree. No local Lean/lake invocation.
- Static import-closure audit: the three requested modules cover both new helpers and SmoothPurity/UpperShriek, but not every independent module brought in by #2087. Broader validation is still required for the merge if retaining it as an integration result.
