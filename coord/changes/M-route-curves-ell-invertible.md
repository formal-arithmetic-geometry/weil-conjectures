# Compact-support constructibility: torsion invertible on the base, no characteristic-p branch

## Reason

Route audit 2026-10-25 (batch 4 A), approved by the human 2026-10-26.
`properSmoothCurves_prime_higherDirectImage_constructible` and its finite-module version assumed no
invertibility of the coefficient torsion, so they also proved the characteristic-p case
(`prime_charP_constructible`: Artin-Schreier kernel, characteristic-p high vanishing, Frobenius
vector-bundle kernel). The blueprint needs only l-primary coefficients with l different from the
characteristic (Stacks 0GL0 as used by the l-adic finiteness theorems).

## Old

The seven theorems below had no invertibility hypothesis; the prime-coefficient theorem glued the
open piece D(l) with the closed piece V(l).

## New

Each theorem takes `hΛ : ∀ (a : Λ) (s : S), IsUnit (addOrderOf a : S.presheaf.stalk s)`
(for the prime theorem: `hunit : ∀ s : S, IsUnit (ell : S.presheaf.stalk s)`):

* `properSmoothCurves_prime_higherDirectImage_constructible` (proved directly by the invertible-prime
  argument; the characteristic-p branch, the base-change glue and the imports PrimeCurveCharPHighVanishing,
  PrimeCurveArtinSchreierKernel, FrobeniusVectorBundleKernel, ConstructibleCyclicModuleOfAbelian,
  ConnectedFibresConstantDegreeZero are dropped; the modules stay in the library);
* `properSmoothCurves_finiteModule_higherDirectImage_constructible`;
* `constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one`;
* `isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek`;
* `exists_dense_open_affineLine_shriek_constructible`;
* `isConstructibleEtaleModuleSheaf_affineLine_shriek` (the Noetherian-approximation step adds an
  inverse of the characteristic of Λ to the finite generating set);
* `isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate`.

Callers: `finite_localSystem_higherDirectImage_smooth_proper` (ell invertible already assumed),
`proper_directImage_finiteness` (its `hΛ`, previously cleared as unused, is now passed),
`EllAdicProperConstructibleCohomology` (the residue field of O_E has characteristic l; l is a unit
on schemes over k with ringChar k ≠ l) and `IntegralProperBaseChange` (same). Statements of these
callers are unchanged. DAG: the seven nodes carry `statement_change` records.
