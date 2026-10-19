## What changed

Proved `AlgebraicGeometry.Etale.isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper` with its signature unchanged. No definitions, statement interfaces, or consumers changed. All new imports are proof-only.

The proof first obtains bounded constructibility from the existing proper theorem. On sheaves, proper base change and the exact global-section equivalence over an algebraically closed point turn the specified fibre bound into classical cohomological dimension at most d. The existing general right-derived upper-amplitude theorem then gives [a,b+d] for the direct image of C tensor f^{-1}M. The proper projection formula identifies it with the required tensor for arbitrary M.

This keeps the unit's constructibility, proper-base-change, projection-formula and fibre-cohomology argument. Below that unit route, the already proved general amplitude theorem replaces the spectral-sequence bookkeeping and the full relative projection formula permits arbitrary sheaves directly. `lem-etale-derived-functor-upper-amplitude` and `lem-kun-leray-unbdd` are existing generic tools (the latter Lean-closed); no new mathematical assumptions are used.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper` (node `det-ctf-finite-proper-tor`). Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module. The theorem still depends on the library's stated results; it does not claim that their transitive axioms are all closed.

Validation: the retained proof compiled again against the current library (23.4 seconds), and the version with the unused separably closed cohomology import removed compiled cleanly (20.6 seconds). A direct text comparison confirms the theorem signature is identical to the current source. The required delivery preflight is run by deliver3.py. The signature retains all hypotheses, including hp and hab. Edge cases covered without extra assumptions: empty schemes, zero ring, zero sheaves, d=0, negative a and b, and nonflat or infinitely generated test sheaves. The arbitrary test sheaf is never assumed constructible.

## No longer needed

Removed proof imports:
- `Mathlib.Algebra.Homology.Additive`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`
- `Sheaf.SixFunctors.ProperBaseChangeModules`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`

The following former direct proof dependencies are no longer used by this module (they may remain needed elsewhere):
- `def-kun-constant-sheaf`
- `det-properbasechange-modules`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-module-direct-image-left-exact`
- `thm-sp-truncation-e2`
- `lem-sfb-etale-derived-tensor-stalk`
- `lem-weil-pbc-constant-sheaf-geometric-stalk`

The unused `WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology` import from the retained attempt was also removed. The algebraically closed point equivalence is supplied directly by `Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk`.

No modules are withdrawn. Public statement imports are retained. Direct use of the derived stalk tensor comparison, constant-module stalk comparison, injective representative construction and truncation spectral sequence is unnecessary: classical proper base change gives the sheaf bound, and the existing general amplitude theorem supplies the derived bound. The full relative projection formula treats arbitrary module sheaves. Removed obsolete top-level tool-use approvals for the pruned nodes listed above and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`; no approvals were added.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable hypothesis was found. The earlier proof plan overlooked a shorter implementation using the now available proved `Functor.isLE_rightDerivedFunctor_obj_of_dimension`. The declaration docstring and the node's proof, proof_deps and proof_origin now describe the actual Lean proof. No new node, statement repair, definition repair, forced adaptation, or change record is needed.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
