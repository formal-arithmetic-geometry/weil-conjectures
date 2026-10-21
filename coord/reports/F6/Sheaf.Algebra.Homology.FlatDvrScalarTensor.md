## What changed

The item keeps its original declarations, statement, coefficient universes and scalar-model definitions. Its proof now combines ordinary DVR Tor, a scalar-resolution comparison, exact realization and the derived tensor unit comparisons. All added declarations are under Sheaf; no adopted source-library file changes.

DvrScalarTor proves the scalar calculation using a finite free length-one presentation, rather than Smith normal form. FlatScalarRealization constructs the canonical additive functor whose object formula is exactly the item's scalarExtension. FlatScalarRealizationExact proves its exactness from the stated flatness hypothesis. FlatScalarRealizationFlat proves that it preserves flat scalar modules, without assuming that the target algebra is flat. FlatScalarTorComparison transports ordinary resolution homology through this exact functor. FlatScalarTensorUnits proves both free-factor clauses directly from the existing K-flat total comparison and explicit complex unitors.

FlatScalarTensorResolution proves the scalar projective-resolution model from exactness, preservation of flatness, bounded-above K-flatness, the proved total-tensor comparison and categorical K-flat augmentation invariance, and the natural ordinary tensor comparison. It transports the augmentation, uses the degree-zero single tensor comparison, and commutes scalar tensor with cochain extension. FlatScalarTorComparison then proves the homology and scalar Tor calculation.

The only new unresolved result is FlatScalarTensorComparison: the natural ordinary tensor identity for this specified constant-then-extension functor. Its source is the tensor universal property in Stacks 03EK/0GMW. It has no derived category, resolution, homology, DVR or finite-presentation conclusion. The exactness, flatness, K-flat resolution model, Tor transport and DVR algebra are written separately with complete combining proofs.

## Proved and sorry left

Closed the item's one hole, SheafOfModules.FlatDvrScalar.flat_dvr_scalar_tensor, by a complete assembling proof. Added one hole, SheafOfModules.flat_scalar_tensor_comparison (lem-sfb-flat-scalar-tensor-comparison). Thus this is a decomposition, closing one hole and adding one, with net hole change zero within the delivered files; it is not a claim of an axiom-free proof of the target closure.

The following new public results have complete proofs: ModuleCat.dvr_scalar_tor; SheafOfModules.flatScalarExtension_additive; SheafOfModules.flatScalarRealization_additive; SheafOfModules.flatScalarRealization_exact; SheafOfModules.flatScalarRealization_flat; SheafOfModules.flat_scalar_tensor_resolution; SheafOfModules.flat_scalar_tor_comparison; and SheafOfModules.flat_scalar_tensor_units. All definitions contain real constructions. The only sorry in this delivery is the named public theorem SheafOfModules.flat_scalar_tensor_comparison. The resolution model uses the proved K-flat total-tensor and categorical bounded-flat APIs; it no longer imports the still-holed fixed-K-flat theorem. Overall closure progress, including any newly reached existing holes, is determined by the project ledger.

The scalar proof handles zero modules and empty finite presentations. The cyclic proof resolves the larger exponent and uses the already proved Tor symmetry when the factors must be exchanged. It requires a nonzero uniformizer, derived from the original DVR hypothesis. The comparison theorem and unit theorem require neither points nor a nonempty site nor a nonzero target ring.

## No longer needed

Removed the item's private proof imports Mathlib.Algebra.Homology.BifunctorShift, Sheaf.LinearAlgebra.DvrMatrixSmithPowers, Sheaf.CategoryTheory.FiniteTypeConstantExact, Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat and Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients. Replaced them with DvrScalarTor, FlatScalarTorComparison and FlatScalarTensorUnits.

The route no longer uses lem-sfb-dvr-matrix-smith-powers (Sheaf.LinearAlgebra.DvrMatrixSmithPowers): finite free kernel presentations compute Tor without diagonalizing an arbitrary matrix. It also no longer uses lem-weil-pbc-finite-type-constant-exact (Sheaf.CategoryTheory.FiniteTypeConstantExact): the specified commutativeSiteConstantModuleFunctor already has a proved exactness API. The equal-universe lem-pc-bounded-above-flat-kflat-site (Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat) is replaced by the proved independent-universe bounded-flat theorem lem-weil-pbc-independent-bounded-flat-kflat. Those three obsolete top-level tool_uses approvals were removed, preserving the order and contents of the remaining approvals.

The intermediate resolution proof also prunes lem-weil-pbc-kflat-fixed-tensor-triangulated (Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated): categorical bounded-flat K-flatness preserves the second augmentation directly. This existing module is retained.

The recorded derived tensor descent and K-flat quasi-isomorphism invariance remain needed transitively through the existing total-tensor comparison. Their approvals are retained. No existing module is withdrawn, and no unit statement or realized unit step is bypassed. The historical split_report is left intact; the current proof and proof_deps describe the new route.

## Where the brief, the DAG or earlier work was wrong

No false statement or target-interface change was found. The old Smith route was a valid plan but unnecessary for the scalar calculation. The stated ScalarModelFiniteFlatResolution result supplies an existential two-term map between powers of the target ring, without retaining the scalar differential; it does not by itself identify the cohomology of that tensor complex as a realized scalar module. The new resolution comparison preserves the scalar chain complex explicitly.

The existing FlatRestrictionExactLeftAdjoint proof supplies an unspecified left adjoint in equal site universes. For the item's fixed object formula and independent site universes, exactness is proved for the canonical functor directly, using sectionwise tensor symmetry and the conservative forgetful functor to abelian sheaves. No existing definition is repaired or replaced.

## New nodes

- def-sfb-flat-scalar-realization: the specified additive constant-then-extension functor, with four public declarations in FlatScalarRealization.
- lem-sfb-flat-scalar-realization-exact: flatness makes that specified functor exact; FlatScalarRealizationExact.
- lem-sfb-dvr-scalar-tor: high-degree vanishing, finite presentation and the minimum-exponent cyclic Tor formula; DvrScalarTor.
- lem-sfb-flat-scalar-tensor-units: both degree-zero ring-sheaf unit comparisons for the recorded tensor; FlatScalarTensorUnits.
- lem-sfb-flat-scalar-realization-flat: the proved preservation of scalar flatness, including projective resolution terms; FlatScalarRealizationFlat.
- lem-sfb-flat-scalar-tensor-comparison: the remaining ordinary tensor comparison for canonical realization; FlatScalarTensorComparison.
- lem-sfb-flat-scalar-tensor-resolution: the proved general K-flat scalar-resolution model, using the ordinary comparison and the proved total-tensor comparison; FlatScalarTensorResolution.
- lem-sfb-flat-scalar-tor-comparison: the proved passage from the resolution comparison to cohomology and ordinary scalar Tor; FlatScalarTorComparison.

All eight nodes inherit the item's chapter and unit and cite the same paragraph (2) blueprint ancestor. No change record is required: no existing statement or definition changes.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
