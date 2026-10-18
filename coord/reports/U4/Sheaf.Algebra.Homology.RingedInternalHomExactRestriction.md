## What changed

Proved the six additive/finite-limit/finite-colimit restriction instances and the natural
three-variable derived tensor--Hom adjunction in the assigned module. Every existing
signature and public import is unchanged. No definitions or other modules were changed.

Restriction limits are reflected from presheaves of abelian groups. For colimits, the
continuous and cocontinuous slice functors induce left adjoints on abelian sheaves;
the exact conservative forgetful functor reflects finite colimits of module sheaves.

The adjunction follows the existing K-flat/K-injective representative plan. The concrete
functorial flat resolution from KFlatResolutionIndependentCoefficients proves that
P.ι followed by Q is a localization. Existing derivedInternalHom_comparison,
quasiIso_homComplex_map, isKInjective_homComplex_of_isKFlat and
homComplex_tensorTotal_iso then give the natural isomorphism on representatives.
Fully faithful precomposition with the product localization descends it simultaneously
in all three variables. A private tensor-map calculation identifies successive action
of the uncurried bifunctor with the simultaneous action in the currying theorem.

The new proof imports are Continuous, Presheaf.Sheafification, HomotopyCategory.Braided,
and OfFunctorialResolutions. The existing KFlatResolutionIndependentCoefficients import
uses `import all` to reuse its proved concrete resolution and closedness helpers.
The node copy records this proof and removes the unnecessary separate slice-exactness
proof dependency. The two remaining clauses retain their original complete proof plans.

Validation: the final single-file delivery compile and axiom probe passed. The dry run
reported OK with review class CODEX because the existing node proof was updated. All
nine original signatures and all public imports were also compared unchanged.

## Proved and sorry left

Closed 7 of the 9 original holes, with no holes added and no split-offs:

- CategoryTheory.ringedSite_overFunctor_additive
- CategoryTheory.ringedSite_overFunctor_limits
- CategoryTheory.ringedSite_overFunctor_colimits
- CategoryTheory.ringedSite_overMap_additive
- CategoryTheory.ringedSite_overMap_limits
- CategoryTheory.ringedSite_overMap_colimits
- CategoryTheory.ringedInternalHom_tensor_adjunction

The only remaining sorries are the unchanged declarations
CategoryTheory.ringedInternalHom_restriction and CategoryTheory.ringedInternalHom_exact,
both belonging to lem-weil-pbc-ringed-internal-hom-exact-restriction.

Restriction still needs a natural chain-level comparison for arbitrary slice sites and
Over.map, together with its composition equation and descent to derived categories.
The available HomComplexRestrictOpen result is specialized to ringed spaces and gives
an objectwise Nonempty isomorphism; it does not supply this general coherent interface.
Exactness still needs the signed cone maps and coherent CommShift structures in both
variables. The existing separate shift and cone object isomorphisms do not by themselves
specify those structures. No replacement hypotheses or weakened conclusions were used.

## No longer needed

Removed these direct proof imports (some remain available transitively):

- Sheaf.Algebra.Homology.KFlatResolution
- Sheaf.Algebra.Homology.HomComplex
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
- Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
- Sheaf.Algebra.Homology.DerivedInternalHomShiftLeft
- Sheaf.Algebra.Homology.DerivedInternalHomShiftRight
- Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
- Mathlib.Algebra.Homology.DerivedCategory.KInjective
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective
- Mathlib.CategoryTheory.Triangulated.Pretriangulated
- Mathlib.CategoryTheory.Triangulated.Triangulated
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients
- Sheaf.Algebra.Homology.HomComplexMappingCone

The separate dependency lem-pur-site-restriction-module-adjunction-exact is removed from
proof_deps and from proof step 2: the six instances in this module establish precisely
the needed exactness directly from Mathlib. Its attached LocalizedModuleExactForSystems
module is not needed by this proof. No claim is made that other targets no longer use it.

The K-flat-resolution and K-injective-resolution nodes remain needed, but their separate
wrapper imports are unnecessary: the proof uses the existing concrete functorial
resolutions. The cone, triangle and shift node dependencies remain in the plans for the
two unchanged original sorries; they are not being withdrawn.

## Where the brief, the DAG or earlier work was wrong

The module's blueprint tag identifies the correct node, but the current node's lean
attachment points to RingedInternalHomSignedCalculus.normalizedAdjunction_existsUnique,
not the assigned module. Its proof still records the original adjunction, restriction
and exactness clauses. I preserved that attachment and all statements; only proof,
proof_deps and proof_origin are updated.

No mathematical statement was found false. The representative argument requires both
tensor factors in P, as the parameter r specifies, and the proof uses both accordingly.
No pullbacks or extra assumptions on the site are needed for the six restriction instances.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
