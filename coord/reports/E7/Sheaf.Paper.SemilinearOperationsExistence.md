## What changed

The existence result is assembled from geometric, scalar-extension, and open-localization branches. Open localization uses the actual open restriction functor, its left adjoint, the canonical evaluation mate, and exact derived adjunction. The sequence evaluation theorem is generalized to independent site object and morphism universes, which the slice category requires. Its coextension proof is unchanged. All five packet modules compile; the final delivery gate rechecks the warning-free packet.

## Proved and sorry left

Closed: WeilConjectures.SemilinearSections.semilinearOperationsData (one original hole), by decomposition and an explicit open-localization construction.

Remaining new holes:

- WeilConjectures.SemilinearSections.openRestrictionEvaluationSections (lem-coef-open-restriction-evaluation-sections).
- WeilConjectures.SemilinearSections.semilinearGeometricOperations (lem-coef-semilinear-geometric-operations).
- WeilConjectures.SemilinearSections.semilinearScalarOperations (lem-coef-semilinear-scalar-operations).

This is a decomposition, not a net proof: one original hole closed, three lower holes added. The generalized sequenceModulePullbackEvaluation_isIso has no holes. No hole remains in the item module itself.

## No longer needed

No original dependency is claimed globally pruned. The geometric and scalar dependencies remain needed by their respective branches. Experimental private helper modules are not included in this packet. The module Sheaf.CategoryTheory.LocalizedModuleExactForSystems remains used. The new exact derived-adjunction proof uses def-weil-exact-derived-adjunction; the former generic lem-pc-derived-adjoint-functors is not needed by this branch, although its declaration remains in the library.

Removed proof imports from the assembly module (their branch-specific dependencies remain in the new nodes):

- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
- Sheaf.CategoryTheory.RingedSliceExtensionTensor
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
- Sheaf.Paper.KFlatRingedToposPullback
- Sheaf.Paper.ProjectionMateExact
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.RingedTopoiDerivedPullback
- Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

## Where the brief, the DAG or earlier work was wrong

The sequence-evaluation theorem's docstring and DAG advertised independent site universes, but its Lean signature required the two sites to share object and morphism universes. Open localization has source Over U in max c v and target C in c. The generalized coextension argument compiles. The current downstream scan reports 2850 transitive importers and only AmbientPullbackTensorCoherence as an external declaration user; its application leaves universes implicit and specializes the new statement unchanged. No consumer needs adaptation. No mathematical hypotheses or target signatures change. The retained packet also contained a scoped heartbeat option before a universe command, and used two slice-ring presentations in exactness inference. The scoped option is removed; the short-complex comparison now uses three explicit component isomorphisms. Normal transparency settings are retained, and the section variable in the open comparison is typed through its source composite to avoid an expensive kernel conversion.

## New nodes

lem-coef-semilinear-geometric-operations: the geometric branch (inverse-image tower, normalized derived adjunctions, tensor and transition comparisons) of Construction 4.1.

lem-coef-semilinear-scalar-operations: coefficient extension on the ringed sequence site, with evaluation fixed by the scalar restriction transpose.

Change record: coord/changes/sequence-evaluation-independent-sites.md.

lem-coef-open-restriction-evaluation-sections: the identity-on-sections restriction comparison, stated on the source composite carrier to avoid expensive equality checks. The remaining open-localization construction is a complete proof from this comparison. Edge cases: empty C makes the open clause vacuous; n = 0 is the same restriction square; no invertibility or flatness of the tower maps is assumed by any of the three new statements.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
