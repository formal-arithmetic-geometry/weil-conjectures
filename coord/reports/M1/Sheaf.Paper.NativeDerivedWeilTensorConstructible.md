## What changed

Replaced the sole hole of Sheaf.Paper.NativeDerivedWeilTensorConstructible with a
proof using the existing native geometric cohomological criterion, the existing
adic constructibility predicate comparison, and boundedConstructible_tensor_closure.
The geometric fiber receives its finite-type, separated and Noetherian instances,
and Algebra.ringChar_eq transfers the characteristic inequality. Boundedness and
each constructible cohomology sheaf are transported explicitly across the tensor
comparison, then the criterion returns native WeilComplex membership.

Added Sheaf.Paper.NativeGeometricTensorComparison with one intermediate theorem:
AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_tensorComparison.
It compares the two ambient derived tensors, naturally in arbitrary inputs, and
asserts no constructibility. It is strictly the coefficient/tensor identification
step: existing tensor closure and the existing cohomological criterion supply the
rest of the parent argument. No definitions, existing statement signatures,
source-library declarations, or target statements were changed. Original public
imports are preserved; the new imports of the item are proof imports.

The item's proof docstring and DAG proof now describe the implemented route.
The new theorem's docstring and node give the complete balanced-bilinear,
scalar-forgetting, K-flat total-complex and localization argument.

## Proved and sorry left

Original holes: 1, in
AlgebraicGeometry.WeilComplex.nativeDerivedTensor_mem_weilComplex
(node lem-sf-derived-weil-tensor-hom-adjunction).
Its body is now a complete proof from the named comparison and existing declarations.

Added holes: 1, the entire proof of the public theorem
AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_tensorComparison
(node lem-sf-native-geometric-tensor-comparison).
No other textual holes remain in the delivered modules. This is a decomposition,
not a net proof: one upper hole replaced by one genuinely smaller comparison step.
The remaining statement has neither bounded-constructible hypotheses nor their
conclusion, and cannot prove the parent without the existing tensor-closure theorem
and constructibility comparisons.

Validation so far: the new comparison module compiled. The parent's first two
compiles exposed missing scoped instance/closure instance issues; the current proof
uses explicit boundedness and cohomology transport to avoid the latter search.
The next compile failed before Lean started: stdbuf could not create a temporary
directory, reporting No space left on device, exit 125. Final validation is pending.

## No longer needed

Removed direct proof imports:
- Sheaf.Paper.TotallyDisconnectedCoefficientRealization
- Sheaf.Paper.CompletedCondensedCoefficients
- Sheaf.Paper.NativeWeilClosedForgetful
- Sheaf.Paper.CoefficientHeartCommonStratification
- Sheaf.Paper.CartesianCoefficients
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.Paper.ProjectiveCohomologySplitModel
- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
- Sheaf.AlgebraicGeometry.NoetherianStratumDetection
- Mathlib.CategoryTheory.Sites.LocallySurjective

The new route reuses the existing ordinary condensed tensor-closure proof instead
of independently repeating the local stratification, weakly contractible split-model,
K-flat finite tensor and descent calculation. Accordingly, the following old direct
proof edges were removed from the item:

- lem-sfb-totally-disconnected-coefficient-realization
- sk-prop-sfb-qlbar-colimit-x
- lem-sf-weil-native-closed-forgetful
- det-lem-coefficient-heart-common-stratification
- sk-prop-sfb-cartesian-coefficients
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-weil-pbc-proetale-affine-wcontractible-covering-family
- lem-weil-proetale-weakly-etale-localization
- lem-sf-projective-cohomology-split-model
- lem-pc-bounded-above-flat-kflat-site
- lem-weil-pbc-noetherian-stratum-detection
- lem-weil-pbc-site-sheaf-sets-epi-locally-surjective

Some remain transitive dependencies of the reused existing results, notably native
closed-forgetful and coefficient realization; this delivery does not claim that
these modules leave the targets' entire closure. No module is withdrawn. Existing
upstream declarations are all preserved. Removed obsolete top-level tool approvals
are exactly the old direct dependencies above except native closed-forgetful, which
had no top-level tool approval; the finite-type-over-Noetherian approval is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement was found. The original eight-step plan
predates the existing native module/constructibility comparison and existing ordinary
tensor-closure theorem. The reviewer advisory already suggested reusing the latter;
this delivery carries out that route while exposing the coefficient tensor bridge
as its genuine remaining step. There is no change to the unit's statement or route;
its realized statement and step lists are empty, and the tensor input of Step 1 of
fix-lem-tensor-adjunction.proof.md is still supplied.

Edge checks for the new comparison: zero or acyclic inputs yield zero tensors;
empty schemes have the same equivalences and zero modules; degree-zero inputs give
the actual relative tensor; arbitrary shifts preserve the signed total differential.
No boundedness or perfectness is silently assumed. This does not identify derived
Weil objects with fixed pairs of derived ordinary objects.

Searches: LeanFinder returned general LightCondensed monoidal structures,
LeanSearch returned monoidal equivalence transport and expComparison, Loogle gave
mapDerivedCategory and its ordinary functorial comparisons, and Mathlib grep found
no ready-made derived scalar-forgetting tensor comparison. Source searches found
the existing module equivalence, native closed-forgetful tensor comparison, native
geometric constructibility criterion and ordinary tensor closure, and all are reused.
Blueprint search for tensor realization found no exact node. The broader internal
restriction and inflation tensor nodes concern group-action restriction, a different
functor. Dependency traversal of all reused results found no path back to this item.

## New nodes

lem-sf-native-geometric-tensor-comparison, in
 dag/nodes/sec-six-functors/lem-sf-native-geometric-tensor-comparison.json,
attaches the sole new module and theorem. It is the coefficient/tensor comparison
needed before applying the existing ordinary tensor-closure result. Its source is
the sheaf tensor's balanced-bilinear universal property in Stacks sites-modules.tex,
Section Tensor product, and the K-flat total-complex argument in
sites-cohomology.tex, lemma-pullback-tensor-product, composed with the stated native
closed-forgetful comparison. No change record is needed: no existing interface or
definition is changed, and the new theorem has no existing consumers besides the
parent updated in this delivery.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
