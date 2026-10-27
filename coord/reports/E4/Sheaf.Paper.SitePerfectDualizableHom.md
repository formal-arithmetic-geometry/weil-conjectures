## What changed

Replaced the single hole in `sixFunctor_sitePerfect_dualEvaluation_isIso` by a complete
combination proof. Finite and integral coefficients use the already proved
`ringedSitePerfectDualityForModel` in the specified ambient models and the new
formal closed-embedding transfer step. One rational argument combines local evaluation
with covering detection, and is reused at every finite coefficient field before
common-stage descent. The original theorem signature and its three public imports
are unchanged. Added four modules and their nodes; updated the item node to this route.

## Proved and sorry left

Closed the original body hole of
`WeilConjectures.sixFunctor_sitePerfect_dualEvaluation_isIso` (one of one original holes).
This is a decomposition, not a sorry-free proof: four holes are added, one in each
new module, with exactly `:= by sorry` bodies:

- `WeilConjectures.closedEmbedding_perfectEvaluation` — `lem-sf-closed-embedding-perfect-evaluation`.
- `WeilConjectures.rationalCover_reflectsIso` — `lem-sf-rational-cover-reflects-iso`.
- `WeilConjectures.rationalEvaluation_cover` — `lem-sf-rational-evaluation-cover`.
- `WeilConjectures.commonStage_perfectEvaluation_descent` — `lem-sf-common-stage-perfect-evaluation-descent`.

The item module has zero holes. No definition contains a hole. Net holes for this
packet are one closed and four added (net -3). The closed-embedding lemma is a
coefficient-independent formal transfer result, the rational-cover lemma proves only
local invertibility, the reflection lemma concerns arbitrary constructible morphisms
without a perfectness assumption, and common-stage descent assumes finite-stage
invertibility. None restates the item under a new name.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `WeilConjectures.Algebra.Homology.HomComplex`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.CategoryTheory.ScalarLocalization`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteProjectiveInternalHomEvaluation`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Sheaf.Paper.SfRationalBoundedConeTorsion`.
- `Sheaf.Paper.SfRationalLocalGlobalPowerTorsion`.
- `Sheaf.Paper.RationalSliceCompletedEvaluation`.
- `Sheaf.Paper.RationalThickEvaluation`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`.
- `Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.Paper.ScalarExtensionExactIntrinsic`.

Replaced the item's direct proof-dependency edges listed below. This does not claim
that the underlying modules can all be withdrawn: the new local and detection lemmas
still use many of them mathematically, and the proved ringed-site theorem retains its
own dependencies. No upstream declaration or module was removed.

- `def-pc-kflat-complex`.
- `def-pc-tensor-complex-sheaves`.
- `def-pur-derived-internal-hom`.
- `def-pur-hom-complex`.
- `def-pur-integral-derived-operations`.
- `def-sf-datum`.
- `def-weil-abstract-derived-category`.
- `def-weil-algebraically-closed-coefficients`.
- `def-weil-derived-complete`.
- `def-weil-derived-complete-integral-detailed`.
- `def-weil-derived-pullback-tensor-hom`.
- `def-weil-finite-type-morphism`.
- `def-weil-linear-scalar-localization`.
- `def-weil-pbc-proetale-site`.
- `def-weil-pbc-strict-perfect-coefficient-package`.
- `def-weil-rationalization-karoubi`.
- `def-weil-site-perfect-complex`.
- `lem-fix-operation-reduction`.
- `lem-pc-bounded-above-flat-kflat-site`.
- `lem-pc-bounded-exact-term-hom-quasi-iso`.
- `lem-pc-finite-projective-internal-hom-evaluation`.
- `lem-pc-kflat-resolution`.
- `lem-pur-derived-change-of-rings`.
- `lem-pur-site-restriction-module-adjunction-exact`.
- `lem-sf-derived-homology-long-exact`.
- `lem-sf-rational-bounded-cone-torsion`.
- `lem-sf-rational-local-global-power-torsion`.
- `lem-sf-rational-slice-completed-evaluation`.
- `lem-sf-rational-thick-evaluation`.
- `lem-sf-triangle-morphism-iso`.
- `lem-weil-integral-constructible-triangulated`.
- `lem-weil-linear-scalar-localization-triangulated`.
- `lem-weil-pbc-degreewise-split-derived-triangle`.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `lem-weil-proetale-countable-products-exact`.
- `lem-weil-scalar-extension-exact-triangulated`.

Removed all old top-level `tool_uses` approvals from this item because its new direct
proof uses only the named combination steps and the proved ringed-site theorem.
The precise old approvals removed are:

- `lem-pc-finite-projective-internal-hom-evaluation`.
- `lem-pc-bounded-exact-term-hom-quasi-iso`.
- `lem-pc-bounded-above-flat-kflat-site`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `lem-pur-site-restriction-module-adjunction-exact`.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-fix-operation-reduction`.
- `lem-weil-integral-constructible-triangulated`.
- `lem-pur-derived-change-of-rings`.
- `lem-pc-kflat-resolution`.
- `lem-weil-proetale-countable-products-exact`.
- `lem-weil-scalar-extension-exact-triangulated`.
- `lem-weil-pbc-localization-module-tensor`.
- `lem-sf-derived-homology-long-exact`.
- `lem-weil-pbc-truncation-triangle`.
- `lem-weil-pbc-hom-into-triangle-exact`.

## Where the brief, the DAG or earlier work was wrong

The finite and integral parts need not repeat the long termwise chain calculation:
the existing model-specific ringed-site perfect-duality theorem already supplies it.
The remaining obstacle is transfer to the datum's specified closed presentation.
The earlier rational plan is retained, including ambient slice categories, so no
constructibility of local terms or integral lifting of rational retractions is assumed.
No existing statement or definition was changed, and no forced adaptations were needed.

## New nodes

`lem-sf-closed-embedding-perfect-evaluation`: Let B and A be categories, P an object property of B, Q a property of opposite-B times B, and H the actual partial internal Hom on Q. Let M be a closed domain on P, N a symmetric closed structure on A, and F:B→A fully faithful with evaluation-normalized ambient closed comparison e. Let O be isomorphic to the ambient tensor unit. For K,L in P, suppose ambient canonical evaluation Hom(FK,O) tensor T → Hom(FK,T) is invertible for every T in A. Then canonical evaluation Hom(K,I) tensor L → Hom(K,L) in M is invertible. These structures and maps are those of [def-sf-datum, lem-sfb-ringed-site-duality-maps].

`lem-sf-rational-cover-reflects-iso`: Fix a finite-field datum D, coefficient datum C, finite extension E of Q_l, and a separated finite-type D-space X. Let g:K→M be a morphism in its intrinsic rational constructible category. Suppose for every pro-etale object V there is a covering sieve R such that, for every arrow U→V in R, the image of g under the constructible-to-ambient rational inclusion and subsequent restriction to the actual slice over U is invertible. Then g is invertible. The intrinsic categories and inclusion are those of [def-sf-datum, lem-sf-coefficient-dual-model-transport].

`lem-sf-rational-evaluation-cover`: Fix a finite-field datum D, coefficient datum C, finite extension E of Q_l, and a finite-type D-space X. Let A be coefficient closed models normalized by the integral ambient realization and rationalization of [def-sf-datum]. For rational constructibles K,M, assume K is site-perfect in the sense of [def-weil-site-perfect-complex]. Then the image of the canonical rational tensor-dual evaluation under the constructible-to-ambient inclusion of [lem-sf-coefficient-dual-model-transport] is invertible on a covering sieve over every object of the pro-etale site, after restriction to each actual slice site.

`lem-sf-common-stage-perfect-evaluation-descent`: Fix a finite-field datum D, coefficient datum C, finite extension E of Q_l, positive finite exponent, six-functor datum S and D-space X as in [def-sf-datum]. Suppose at every finite coefficient subfield of C.Qbar the specified rational closed model has invertible canonical tensor-dual evaluation for every site-perfect first argument and every second argument. Then in the actual common-stage pair category the specified tensor-dual evaluation is invertible for every common-stage site-perfect first argument and every second argument. The site-perfect predicates are those of [def-weil-site-perfect-complex].

Each new statement has a source, proof in words, three kinds of Mathlib searches,
and its Lean attachment. Blueprint searches for closed embeddings, rational evaluation,
and common-stage perfectness found no duplicate of these steps. The nearest rational
retract node concerns split pairings rather than evaluation on arbitrary local bounded
complexes. Edge cases checked in the statements: zero objects, empty perfect support,
rank-zero summands, the empty scheme, and negative cohomological support intervals.
No change record is needed because no existing statement or definition was repaired.

Validation: all four new statements and the complete combination proof compile cleanly.
The item compiled in 24.7 seconds. The first combination-proof check found
a costly `ReflectsIsomorphisms` instance search; the proof now uses the explicit
`fullyFaithfulι.isIso_of_isIso_map` API instead. No timeout limit was changed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
