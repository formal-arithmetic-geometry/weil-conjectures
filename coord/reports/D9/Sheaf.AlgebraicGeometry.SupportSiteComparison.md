## What changed

Change record: `coord/changes/D9-support-site-comparison-proof-scopes.md`.

Completed the ordinary support comparison unit by applying the etale support-kernel
functor to the comparison adjunction unit. Its naturality is functoriality of that unit,
and its normalization and uniqueness follow by composing with the monic kernel inclusion.

Constructed the normalized kernel-evaluation isomorphism using preservation of kernels
by evaluation and the kernel map induced by terminal evaluation. Naturality and uniqueness
are checked after the kernel inclusion. A proved private helper identifies terminal
evaluation with the canonical global restriction map.

Proved full-support normalization in both sites: the identity immersion has empty open
complement, sections there are zero, and the kernel inclusions are isomorphisms.
The canonical terminal-evaluation isomorphism supplies the pro-etale global-sections
presentation. Deriving these natural isomorphisms preserves invertibility.

Proved invertibility by normalizing the derived base-change map against the derived
comparison adjunction unit and the composition isomorphism. Applied the existing
finite-coefficient comparison-unit theorem. Proved the forgetting-supports square
by naturality of derived base change and compatibility of bounded-below and
unbounded derived natural transformations.

Proved the uniquely quotient-normalized open pullback of supported constants from
closed base change and the canonical pullback of constant sheaves. Compatibility of
units and the commutative base-change square gives the normalization; epimorphic
quotient maps give uniqueness.

Added the open-restriction comparison by checking its left-mate coefficient square on
quotient generators, then deriving the corresponding square of ordinary right mates.
The canonical exact-derived pullback isomorphism is retained throughout.

Added the exterior-product comparison by checking the ordinary coefficient tensor square
on the epimorphic support quotient. The existing normalized total-complex and derived
tensor APIs lift that square. The two pulled-back evaluation counits transport under the
comparison mate, so the product-support adjunction identifies the requested morphisms.
The existing pro-etale product-naturality module supplies coefficient naturality through
the full morphism-family tensor transport. Naturality cancels the arbitrary presentation
isomorphism `eF` in the final formula.

The generic derived tensor argument performs both the conversion between signed-complex
comparison APIs and the lift from ordinary coefficient squares before specializing to
module sheaves. Keeping type transparency enabled avoids repeatedly unfolding concrete
sheaf constructions. The quotient-adjunction normalization is likewise proved abstractly
before specialization. These are proved private helpers; no extra assumptions are added.

All existing signatures, public imports, definition bodies and docstrings are preserved.
No source-library modules or consumer modules are changed. The unit-route import
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` is retained. The two canonical
constant-functor helper instances are local to private proof sections.

## Proved and sorry left

Closed all eight original holes. Added zero holes, split off zero statements, and left
zero `sorry`s in the item module. Every new private helper is proved.

The complete proof compiled through the required server compiler in 49.8 seconds.
The final item path is also checked before delivery. All 28 existing public declaration
signatures, all 20 existing definition bodies, and the public imports were compared
against the current source and are unchanged. Every line is at most 100 characters.

The declarations whose holes are closed are:

- `AlgebraicGeometry.ProEtale.supportComparisonUnit_existsUnique` (`def-pur-support-comparison-unit`).
- `AlgebraicGeometry.ProEtale.supportKernelEvaluationIso_existsUnique` (`lem-pur-support-site-comparison`).
- `AlgebraicGeometry.ProEtale.fullSupportForget_isIso` (`lem-pur-support-site-comparison`).
- `AlgebraicGeometry.ProEtale.supportComparison_isIso` (`lem-pur-support-site-comparison`).
- `AlgebraicGeometry.ProEtale.supportComparison_forget` (`lem-pur-support-site-comparison`).
- `AlgebraicGeometry.ProEtale.supportOpenConstantIso_existsUnique` (`lem-pur-support-site-comparison`).
- `AlgebraicGeometry.ProEtale.supportComparison_open` (`lem-pur-support-site-comparison`).
- `AlgebraicGeometry.ProEtale.supportComparison_exterior` (`lem-pur-support-site-comparison`).

## No longer needed

Removed these private proof imports, unused by the completed proofs and current definitions:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`.
- `Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison`.
- `Sheaf.AlgebraicGeometry.SupportQuotientFlat`.
- `Sheaf.AlgebraicGeometry.SupportQuotientProduct`.
- `Sheaf.AlgebraicGeometry.SupportedProductQuotientModel`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.

The revised route uses the existing supported-coefficient adjunctions and normalized tensor
APIs directly. No modules or declarations are deleted, and the blueprint unit route stays.
The following old direct proof dependencies are no longer needed by this item; some remain
transitive dependencies of the existing APIs, so this is not a claim of global withdrawal:

- `def-pur-sheaf-tensor-product`.
- `def-weil-extension-by-zero`.
- `def-weil-pbc-composite-adjunction`.
- `def-weil-pbc-extension-by-zero`.
- `lem-pc-derived-adjoint-functors`.
- `lem-pur-derived-support-comparison-direct-image`.
- `lem-pur-support-quotient-flat`.
- `lem-pur-support-quotient-product`.
- `lem-pur-supported-product-quotient-model`.
- `lem-sf-comparison-pullback-exact`.
- `lem-weil-pbc-exact-functor-derived-functor`.
- `lem-weil-pbc-free-yoneda-presheaf-module`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `lem-weil-pbc-site-module-presheaf-sheafification-exact`.
- `prop-pur-kinjective-resolutions-exist`.

The following obsolete `tool_uses` entries are dropped:

- `lem-cbc-proetale-extension-zero`.
- `lem-kun-kflat-criteria`.
- `lem-pod-etale-stalk-tensor-scalar`.
- `lem-weil-pbc-constant-sheaf-geometric-stalk`.
- `lem-weil-pbc-etale-restriction-injectives`.
- `lem-weil-pbc-exact-functor-derived-functor`.
- `lem-weil-pbc-inverse-image-free-etale-module`.
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `prop-weil-pbc-inverse-image-modules-exact`.
- `lem-pur-derived-support-comparison-direct-image`.
- `lem-pur-support-quotient-flat`.
- `lem-pur-support-quotient-product`.
- `lem-pur-supported-product-quotient-model`.


## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The ordinary comparison kernel is literally
the etale support kernel of comparison direct image, so applying the kernel functor to
the adjunction unit constructs it directly. No auxiliary existence lemma is needed.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
