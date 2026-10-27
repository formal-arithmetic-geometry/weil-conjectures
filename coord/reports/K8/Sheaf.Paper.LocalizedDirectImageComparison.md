## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.localizedDirectImageComparison_isIso`
in `Sheaf.Paper.LocalizedDirectImageComparison`, preserving both published declaration
signatures and the complete body of `localizedDirectImageComparison`.

The induced norm makes the existing continuous-integral coefficient ring and inclusion
identical to the finite-subfield coefficient ring and inclusion. Adapted the telescope
argument of `ContinuousIntegralPushComparison.integralScalarPushHom_isIso`, removing its
unused constructibility restriction. The proof uses the given lower bound, proves the
mate-unit identity, compares the two cohomology colimits, and reflects the resulting
isomorphism through exact scalar restriction. Four proved private helpers express the mate-unit calculation, zeroth-leg comparison,
the bounded-below telescope argument over an abstract normed field, and equality
transport of the bundled commutative coefficient arrow. No other module is edited.

Updated the node proof and dependencies to this internal-module proof. The blueprint
unit's common-lower-bound localization route is retained. All public imports stay verbatim;
new proof imports are private. No definitions or statements changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.localizedDirectImageComparison_isIso`
(node `lem-sfb-localized-direct-image-comparison`).

Zero holes remain in the item; zero holes were added and zero statements were split off.
The private helpers `mate_unit_comap`, `localization_comparison_zero`,
`bounded_integralScalarPushHom_isIso`, and
`bounded_integralScalarPushHom_isIso_of_eq` are proved.

## No longer needed

Removed private imports:

- `Sheaf.Paper.SectionDerivedPushpullNormalization`
- `Sheaf.Paper.SectionDerivedTensorNormalization`
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore`
- `Sheaf.CategoryTheory.ScalarLocalizationModuleColimit`
- `Sheaf.CategoryTheory.ScalarLocalizationSheafExact`

The internal telescope lemmas already concern exactly the ambient coefficient objects.
Thus the proof no longer needs the section-ring detour or its separate normalization
of the unit. Removed dependency nodes from the item's previous proof route:

- `lem-pd-section-derived-pushpull-normalization`
- `lem-sfb-internal-section-scalar-adjunction`
- `lem-sfb-scalar-change-direct-image-unit`
- `lem-weil-pbc-ring-sheaf-change-adjunction`
- `lem-weil-pbc-scalar-localization-sheaf-exact`

Also removed these obsolete approved tool entries, which the earlier proof docstring
cited but the current node proof dependencies had already omitted:

- `lem-pd-section-derived-tensor-normalization`
- `lem-weil-pbc-condensed-qcqs-pushforward-continuity`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-weil-pbc-scalar-localization-complex-colimit`
- `lem-weil-pbc-scalar-localization-module-colimit`

The proved internal continuous-integral telescope homology and continuity lemmas
provide the precise combined conclusions needed here. The public import of
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` remains unchanged.
The required unit-route import `Sheaf.Paper.CartesianCoefficients` and its node
remain: the canonical Cartesian coefficient identifications underlie the source
restriction/direct-image comparison. No declaration or module is withdrawn. The listed modules may still be required by
other consumers or by the transitive proofs of the retained telescope lemmas.

## Where the brief, the DAG or earlier work was wrong

The separate section-ring normalization is unnecessary. The library's proved
`ContinuousIntegralPushComparison` argument uses only the lower bound of its
constructible input. The same argument applies directly to the arbitrary bounded-below
input of this item, because its coefficient inclusion is definitionally the existing
continuous-integral inclusion under the induced norm.

Compilation initially encountered the launcher outage reported fixed on 2026-10-23;
those requests were retried. Later actual timeouts came from repeatedly comparing the
two valuation-ring presentations inside derived module types. Their coefficient
arrows agree by `rfl`. A private transport helper substitutes equality of their bundled
commutative-monoid arrows before forming these categories. Commutativity witnesses
are read directly from the bundle; tensor instances in the abstract telescope proof
are shared. Scoped backward-elaborator options allow comparison of the equivalent
presentations. They apply only to the five theorem declarations, and the interface
checker reports no changes. No definition, instance or consumer was changed.

The boundedness check also simplifies: the bounded-below derived functor returns an
object with the required property, and its compatibility isomorphism transfers that
property to the ambient direct image. The previous degreewise vanishing calculation
was unnecessary. The complete zero-hole version compiled in 50.7 seconds through
`lcompile.py`. Profiling is removed in the final file; delivery checks compile it and
check its axioms independently.

The first preflight caught an accidental `letI` to `let` edit of the existing
definition and a removed Cartesian unit-route import. Both are restored. A later
preflight caught a file-level elaborator option; it is now scoped to the individual
theorem declarations. The existing definition body and all public imports are
verbatim unchanged.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
