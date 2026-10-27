## Worker report

The module Sheaf.Paper.FieldCohomologyPerfectDescent states the item in two declarations:
WeilConjectures.field_cohomology_perfect_descent_rational and
WeilConjectures.field_cohomology_perfect_descent_qbar. Both proofs are sorry. The only
helper, fieldCohomologyIntegralModelLift, is the actual composite of carrier ULift,
restriction along ULift.ringEquiv, and termwise extension to complexes. It contains
no existence choice and no postponed proof. There are no new nodes or dependency repairs.
The existing def-sc-module-total-hom-complex gains an explicit statement-dependency edge;
its recorded upstream module supplies the signed dual, without a second definition.

Hypotheses and clauses, in order:

* The global datum (p,a,q,k₀,k) is D : FiniteFieldDatum. The coefficient prime is
  l with [Fact l.Prime] and hl : l ≠ D.p. The fixed closure is Ω with Field,
  Algebra (Padic l) Ω, and IsAlgClosure (Padic l) Ω.
* The scheme is X : Scheme, [X.Over (Spec (.of D.k))]. Its structure map is
  X ↘ Spec (.of D.k). LocallyOfFiniteType and QuasiCompact on this map are finite
  type; IsSeparated is separatedness. There is no Weil structure, smoothness or
  properness hypothesis. A quantified Compactification of the structure map is
  the presentation parameter of the recorded compact sections construction, not
  a properness requirement on X. Separated finite type ensures its existence.
* E : Padic.FiniteCoefficientFields l Ω is literally a finite intermediate field
  in the fixed closure. Its field is E.val; its valuation ring is exactly
  Padic.coefficientExtensionIntegers l E.val.
* K_E is an object of sfRationalConstructibleCategory l E.val X. K_R is an object
  of sfIntegralConstructibleCategory l E.val X. _hrep is a Nonempty derived-category
  isomorphism from its raw localization to K_E. Thus any integral representative
  is covered, including representatives related by a rational isomorphism.
* The first conclusion finiteTorConstructibleIntegral l E.val X K_R.obj is the
  recorded predicate: one ordered Tor interval for every positive finite reduction.
* Existential cochain complexes Pₛ and Pₑ are the two integral models. The quantified
  finite set {Pₛ,Pₑ}, bounds a ≤ b with IsStrictlyGE/IsStrictlyLE, and termwise
  Module.Projective and Module.Finite render bounded finite projective complexes.
* The first two Nonempty isomorphisms identify their localized canonical universe
  lifts with integralOrdinarySections and integralCompactSections. Small modules
  are compared to the library's larger point modules by the explicit canonical
  lift; no equality of small-site object and arrow universes is imposed.
* The paired alternatives (P=Pₛ,C=ordinary) or (P=Pₑ,C=compact) enforce the word
  respectively. ModuleCat.extendScalars of the actual inclusion algebraMap R E,
  applied termwise to P, is precisely P tensor_R E, with the canonical commutor
  accounting for the tensor-factor order used by ModuleCat.
* The next isomorphism identifies (ihom C).obj (tensor unit) with Q of
  CochainComplex.moduleHomComplex (P tensor_R E) (tensor unit). This is ordinary
  module RHom into E[0], not the coefficient dual of a sheaf. The module Hom
  differential is d_target f - (-1)^i f d_source, hence (-1)^(i+1) f d_P for
  this target. The degree-i term is canonically Hom_E(P_E^(-i),E).
* The final rational clause applies pointFiniteDimensional E.val to each of the
  two section objects and to each ordinary module dual. This predicate is exactly
  finite support of cohomology and finite-dimensionality in every integer degree.
* For each common-stage K, the second theorem chooses F and K_F : Stage l Ω X F,
  with Nonempty (K ≅ ⟨F,K_F⟩). F is the requested finite field of definition.
  The canonical Coefficient l Ω F is the small Shrink model already used by the
  dependency; fieldDerivedScalarExtension along Shrink.algEquiv transports its
  rational sections back to the actual subfield F.val.
* Cₛ,Cₑ are complexes of F.val-vector spaces. The four-element set consisting of
  them and their two moduleHomComplex signed duals has bounded support and
  termwise finite-dimensional vector spaces. hₛ,hₑ,hₛd,hₑd record membership of
  their derived images in the existing finite-dimensional point category.
* The two stage-section isomorphisms and two PointFdQbar isomorphisms assert that
  the ordinary/compact images are represented by (F,Cₛ) and (F,Cₑ), respectively.
  The two following derived isomorphisms identify the ordinary module duals of
  their realizations with the realizations of (F,Cₛ^∨) and (F,Cₑ^∨). PointFdQbar
  is the recorded induced-category realization, so this is precisely representation
  of the dual objects in the common-stage category; no arbitrary dual map is assumed.
* Finally one pair of bounds a ≤ b works for all four displayed common-stage pairs.
  coefficientQbarCohomology gives literally scalar extension of H^i at F.
  FiniteDimensional Ω in every i and IsZero for i<a or b<i state exactly the
  finite-dimensionality and vanishing clauses. Zero cohomology here is IsZero
  of a ModuleCat object, never IsZero of an unstructured Type.

The declaration universes use the common ambient universe of the recorded point
categories, with the pro-etale module universe still u+1 and small projective
models in u. The existing derived localization instance is locally prioritized
using `attribute [local instance 10000] HasDerivedCategory.ofIsGrothendieckAbelian`.
This is the existing upstream construction, not newly declared data. Consumers
using these signatures can enable that same existing instance. Its priority is
needed because an inherited module-derived instance otherwise makes instance
search select an incompatible localization universe.

Dependency declarations read and used:

* Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses:
  CategoryTheory.derivedInternalHomOfUniverses gives the ringed-site convention;
  the ordinary module specialization is the existing closed derived monoidal
  structure, with its projective model below.
* Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients:
  WeilConjectures.generalAlgebraicallyClosedConstructibleCategory and
  GeneralAlgebraicallyClosedCoefficients.Stage, with literal finite-stage pairs.
* Sheaf.Paper.SfIntegralConstructible:
  WeilConjectures.sfIntegralConstructible and sfIntegralConstructibleCategory.
* Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum.
* Sheaf.Paper.FiniteTorAmplitudeSites, publicly importing FiniteTorAmplitude:
  WeilConjectures.finiteTorConstructibleIntegral; the etale finite-level predicate
  is not substituted for this integral pro-etale condition.
* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite, publicly importing
  CoefficientExtension: Padic.coefficientExtensionIntegers and its field-extension
  data (the primary finite_coefficientExtensionRing is not needed at this field stage).
* Sheaf.Paper.CommonStageCompactWeilCohomology, publicly importing the original
  OrdinaryCompactCohomology: integralOrdinarySections, integralCompactSections,
  rationalOrdinarySections, rationalCompactSections, qbarOrdinarySections and
  qbarCompactSections. The primary commonStageCompactWeilCohomology retains Weil
  action for a separate clause of that dependency and is not substituted here.
* Sheaf.Paper.SfRationalizationKaroubi: sfRationalConstructibleCategory and
  sfRationalConstructibleLocalization, with unchanged objects and no Karoubi envelope.
* def-weil-scheme-morphism-properties is a convention node. Its named properties
  are Mathlib LocallyOfFiniteType, QuasiCompact and IsSeparated.
* Sheaf.Paper.PointFdQbarCategory: DerivedCategory.PointFdQbar and
  pointFdQbarRealization. Its objects are actual finite-field pairs.
* Sheaf.Paper.CoefficientCohomologyModules: DerivedCategory.coefficientQbarCohomology;
  the same module's coefficientFdCohomology is used by the rational section interface.
* WeilConjectures.Algebra.Homology.ModuleHomComplex:
  CochainComplex.moduleHomComplex, the existing signed complex.

The stated proof-dependency modules are imported without public visibility:
IntegralResidueTor, SfDerivedDirectImage, QcqsCompactSupportRealization,
FiniteCoefficientPoint, ProjectiveHomEvaluationModel, PerfectRingComplexGeneral,
the upstream Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
IntegersLocalizationUniformizer. CommonStageCompactWeilCohomology,
SfRationalizationKaroubi, GeneralAlgebraicallyClosedCoefficients,
PointFdQbarCategory and CoefficientCohomologyModules already have public imports
because the signatures use them. The proof dependencies
lem-sf-integral-sections-perfect-reduction and lem-pod-perfect-dual-scalar-calculus
have no recorded Lean modules on the inspected base; their proof steps remain
explicitly documented for stage 3. They are not assumed as extra hypotheses.

Edge cases checked: the empty scheme and the zero complex permit zero projective
models and any ordered zero support interval; no nonemptiness or nonzero bound is
required. Integral torsion representatives may rationalize to zero; the rational
isomorphisms do not claim their integral cohomology is nonzero. Arbitrary integer
shifts and negative degrees are covered by integer bounds; signed dual bounds
reflect the original support. The base field E=Ql and repeated finite fields are
allowed by FiniteCoefficientFields and the recorded scalar tower. No degree,
cohomology interval, compactification or finite field is required to be nontrivial.
The generic finite-type separated scheme is not restricted to one equipped with
Weil descent, smoothness or properness. No statement correction or disputed flag.

Searches made:

* msearch.py leanfinder, query: “Rationalization of integral perfect etale cohomology
  complexes gives bounded finite dimensional models and their signed duals over
  finite coefficient field stages”. Eight hits about BDeRham, etale algebras and
  cotangent complexes; no matching statement. Exact returned hits are in searches.jsonl.
* msearch.py loogle, query: `DerivedCategory, "rational"`. Zero hits.
* msearch.py grep, query:
  `(rationalization|[Rr]ational).*(cohomology|[Pp]erfect)|cohomology.*[Ff]inite[Dd]imensional`.
  Zero Mathlib hits.
* rg of lean/WeilConjectures and lean/Sheaf for the item id and expected
  fieldCohomologyPerfectDescent/field_cohomology_perfect names: no prior declaration.
* rg of Sheaf/Paper for rational perfectness and signed duals found
  PoincarePointFiniteness and related scalar/duality interfaces. The former
  assumes a PoincareDualitySetting and gives only finiteness/dualizability; it
  does not state these models for an arbitrary separated finite-type X.
* Read the dependency modules and their complete relevant signatures/docstrings,
  the live CommonStageCompactWeilCohomology via scompile --source, and the exact
  blueprint Step 3. The older phrase “possibly up to a direct summand” in that
  source paragraph is superseded by the node's explicit raw-localization convention;
  no summand hypothesis or Karoubi completion is introduced.

Validation: all delivered declarations were checked in module mode with scompile.py.
The source contains no auto-bound implicits. No library build or direct live-tree
mutation was run. The final delivery dry run and compile are recorded by deliver2.py.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
