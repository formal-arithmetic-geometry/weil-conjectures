## Worker report

The module Sheaf.Paper.ClosedScalarDomains states all clauses of
lem-coef-closed-scalar-domains in two named theorems with sorry proofs:
WeilConjectures.closedScalarDomains_scalar and
WeilConjectures.closedScalarDomains_exceptional. Definitions contain actual terms.
The local read clone has no Lean record for this item; Q126's independent review
is a stage-1 split review, not a stage-2 statement landing. The retained sandbox
contained dispatcher brief markers only. No repair note for this item was present.

Hypothesis and clause correspondence:

- The global k = algebraic closure of F_q is D : FiniteFieldDatum. The coefficient
  prime is l with Fact l.Prime and _hl : l ≠ D.p. Both finite extensions E,L have
  Field, Algebra (Padic l), and FiniteDimensional instances.
- Every positive coefficient exponent is represented exactly once by m+1 or n+1
  for m,n : ℕ. closedScalarCoefficient is an abbreviation for the recorded
  Padic.coefficientExtensionRing at that exponent. There is no zero-exponent case
  admitted and no positive-exponent case excluded.
- φ is an arbitrary ring homomorphism of those quotient rings. Its canonical
  RingHom.ulift changes only the value universe. No Flat, finite projective
  dimension, injectivity, surjectivity, coefficient field inclusion, or relation
  between the exponents is a premise.
- T, X, Z : Over (Spec (.of D.k)) have separated, locally finite type and
  quasi-compact structure morphisms. Together the latter two mean finite type.
  The closed immersion is i : Z ⟶ X in this Over category, hence a k-map, with
  IsClosedImmersion i.left.
- The categories are DerivedCategory of ModuleCat-valued sheaves on the actual
  Mathlib ProEt.topology, with coefficient universe u+1 and scheme universe u.
  The canonical finiteCoefficientIntrinsicRealization identifies this presentation
  with the recorded modules over the constant commutative ring sheaf. No site
  morphism universe is equated with the site object universe.
- D^b_ctf is the published finiteTorConstructibleProEtaleModule, namely the exact
  pullback of the recorded intrinsic finiteTorConstructible under that realization.
  The interval premise is the recorded HasProEtaleTorAmplitude on the realized
  input, with explicit a b : ℤ and _hab : a ≤ b. It tests all module sheaves.
- closedScalarExtension is literally pbcFixedScalarExtension on ProEt.topology,
  the left adjoint of actual derived restriction of scalars, so it is ordinary
  uncompleted derived scalar extension. It is not an arbitrary chosen map or
  a completed tensor. The source's lem-pur-derived-change-of-rings module is
  publicly imported, as is the published fixed-scalar interface in
  EtaleDerivedScalarTensor.
- closedScalarDomains_scalar concludes ClosedScalarDomain for K_B at a,b.
  This conjunction contains the recorded intrinsic finite-Tor constructibility,
  the same intrinsic Tor interval, and a bounded constructible ordinary-etale
  origin Q with the same Tor interval, identified by the specified exact
  comparisonUpperStar.mapDerivedCategory.
- The more precise model clause separately quantifies a cochain complex Q of
  ordinary-etale A-module sheaves. ObjectProperty.flat (Q.X q) expresses flatness;
  IsConstructibleEtaleModuleSheaf (Q.X q) is the recorded finite stratification
  constructibility; IsZero in q<a or b<q means support in [a,b]. The first
  Nonempty is an isomorphism ν_A^* Q ≅ K in the actual derived category.
- The scalar-extended terms use etaleSheafExtendScalars φ.ulift, the ordinary
  sheafified balanced tensor, and are explicitly flat and constructible as
  B-module sheaves. Its termwise mapHomologicalComplex gives Q tensor_A B.
  The final Nonempty is ν_B^*(Q tensor_A B) ≅ K_B in the B-linear derived
  category, preserving the B action on the scalar factor. These are derived
  isomorphisms, not merely degreewise isomorphisms.
- C : SfAffineChartPresentation i.left is exactly the recorded arbitrary finite
  affine chart family. C.maxDimension is max d_U with empty maximum zero.
  sfDimension X.left is topological dimension with value zero for the empty
  scheme. The interval is written explicitly as
  a - 2 * (C.maxDimension : ℤ), b + 2 * (sfDimension X.left : ℤ) + 1.
- closedScalarDomains_exceptional asserts ClosedScalarDomain three times, for
  N_A, its ordinary scalar extension, and N_B. The exceptional objects use the
  published sfFiniteExceptionalFixed at Compactification.ofIsProper i.left;
  this is the constructible etale-origin exceptional functor ν^* i^× Rν_*.
  Each conjunction supplies bounded constructibility, the displayed common
  Tor interval over its own ring, and a bounded constructible etale origin
  with that same interval. The geometry and chart constants are shared.
- The scalar assertion is universally quantified over every T and every input;
  in particular it also supplies the model and origin assertions for M and
  for N_A on Z. The input K itself has its stated origin via the displayed
  bounded flat constructible representative Q.

Dependency declarations read and used:

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite and its public import
  CoefficientExtension: Padic.finite_coefficientExtensionRing,
  Padic.coefficientExtensionRing. Positive-level finiteness is already provided
  by ProEtale.sfPositiveCoefficient_finite from the exceptional module.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt, ProEt.topology.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel:
  SheafOfModules.DerivedChangeOfRingsCochainModel and its existence theorem.
  The fixed-scalar specialization is the existing
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension, reexported through
  Sheaf.Paper.EtaleDerivedScalarTensor, which also gives the actual ordinary
  etaleSheafExtendScalars interface.
- Sheaf.Paper.FiniteTorAmplitudeSites: finiteTorConstructibleEtale and the
  reexported intrinsic finiteTorConstructible. The existing
  Sheaf.Paper.FiniteTorAmplitudeProEtaleModule provides its canonical fixed-scalar
  specialization finiteTorConstructibleProEtaleModule; HasProEtaleTorAmplitude
  is from Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude. None is redefined.
- def-weil-scheme-morphism-properties is a convention node with no declaration.
  Use Mathlib Over, IsSeparated, LocallyOfFiniteType, QuasiCompact,
  IsClosedImmersion directly as its record instructs.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients: the recorded
  ConstructibleExceptionalCoefficients.System is reexported from its Data
  module. The finite-level functor used here is sfFiniteExceptionalFixed from
  Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage, also exposed by the
  recorded exceptional definition's import closure. No ambient adjoint is assumed.
- Sheaf.Paper.SfDerivedDirectImage: sfFiniteDerivedDirectImage and its ordinary
  finite direct image proEtaleConstantDerivedDirectImage. This dependency is
  imported as recorded; the node's domain assertion introduces no new image map.
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison:
  Scheme.proEtaleSiteComparison and proEtaleSiteComparisonModules; the latter
  is the specified comparisonUpperStar/comparisonLowerStar adjunction.
- Sheaf.Paper.SfPreservationClass: Scheme.sf_preservation_class, with
  SfAffineChartPresentation, maxDimension and sfDimension from its public
  PurityAffineChartBounds import.
- Already stated proof dependencies are imported non-publicly:
  ProEtaleConstructibleOrigin.constructible_proEtale_origin and
  ComparisonTorInterval.comparison_torAmplitudeIn_iff. The other proof nodes
  lem-sp-etale-scalar-flat-model, lem-sp-etale-chart-comparison-isos, and
  lem-weil-pbc-finite-type-over-noetherian currently have neither a lean record
  nor an upstream audit declaration; they are future proof obligations, not
  missing notions in this statement. No redundant proof-node module is invented.

Edge cases checked: empty T,X,Z and empty chart families are permitted; a=b
is permitted; m=n=0 means positive exponent one, not exponent zero; φ=id and
i=id are permitted; E and L may differ; nonflat Z/ℓ² → Z/ℓ is permitted, as are
all unital maps between ramified coefficient quotients. Since the chart maximum
and sfDimension are nonnegative, a≤b implies the exceptional interval is ordered.
The zero complex may have any ordered interval. No nonemptiness premise is added.

Searches for existing declarations:

- msearch.py leanfinder: “Derived scalar extension of finite coefficient
  constructible complexes preserves Tor amplitude interval and closed exceptional
  inverse image domains”. Eight hits, mainly DerivedCategory T-structure and
  bounded-model existence statements; none states the model plus scalar and
  exceptional clauses here.
- msearch.py leansearch: “Derived extension between finite coefficient rings
  preserves bounded constructibility and the same Tor amplitude interval”. Eight
  ring/module finite-presentation and base-change hits, no exact statement.
- msearch.py loogle: “"torAmplitude"”. Zero hits.
- msearch.py grep: “constructible.*(extendScalars|baseChange)|torAmplitude.*(baseChange|extendScalars)”.
  Zero Mathlib hits.
- rg over lean/WeilConjectures and lean/Sheaf for the item id: no hits.
  Searches for scalar domains, scalar flat models, scalarExtension and
  pbcFixedScalarExtension found the existing functors, etale model infrastructure,
  and the parent FiniteClosedShriek theorem. The parent asserts some finite-Tor
  memberships but supplies neither these same-interval bounds nor the two
  explicit flat-model identifications; it is not an exact existing match.
- blueprint_refs.py search “scalar flat model”: zero blueprint nodes. The DAG's
  already split lem-sp-etale-scalar-flat-model and chart-comparison nodes were
  read as the proof dependencies. No new notion or node is necessary.

No statement correction or disputed statement. The current live split is used
unchanged; only its lean field is supplied. The former superseded-assignment
message concerned the already completed stage-1 split, not this stage-2 task.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
