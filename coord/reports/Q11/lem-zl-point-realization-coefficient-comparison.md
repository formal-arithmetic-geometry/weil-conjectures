## Worker report

The module `Sheaf.Paper.PointRealizationCoefficientComparison` states the comparison
between the actual raw rational adic point category and the existing finite-matrix
condensed realization, using the specified condensed coefficient inclusion and its
actual left-derived scalar extension. No proof is supplied. All auxiliary data
constructions have explicit bodies; all postponed assertions are named theorems
with source references and proof plans. The auxiliary declarations belong to this
node and will be included in `lean.declarations`.

Clause-by-clause reading:

- The finite-field datum is `(D : FiniteFieldDatum.{u})`. Primality and the unequal
  characteristic hypothesis are `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
  `(E : PadicAlgCl.FiniteIntermediateField l)` is a finite extension inside the
  specified algebraic closure, not an unrelated abstract field. `point D` is
  `Spec (.of D.k)`.
- The small algebraic-closure model has its finite subfield in `Type 0`, whereas
  the recorded adic categories use a field in the scheme universe. `FieldModel`
  is precisely `ULift E.val`; `moduleLift` is the canonical carrier lift and
  scalar restriction along `down`. `fdLift`, `fdLift_equivalence` and
  `fdEquivalence` expose this particular equivalence. Its inverse is selected
  only from a fully specified equivalence, not a mere existence statement.
  No equality of universes or restriction on `D.k` is assumed.
- `coefficientLift` pulls back the actual continuous-function coefficient map
  `up`. Its inverse is coefficientwise `down`. `coefficientRestriction` changes
  only that presentation. The final coefficient objects and inclusion are the
  existing `padicSubfieldRingObj`, `padicAlgClRingObj` and
  `padicSubfieldRingObjToPadicAlgCl`.
- The completed integral full-subcategory agreement is `RawComparison.integral`
  with `integral_identity`. That equation uses the existing completed-ring
  comparison `integralDetailedCoefficientComparison`, whose finite projections
  are prescribed. `RawComparison.rational`, `objects` and `tensors` extend the
  same integral identification to the raw scalar localization, fixing every
  pure Hom tensor through the recorded fraction-field identifications. No
  Karoubi envelope or new integral category is substituted.
- The parameter `r : CondensedERealization.At ...` is the dependency's specified
  realization datum. `realization` is its actual functor on the identified raw
  domain; its encoding followed by the inverse encoding is the existing
  section/internal-module presentation equivalence. `extendedRealization`
  composes it with `derivedExtendScalarsToPadicAlgCl`, exactly the left side.
- `fibre` is `pointRationalFibre` followed by the inverse canonical coefficient
  size lift. `matrixRealization` is this fibre followed by the dependency's
  `rho` and its full inclusion into the ambient derived category. Thus the
  argument of beta is an adic object, while rho receives a vector-space complex.
- `ComparisonStatement` uses one shared `CondensedPointSupertraceData` witness
  for rho, its scalar action and all its matrix models. The theorem supplies
  that witness and the normalized comparison simultaneously; it does not choose
  data from the dependency's unproved mere existence theorem.
- The specified natural isomorphism is the `∃! β` in `ComparisonStatement`.
  Its type is `extendedRealization ... ≅ matrixRealization ...`; naturality
  therefore covers all derived morphisms, not only chain maps.
- `Normalized` quantifies over finite-free completed integral complexes `P`,
  every bounded finite-dimensional frame `F`, every basis and the actual
  point-equivalence identification. `SectionNormalized` fixes that
  identification on basis sections, and the equation using
  `pointRationalNormalization` fixes its derived fibre map.
  `modelCounit` is composed entirely of the specified realization comparison,
  exact-functor localization comparisons and the universal left-derived tensor
  counits. `MatrixNormalized` sends each actual tensor generator to the same
  generator of the dependency's U-valued matrix complex. Thus the degreewise
  matrices are exactly the original matrices through E into Omega, with no
  arbitrary comparison arrow substituted.
- The equation in `Normalized` combines that termwise comparison with
  `smallFrameIso`, which uses the actual inverse size-equivalence unit. The
  point-fibre normalization is the dependency's actual one. This expresses the
  stated combination with the point-equivalence unit.
- Quantification over all bases and representative isomorphisms in
  `Normalized`, and uniqueness of the natural isomorphism, express independence
  of bases, lattices and quasi-isomorphic representatives. Every bounded
  finite-dimensional complex admits an integral lattice after rescaling its
  finitely many differential matrices, as explained in the proof docstring.
- `rawRepresentativeShift` and `ordinaryShiftComparison` are the actual
  quotient/localization and termwise shift arrows. `FibreShiftNormalized` fixes
  the fibre shift against actual section complexes, using the size-equivalence
  counit in `liftedSectionComparison`. `ShiftCompatible` fixes the left shift
  against `modelCounit` and those termwise arrows, then asserts
  `NatTrans.CommShift` with the composite of this normalized fibre shift and
  rho's recorded shift. Thus the two shift structures cannot be chosen merely
  to force compatibility of an arbitrary isomorphism.
- `MatrixUnitNormalized` fixes the matrix model's one-term unit comparison
  against its monoidal unit map, with coefficients acting by the dependency's
  actual scalar multiplication. Together with `Normalized` for the completed
  coefficient module in degree zero, this is the canonical tensor
  multiplication identification, sending one to one.

Dependency declarations read and used (public imports include the underlying
coefficient and category definitions):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`:
  `AlgebraicGeometry.ProEtale.derivedExtendScalarsToPadicAlgCl`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `padicSubfieldRingObj`, `padicAlgClRingObj`,
  `padicSubfieldRingObjToPadicAlgCl`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `coefficientMap`, `upperStarFromPoint`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj` and the
  finite-subextension-valued continuous-function construction.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient-extension
  definitions and `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralDetailedCoefficientComparison`,
  `integralDetailedCoefficientRestriction_exact`, `integralDetailedTransport`,
  `integralStratifiedPerfectDetailed`.
- `Sheaf.Paper.CondensedERealization`: `CondensedERealization.At`,
  `moduleEncoding`, `Integral`, `Rational`, `Coefficient`, `condensedE_realization`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`,
  `pointRationalNormalization`, `pointCompletedSections`,
  `pointModuleRationalization`. These are the actual point-fibre declarations
  used by the ordinary-cohomology interface. Importing the larger recorded
  `CommonStageCompactWeilCohomology` facade initially exposed unrelated universe
  errors in `CoefDerivedSystemEvaluationCalculus`; using this owning smaller
  module avoids that transitive import without changing the fibre.
- `Sheaf.Paper.PointFdComplexes`: `DerivedCategory.pointFiniteDimensional`.
- `Sheaf.Paper.CondensedPointSupertrace`: `PointSupertraceFrame`,
  `CondensedPointRealizationData`, `CondensedPointScalarData`,
  `CondensedPointMatrixData`, `CondensedPointSupertraceData`.
- `Sheaf.Paper.FdCoefficientComparison`: `fdCoefficientTransport` and its
  additivity adapter are reused directly; `fdRawTensor` retains the
  localization's precise module instance. Its `FdRationalStageComparison`
  concerns the different existing `pbcFiniteField` shrink presentation;
  `RawComparison` specializes the same prescribed category identification to
  the ULift model needed by this point comparison.
- The proof docstring uses `point_fibre_equivalence`, `derived_map_lift` and
  condensed flat coefficient calculus from the recorded proof dependencies. Their
  large proof-only import closures are not required to elaborate this statement;
  all declarations appearing in the signature come from the direct imports above.

Edge cases checked before statement completion: zero complex and empty finite
bases; negative and arbitrary integer degrees; one-term coefficient unit;
E equal to Q_l; arbitrary positive characteristic distinct from l; coefficients
in `Type 0` with a scheme in an independent universe; changes of basis and
quasi-isomorphic bounded representatives; arbitrary derived morphisms; shifts
with the usual differential sign. Empty-rank generator clauses are vacuous, but
the natural isomorphism and its uniqueness still apply to the zero object.

Searches performed:

- `msearch.py ... leanfinder "Point realization of adic complexes commutes with
  condensed coefficient extension to algebraic closure"`: eight unrelated
  adic-completion hits; none compares the specified J and rho.
- `msearch.py ... loogle "NatIso, Functor.CommShift"`: no matches (`NatIso`
  was not a known query name).
- `msearch.py ... grep "point.*[Rr]ealization|[Cc]ondensed.*[Cc]omparison"`:
  four generic Mathlib condensed topological-comparison hits; no match.
- `rg` over the upstream project and side `lean/Sheaf`, using point realization,
  coefficient comparison, finite-matrix and rational-fibre patterns, located
  the dependency modules above and `FdCoefficientComparison`, but no existing
  theorem asserting this comparison.
- Searching the exact item id in the upstream source found no declaration.

The auxiliary `moduleDerived` instance names the existing Grothendieck-derived
model at its original module Hom universe. `siteSmall` fixes the unused universe
parameter in `essentiallySmallSelf` to zero, yielding exactly the existing
small pro-etale site at size u+1. Neither introduces a new site or localization.

No statement correction or disputed mathematical assertion is proposed. The
completed-ring, internal/section-module and coefficient-size identifications
are the existing canonical coordinate identifications; they add no mathematical
hypothesis and replace none of the specified constructions.

Self-check of the retained packet (2026-10-18): the initial dry run timed out.
Focused profiling then identified a typeclass heartbeat timeout for
`ordinary.PreservesZeroMorphisms` at the cochain lift. The module now supplies
`ordinaryZero` directly from `ordinaryAdditive`, and `omegaExtensionZero` from
the existing additive coefficient-extension instance. Both are adapters to
existing proofs; they add no mathematical assumptions or postponed assertions.
The normalized comparison statement is unchanged. The three added statement
dependencies (`def-fd-coefficient-comparison-datum`,
`def-weil-point-fd-complexes`, `def-weil-finite-coefficient-point`) already have
landed declarations on `newtargets-dag`. The saved JSON signature matches the
Lean source verbatim; all original dependency ids are retained, auto-implicit
binding is disabled, definitions have explicit data, and all lines meet the
100-character limit.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
