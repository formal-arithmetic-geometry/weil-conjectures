## Worker report

The module `Sheaf.Paper.PurityAffineLineBoundaryRealization` states
`WeilConjectures.PurityFiniteSetting.affine_line_boundary_realization` with a single
`sorry`. Its auxiliary declarations contain real constructions and propositions;
there is no chosen arbitrary morphism, hollow definition, new node, dependency
repair, or statement correction. The existing DAG statement is unchanged.

The source read is blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`thm-pur-affine-line-orientation.proof.md`, first paragraph and final site-comparison
sentence, together with `lem-pur-gysin-structure.md` and the assigned node's seven
proof steps. The theorem docstring carries all seven steps and their dependencies.
The source's global morphism is the supported Kummer class realized through
H^0 and the closed-support adjunction, with its etale origin retained.

Hypothesis and clause correspondence:

- The binder `P : PurityFiniteSetting.{u}` is the recorded finite-field and
  coefficient datum: its `field`, `coefficients`, finite `extension`, `level` and
  `level_pos` fix k, p, ell distinct from p, E, its valuation ring and quotient
  A = O_E/(varpi_E^n), n >= 1. `h : P.ramificationIndex ∣ P.level` is exactly e|n.
  `P.kummerLevel` is n/e, and `P.exponent` is ell^(n/e). The first conjunct states
  N >= 1 and mA=0 explicitly. The small-site coefficient lift is `P.Coefficient`;
  `P.Ring` is the underlying quotient without this lift.
- `Y`, `a : Y ⟶ Spec (.of P.field.k)`, and the three classes `IsSeparated a`,
  `LocallyOfFiniteType a`, `QuasiCompact a` express precisely separated finite type
  over k. No smoothness, regularity, nonemptiness or additional dimension bound
  is assumed.
- `Line Y`, `zeroSection Y`, `Punctured Y`, `openImmersion Y`, and
  `coordinateKummer` are the recorded affine-line datum, not new constructions.
  `twistEtale h (Line Y)` is the actual roots tensor line and `twist h (Line Y)`
  its exact comparison inverse image. Thus the theta and phi coefficient formulas
  and the actual coefficient-extended Kummer class are inherited unchanged from
  `PurityFiniteSetting` and `PurityAffineLineDatum`.
- The existential `(d : ℕ)` bounds `topologicalKrullDim (Line Y)`.
  Its accompanying `hj` proves quasi-compactness of the actual open immersion,
  and `HasOpenComplementCondition ... (2*d)` is the recorded two-part ordinary
  etale condition. Zero is an allowed bound; no positive dimension is required.
- The next conjunct is `IsLeftAdjoint` of the ordinary etale derived closed
  direct image. The underlying `etClosed` construction is already defined for
  every closed immersion independently of an open-complement condition. No
  right adjoint on all pro-etale complexes is asserted.
- For every ordinary etale `M`, the next conjunct preserves the recorded
  `isBoundedConstructible` predicate, and, separately, `finiteTorConstructibleEtale`.
  The finite-Tor hypothesis is explicit in the implication, never inferred from
  bounded constructibility alone. The output is the actual ambient right adjoint.
- The common etale cover `V` trivializes both the etale twist and its pro-etale
  pullback to the constant coefficient unit. These are precisely locally constant
  free rank-one A-sheaves, with finite stalks because A is finite.
- `hasTorAmplitudeIn ... 0 0 (gysinEtaleInput ...).obj` and
  `HasProEtaleTorAmplitude ... 0 0` for the intrinsic realization of `gysinInput`
  give both displayed Tor intervals. The exact comparison/single-complex
  definitions identify the latter with F in degree zero.
- The two `finiteTorConstructible` conjuncts put the actual `derivedSheaf ... false`
  (A_Y[0]) and `gysinValue` (Rs^!F[2]) in the existing full finite-Tor category.
  The following `∀ q ≠ 0, IsZero ...` is concentration of K in degree zero.
- `AffineLineBoundaryRealization` expands the remaining clauses. Its `χ` has
  exactly the natural-isomorphism type of `supported_cohomology_hom`, specialized
  to s and degree two, with the *underived* s_*A_Y in degree zero. This abbreviation
  names the type of the existing identification; it defines no second support
  functor or Hom construction.
- For every recorded retraction comparison `c`, the witnesses `b`, `edge`, `e`
  obey verbatim the three map normalizations in `GysinSupportIdentification`.
  In particular `e.hom` is the cohomological shift, inverse local-class edge, then
  `c.supportIso`. No freely chosen section-to-support identification is allowed.
- For each `α : gysinSupport`, `∃! m, e.hom (gysinHomToSections m) = α` gives
  existence and uniqueness based on the section condition itself.
  `gysinHomToSections` is explicitly H^0(m) evaluated on 1, including the
  canonical identification H^0(A_Y[0]) = A_Y.
- The equality for every `m` is exactly χ(α) = epsilon after s_*m for
  α = e(ev(m)). The leading inverse `mapDerivedCategorySingleFunctor` comparison
  merely identifies the underived s_*A_Y[0] with the exact derived image of A_Y[0].
  Since the preceding clause realizes every α, this is the equation for every
  supported class, rather than only for the coordinate class.
- `boundaryEtaleValue` is the shifted actual ordinary closed-adjoint value of F_e.
  Its bounded-below witness `hb` is a conclusion. `eK.hom` is required to equal
  `boundaryExceptionalComparison`, whose factors are the recorded retraction
  collapse, counit-compatible uniqueness of ordinary right adjoints, comparison
  unit, and shift comparison. `d.hom` is required to equal the actual closed
  direct-image site mate `boundaryImageComparison`.
- The equation `d.hom ≫ s_*(eK.hom) ≫ ε = ν^*(boundaryEtaleCounit) ≫ shiftComparison`
  specifies epsilon as exactly the transported ordinary etale counit. Both d and
  eK are isomorphisms, so this equation uniquely determines epsilon. No arbitrary
  counit or unrestricted pro-etale adjunction enters the interface.
- For every `m`, the unique ordinary etale map `f` with canonical comparison
  image m states the etale origin of all realizing morphisms. Together with the
  preceding counit and image-mate equations, it gives etale models of the
  displayed supported-Hom equation as well.
- The last clause substitutes `(δ 1).app ... (gysinKummerSection ...)`, the support
  boundary of the actual `coordinateKummer`. It uses any exact support-sequence
  boundary, consistently with the inherited Gysin interface, and states unique
  realization with H^0(m)(1) the corresponding section.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its coefficient ring,
  `constantEtale`, `twistEtale`, `constant`, `twist`, `derivedSheaf`.
- `Sheaf.Paper.PurityAffineLineDatum`: `Line`, `zeroSection`, `lineProjection`,
  `Punctured`, `openImmersion`, `coordinateKummer` via `gysinKummerSection`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: the pro-etale
  `derivedSupportSections`, `supportHypercohomology`, `supportRestrictionArrow`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`, and its
  imported `finiteTorConstructible`, `Scheme.HasProEtaleTorAmplitude`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded
  exceptional coefficient framework. The concrete value uses the existing
  `sfFiniteExceptionalFixed` through `RetractedSupport.closedTerm` and `gysinClosed`.
- `Sheaf.AlgebraicGeometry.OpenComplementCondition`: `HasOpenComplementCondition`.
- `Sheaf.Paper.SupportedCohomologyHom`: `supported_cohomology_hom`; its precise
  functor-isomorphism signature is the type of χ, with explicit normalization here.
- `Sheaf.Paper.PurityGysinStructure`: `gysin_structure`, `gysinInput`, `gysinValue`,
  `gysinSupport`, `gysinHomToSections`, `GysinSupportIdentification` and its maps.
- `Sheaf.AlgebraicGeometry.SupportLongExact`: `SupportSequenceBoundary`,
  `SupportSequenceExact`, `exists_support_longExact`, used through the recorded
  Gysin support construction.
- `RetractedSupportLocalizationComparison`: `Comparison`, `etClosed`, `collapse`,
  `firstComparison`, `imageComparison`, `nu`, `nuPlus`, `hyper`, `localClasses`.
  The new helper maps are their explicit composites, not independent replacements.

All recorded proof-dependency modules that exist are imported. The three proof
nodes `lem-pur-zero-support-retraction-triangle`,
`lem-pur-kummer-triangle-concentration`, and
`lem-pur-supported-class-evaluation-comparison` have no Lean record or usable
upstream declaration in the read DAG; they are proof dependencies only, not
missing notions needed to type the statement. Their eventual proof imports can
be added by the maintainer. Their mathematical roles are in the proof docstring.

Edge cases checked before drafting: empty Y gives empty X and allows d=0; all
sections and Hom groups are the zero groups, and uniqueness remains valid.
Y=Spec(k) gives the ordinary coordinate support class. The level n=e gives N=1;
ramified E is retained without replacing n by an ell-power level. Disconnected
and nonreduced finite-type Y are unrestricted. The zero support class realizes
the zero morphism. No ambient pro-etale-adjoint assumption was introduced.
Universe u is explicit everywhere: small-site objects remain in u+1 and
morphisms in u; coefficient modules are in u+1. `autoImplicit false` forbids
unbound variables. No equality of site universes was imposed.

Searches for an existing statement:

- `msearch.py leanfinder`, query "Affine line zero section supported degree two
  cohomology finite Tor exceptional adjoint counit realization": 8 hits, including
  affine-transition-limit statements, a profinite exactness statement, and
  `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`. None is this
  support realization or counit normalization.
- `msearch.py loogle`, query "CategoryTheory.Adjunction.homEquiv, DerivedCategory":
  OK, zero hits.
- `msearch.py grep`, query `supported_cohomology_hom|gysin.*realiz|affine.*boundary`:
  OK, zero Mathlib hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `boundary_realization|affineLineBoundary|lem-pur-affine-line-boundary-realization`:
  no existing realization declaration. The upstream pro-etale search for Gysin
  and supported Hom found compact-support commentary, not this statement.
- Direct source inspection found the existing Gysin and supported-Hom interfaces
  above and reused them. The new declared names were checked against both project
  trees and Mathlib before delivery; there is no duplicate declaration.

Validation: `scompile.py` compiled the complete module in sandbox and library
coordinates within the default 60-second limits, with no error or non-sorry warning.
The required delivery dry run and its per-file compilation are run before pushing.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
