## Worker report

Item: lem-per-rational-scalar-balanced-localization. The statement is unchanged.
The module Sheaf.Paper.RationalScalarBalancedLocalization gives the actual balanced
comparison and states all its normalizations and coherence clauses. The main theorem
is AlgebraicGeometry.Scheme.rationalScalarBalancedLocalization; its unique isomorphism
has components rationalBalancedComponent. Every theorem has proof `by sorry` and a
source/proof docstring. All definitions have real data. No new DAG nodes or dependency
repairs are needed.

The helpers specialize existing constructions; they do not define a second category,
tensor, K-flat predicate, raw rationalization, or completed coefficient sheaf.
In particular rationalBalancedCoefficient is the existing continuousCoefficientMap
applied to the lifted specified embedding. Its continuity is the named helper theorem
rationalBalancedEmbedding_continuous. This is a proof obligation, not chosen data.
The ordinary comparison is Adjunction.leftAdjointCompIso for the existing normalized
pbcScalarAdjunctions. The s and t comparisons are pbcReductionNormalization.

Hypotheses and objects, clause by clause:

- Prime ell: `(l : ℕ) [Fact l.Prime]`. Each finite extension uses `E F : Type u`,
  `Field`, `Algebra ℚ_[l]`, and `FiniteDimensional ℚ_[l]` instances. The inclusion
  is the specified algebra embedding `i : E →ₐ[ℚ_[l]] F`; an inclusion is a special
  case of this coordinate-free presentation. G, H and j, k encode finite towers.
  `Padic.coefficientExtensionIntegers`, `pbcIntegralDatum`, `pbcUniformizer` are
  the existing chosen valuation rings and uniformizers, lifted to Type (u+1).
- Schemes: `(X : Scheme.{u}) [IsNoetherian X]`,
  `[Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]`, and
  `[Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]`. The geometric normalization
  has these same hypotheses on Y and Z. The elementary coefficient square is stated
  for arbitrary schemes, since its definition and proof need no finiteness restriction.
- Small pro-etale site and completed coefficient sheaves: `ProEt.topology X`,
  `pbcAdicCompletion X (pbcIntegralDatum l E)` and `pbcAdicProjection`. Index n
  in these existing definitions means exponent n+1, so exactly all positive levels
  occur. No n=0 quotient is substituted for the first positive level.
- Module sheaves and unbounded derived categories: existing `pbcModules`,
  `DerivedCategory`, `pbcExtend`, `pbcDerivedExtend`, and `pbcComplexCounit`.
  The integral category is `PbcBoundedConstructibleComplete` (all three membership
  conditions including compatible etale origins); its full ambient Hom sets are retained.
- Raw rational categories and Q: `PbcRationalDerivedCategory` and
  `pbcRationalization`; their objects are unchanged integral objects. No Karoubi
  envelope appears. The given J is `sE.J` or `sF.J` for the recorded
  `RationalModuleRealization`. The data `sE` and `sF` are exactly the normalized
  realizations already stipulated by the node, not extra mathematical assumptions.
  Their `objects` and `fractions` fields supply the stated J formulas.
- Integral C and raw T: exactly `pbcEmbeddingAmbientTensor`,
  `pbcEmbeddingIntegralTensor`, and `pbcRationalScalarExtension` of the dependency.
  The `pbcStageTransition` family supplies its literal-identity normalization.

Coefficient-map clauses:

- `rationalBalancedIntegralCoefficients` states the finite-projection normalization
  of the existing pbcScalarCoefficientMap using pbcScalarQuotientMap. Its second
  conjunct is precisely the c_E,g / c_F,g commuting square, with Lean's forward
  composition notation. The c maps are the published `completedCoefficientMap`.
- `rationalBalancedIntegralNormalization` identifies that very integral inclusion,
  through the given integral realization isomorphisms, with pointwise postcomposition.
- `rationalBalancedGeometricNormalization` identifies that very completed geometric
  map with continuous precomposition. `rationalBalancedIntegralGeometricMap` and
  `rationalBalancedGeometricMap` are direct specializations of the existing
  continuousCoefficientPullback at the coefficientExtensionNormedField topology.
- `rationalBalancedCoefficient_sections` states pointwise postcomposition by i,
  preservation of one, and that every nonzero E-constant has the constant i(a⁻¹)
  as reciprocal. Thus the source uniformizer becomes invertible as required.
  This also fixes the localized fraction formula b/t^n ↦ i(b)i(t)^(-n), since
  all these maps are actual unital ring maps and their values on sections are fixed.
- `rationalBalancedCoefficient_square` identifies localization of the normalized
  integral map with that continuous coefficient map. `rationalBalancedGeometricSquare`
  is the localized geometric square. Both maps preserve coefficient units by construction.

Balanced tensors and naturality:

- `rationalBalancedS` is s_K, with source extension through B_F and target extension
  directly from B_E to F_X. `rationalBalancedT` is t_K through E_X to the identical
  target. Their codomains are literally the same single derived extension.
- `rationalBalancedTensorModels` is a reusable specialization interface for these
  same existing scalar-extension functors. Its first conjunct maps the scalar-first
  sheafified tensor t ⊗ (s ⊗ x) to (t*b(s)) ⊗ x. The second sends t ⊗ x back to
  t ⊗ (1 ⊗ x). This is precisely multiplication/insertion of one, with the
  project's scalar-first parenthesization of the paper's tensor factors.
- Its third conjunct states preservation of K-flatness and flat terms. Its fourth
  identifies the canonical derived composition map, via the universal cochain
  computation counits, with that ordinary multiplication map. Apply it to
  B_E→B_F→F_X or B_E→E_X→F_X; the coefficient-square equality transports the
  former composite to the common coefficient map. It works for every such P,
  so does not select or silently restrict representatives.
- `rationalBalancedDerivedNaturality` states naturality for arbitrary derived
  morphisms, not only cochain maps. Together with the universal computation
  formula this gives representative independence for s, t and their inverses.
- `rationalBalancedComponent` composes s with t inverse, with only the recorded
  J object equalities as transports. Its inverse is consequently t followed by
  s inverse with the reverse transports. `rationalBalancedComponent_naturality`
  states naturality on all raw Hom elements, and `rationalBalancedTheta` is the
  actual `NatIso.ofComponents` using this named proof obligation.
- `rationalBalancedFractions` takes exactly
  `t^r • (t^m • f - t^n • h) = 0`, and asserts equality of the f/t^n and h/t^m
  images under BOTH compared functors. Denominators use Away.invSelf, not
  cancellation in an integral Hom group. The existing realization fraction formula
  and raw T formula give integral naturality times the inverse denominator.
  There is no torsion-free, faithful, bounded-representative or quotient-flatness binder.

Coherence clauses:

- `rationalBalancedCoefficient_comp` fixes composed coefficient maps.
  `rationalBalancedTower` is an equation of components of natural transformations
  on every raw rational object, with exactly `pbcRationalScalarComp` and the
  coefficient-side `pbcReductionNormalization`. The flattening formula in
  rationalBalancedTensorModels gives m ⊗ l ⊗ p ↦ ml ⊗ p.
- `rationalBalancedPentagon` compares the two composites of the specified raw
  associators after J and the direct theta. On flat models both flatten to nml ⊗ p.
  Since the component maps are natural on all raw morphisms, these are natural
  transformation equations there, including fraction arrows.
- `rationalBalancedNormalizedTower` gives the equation explicitly for the
  literally normalized `pbcStageTransition` and `pbcStageAssociator`, using only
  the existing pbcStageNormalization conjugations.
- `rationalBalancedIdentity` states identity of the coefficient map and supplies
  the multiplication unitor on ordinary modules and its derived computation on
  every complex. Its raw equation uses exactly pbcRationalScalarUnit.
  `rationalBalancedNormalizedIdentity` states literal equality T_E/E=id and the
  theta equation after that specified normalization, retaining ordinary multiplication
  and the derived computation formula. Equal adjacent fields are included.

Dependency declarations read and used (all in their recorded modules, directly imported):

- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  CochainComplex.IsKFlatIndependentCoefficients.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  SheafOfModules.cochainModulesMonoidal and its additive tensor interface.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory, Q.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing, publicly exposing the coefficient constructions.
- Sheaf.Paper.AdicCoefficientDatum: completedReductionTower, coefficientMap, and
  completedReductionCoefficient; the already published pbc wrappers retain these objects.
- Sheaf.Paper.IntegralUniformCoefficient: pbcBoundedConstructibleComplete and its
  underlying full category PbcBoundedConstructibleComplete, already specialized by J.
- Sheaf.Paper.PbcQbarCompletedPullback: pbcQbarCompletedPull and its public strict
  completed-pullback framework. The coefficient map needed here is the existing
  completedCoefficientMap; no pair-category operation is substituted for it.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and Scheme.ProEt.topology.
- Sheaf.Paper.PbcRationalCategory: PbcRationalDerivedCategory, pbcRationalization.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  underlying the existing pbcModules abbreviation.
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients:
  CochainComplex.exists_isKFlatResolutionIndependentCoefficients (proof dependency
  too; no duplicate resolution predicate or theorem).
- Sheaf.Paper.RationalModuleRealizationFunctor: RationalModuleRealization,
  rationalModuleRealizationFunctor, rationalModuleConstantMap, and their object,
  fraction, integral and finite-projection normalizations.
- Sheaf.Paper.ContinuousCoefficientRealizations: ProEtale.chartComparison_naturality;
  its coefficient postcomposition/precomposition interpretation is used in the plan.
- Sheaf.Paper.PbcScalarExtension: pbcScalarCoefficientMap, pbcScalarQuotientMap,
  pbcEmbeddingIntegralTensor, pbcRationalScalarExtension, pbcRationalScalarComp,
  pbcRationalScalarUnit, pbcStageTransition, pbcStageNormalization, pbcStageAssociator.

The proof imports also include the recorded successive-derived normalization,
ordinary derived change of rings (publicly exposing its general ringed-site model),
semilinear localization, extension-integers DVR, K-flat ringed-topos pullback,
and continuous immersion realization modules. Absolute-value uniqueness is already
available through the finite coefficient constructions. No parent comparison module
is imported: RationalRealizationScalarCoherence is downstream of this item in the
proof plan. Its partial comparison record alone omits the additional clauses here.

Edge cases checked: ramified E→F (same positive quotient exponent is valid because
v_F(i(t_E))≥1); equal fields and consecutive equal fields; zero derived objects;
zero or torsion numerators and integral Hom torsion; r,m,n=0; empty scheme and empty
site objects (unit equations remain valid in the zero section ring); unbounded
flat-term K-flat models; arbitrary scheme maps rather than only immersions; and
all finite positive quotient levels. The small pro-etale object and Hom universes
remain u+1 and u; coefficient/module universes are u+1. No equality between those
site universes or restriction to Type 0 coefficients is introduced.

Searches for an existing complete statement (2026-10-24):

- msearch leanfinder: "Balanced derived scalar extension of finite l adic coefficient
  sheaves commutes with raw rational localization". Eight hits, chiefly BDeRhamPlus,
  BDeRham and ordinary local-cohomology constructions; no matching theorem.
- msearch loogle: "SheafOfModules.pullbackComp". Five hits: pullbackComp and its
  unit/associative variants. These concern ordinary pullback and do not supply the
  completed-coefficient raw fraction and realization normalizations.
- msearch grep: "derived.*scalar.*localiz|balanced.*localiz". No Mathlib hits.
- msearch leansearch: "Derived tensor extension of completed coefficient sheaves
  commutes with rational localization and has coherent balanced comparisons".
  Eight hits in ordinary IsLocalization tensor/base-change material; no matching theorem.
- rg of WeilConjectures and Sheaf by scalar/localization concepts found existing
  PbcScalarExtension, RationalModuleRealizationFunctor, and the downstream
  RationalRealizationScalarCoherence. They are used where lower-level, without
  importing the downstream theorem or restating its bundled comparison definition.
- Exact item-id and rationalBalanced name searches of WeilConjectures, Sheaf and
  dag/lean_names_upstream.json found no existing owner/declaration for this item.

Read the current blueprint proof lem-per-smooth-pullback-t-exact and the local Stacks
0G7E and 0D6D source statements/proofs. This node is the retained finite-coefficient
balanced-localization input on that route, not a change to the blueprint unit.
No statement dispute or source correction was found.

Validation: compiled each version only with scompile.py. The full module compiled
cleanly in both sandbox and library module modes; final delivery validation is
performed by deliver2.py --no-push and then deliver2.py.

## Second reading by Q42

No independent second worker was started: the dispatcher brief requires direct delivery
and prohibits spawning agents. The maintainer's independent review is the review.
The worker re-read the node and complete module against the clause mapping above.
This pass added explicit arbitrary-derived naturality and the literal-identity
normalization equation, retaining the ordinary unitor's section and cochain formulas.
It also checked the two denominator exponents against the annihilating-power relation
and checked that s and t have the identical direct-extension target.
