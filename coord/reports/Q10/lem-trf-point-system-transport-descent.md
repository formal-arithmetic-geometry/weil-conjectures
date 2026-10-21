## Worker report

The delivery states `lem-trf-point-system-transport-descent` in
`Sheaf.Paper.PointSystemTransportDescent`. Nothing is proved. Every postponed
proof is a named theorem carrying this node's blueprint tag and a proof docstring.
All definitions have real data. The choices of coefficient map, chain transport,
descended transport, finite sigma and evaluation comparisons come from uniqueness
statements with complete sectionwise or localization normalization; none chooses
an arbitrary functor, comparison or fiber identification.

Source read: current main-20261015 blueprint,
`sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`,
paragraph (3), together with all seven proof steps of the extracted node. This is
the agent-formulated prerequisite, not the blueprint unit's own statement. No
mathematical statement correction or disputed statement is needed. The returned
delivery is repaired by the definition ownership node described below.

Hypotheses and clauses, in namespace `WeilConjectures.PointSystemTransport`:

- The finite field and algebraic closure are `D : FiniteFieldDatum.{t}`. The
  coefficient prime is `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p` occurs in
  chainTransport and point_system_transport_descent. The finite extension is
  `E : Type u` with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  Its valuation ring and positive-power quotient are exactly the recorded
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionRing`.
  The quotient ideals are canonical and do not choose another uniformizer.
- The point is `Spec (.of D.k)`. `pointPower D r` recursively composes the recorded
  `frobeniusPointIso D`; this is Spec(gamma)^r. `r : ℕ` and `hr : 1 ≤ r` are
  explicit in the two principal existence/descent statements.
- The site remains `Scheme.ProEt`, of object universe t+1 and morphism universe t.
  Coefficients and modules use `max u (t+1)`. No equality of t and u is imposed.
  ULift of R is the canonical universe transport, not another coefficient ring.
- B_n, its quotient maps, and the completed ring are the existing integral
  coefficient sheaves, `integralCoefficientSheafTransition`, and
  `completedIntegralCoefficientSheafUnrestricted`. Natural indices start at 0
  and mean the exponent n+1, so no positive level is omitted.
- Strict quotient-linear systems are `coefficientSequenceModules`, and their
  ordinary unbounded localization is `coefficientSequenceDerived`. These are
  the existing module category on the vertical sequence site. This is the
  specialization of the system model in SemilinearDerivedSections; it has
  arbitrary original horizontal restrictions, including zero transitions.
- `reindex` is id on the sequence index and postcomposition by h^r on the site.
  `coefficient_existsUnique` prescribes its coefficient map to be c_n inverse
  at every (n,U). `pull` uses Mathlib `SheafOfModules.pushforward` with exactly
  that map, hence its value and both vertical and horizontal arrows are the
  actual reindexing of M, with the transported action. It is the G_r in the node.
- `sections` is the recorded `coefficientSequenceRestriction` followed by
  levelwise `pointRestrictionSections ... none`. Thus it is restriction through
  the completion and exact sections, retaining the whole strict tower, not a
  limit or a tower of derived categories. `pull_exact` and `sections_exact`
  assert additivity and preservation of finite limits and finite colimits.
- `HasRestrictionComponents` identifies every degree/level underlying function
  with the actual restriction along `(id_n, pointRestrictionArrow h^r)` in the
  original system presheaf. HEq only transports unchanged section carriers
  through scalar restriction. By the recorded inverse-image coordinates this
  is restriction, colimit insertion and sheafification, with the latter two
  identified with identity at the distinguished index.
- `chainTransport_existsUnique` asserts a unique natural transformation between
  the complex functors with those components. A component is a chain map in
  the category of strict R-module towers, so it is R-linear, commutes with all
  differentials and original transitions. Its NatTrans type supplies the stated
  chain-map naturality for every f; the sectionwise prescription also uniquely
  determines each individual component map.
- `finiteSigma_existsUnique` states A_n-linearity before restriction of scalars,
  with its value exactly `pointRestrictionRaw ... (some n)`. `finiteSigmaR`
  applies the actual quotient restriction functor, using `quotient` = RingHom.ulift
  of the canonical quotient homomorphism R→A_n.
- The finite comparison is the dependency's
  `inverseImageFiniteComparisonComplex`, not a replacement. `finiteComparison_isIso`
  asserts invertibility on arbitrary unbounded complexes.
  `finiteComparison_inverse` gives the inverse on a times j(x), i.e. x tensor a,
  as c_n inverse(a)x, for every degree, site object and local section.
- `coefficient_squares` states c_(n+1) followed by rho_n equals F(rho_n)
  followed by c_n, and c_completed followed by pi_n equals F(pi_n) followed by
  c_n. These are equalities of actual sheaf ring maps.
- `insertion` is exactly the adjunction-unit generator followed by restriction
  along the canonical comma arrow, the existing j recipe x→x tensor 1.
  `tensorTransition_existsUnique` states the transition on every x tensor a
  using the original system-presheaf horizontal restriction and rho_n(a).
  This is the recorded `coefficientSequenceTransition` on its actual section
  carriers, by that dependency's defining characterization. At a=1 it
  is exactly v_n(x) tensor rho_n(1)=v_n(x) tensor 1. The maps land in the
  same completed-module category after recorded scalar restriction; their
  NatTrans type asserts naturality in the entire strict system.
- `point_system_transport_descent` explicitly asserts that both complex
  functors preserve every quasi-isomorphism, then asserts unique descent I
  with the specified localization representative equation. Its type is a
  natural transformation between functors from the ordinary derived SYSTEM
  category to `DerivedCategory (ℕᵒᵖ ⥤ ModuleCat R)`. The last conjunct states
  naturality for EVERY derived system morphism, including inverses of
  quasi-isomorphisms. No faithfulness of derived evaluations is assumed.
- `evaluation_existsUnique` fixes the source and target level comparisons to
  identity on their actual section carriers. `sourceEvaluation` and
  `targetEvaluation` are their exact-functor derived images with the standard
  composition comparisons. `finite_evaluation` identifies evaluation of I,
  followed by the actual finite j, with the finite restriction/insertion/
  sheafification/tensor-unit recipe. The formulas `finiteTransportComplex`
  and `finiteTransportDerived` specialize the existing point-transport recipe
  to h^r and retain independent coefficient/site universes. They introduce
  no arbitrary map. On bounded constructible C_n this is precisely iota^(r)
  of def-weil-frobenius-point-transport; the explicit representative recipe
  is meaningful even on the ambient unbounded categories.
  `mapFiniteComplexComparison` uses Mathlib’s canonical composition isomorphisms
  to apply sections to j; it adds no comparison choice or hypothesis.
- No binder assumes cartesianness, boundedness, constructibility at other
  levels, finite Tor-amplitude, derived completeness, or any chosen map I.

Dependency declarations read and used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, for the coefficient
  convention. We do not require its extraneous X_0 when working only on s.
- `Sheaf.SixFunctors.SchemeFrobenius`: finite-field Frobenius conventions;
  the point map itself is `frobeniusPointIso` from the point-transport definition.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its underlying completed and
  finite sheaves/projections, used through pointRestrictionSections.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearSections.Systems`,
  `SemilinearSections.DS`, `semilinearDerivedSections`; the actual specialized
  sequence category is the already recorded `coefficientSequenceModules`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, with the canonical U and
  limit context retained; no property of Rlim is added to this point lemma.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseModuleInverseImage`, and its
  exactness theorem, together with `proEtaleIsoPostcompose`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived` and its public base:
  `inverseImageFiniteCoefficientMap`, `inverseImageCompletedCoefficientMap`,
  `inverseImageFiniteModules`, `inverseImageFiniteComparisonComplex`, and
  `inverseImagePullbackComparisonDerived`'s actual comparison conventions.
- `Sheaf.Paper.CoefTowerCoaugmentation`: ordinary whole-tower convention and
  `CoefTower.adjunction`. No limit is substituted for the whole-tower target.
- `Sheaf.Paper.PointProEtaleSectionsExact`:
  `point_proEtale_sections_exact`, for exact point sections.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`,
  `frobeniusPointFiniteSigma`, `frobeniusPointTransportFiniteComplex`,
  `frobeniusPointTransportFinite`, and their explicit representative recipe.
  The node's recorded primary name is the Qbar endpoint of this same module;
  the finite construction is read from its public declarations.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: DerivedCategory and Q.
- Added existing statement dependency `def-coef-ringed-sequence-site`:
  `Sheaf.Paper.CoefficientRingedSequenceSite` supplies
  `coefficientSequenceModules`, `coefficientSequenceEvaluation`,
  `coefficientSequenceTransition`, `coefficientSequenceRestriction`, and
  `coefficientSequenceDerivedEvaluation`; no copy of the strict-system notion.
- Added definition statement dependency
  `def-trf-point-restriction-coordinates` (the naturality theorem remains only a proof dependency):
  `Sheaf.Paper.PointAutomorphismRestrictionNatural` supplies
  `pointRestrictionScalars`, `pointRestrictionRing`, `pointRestrictionSections`,
  `pointRestrictionRaw`, `pointRestrictionArrow`, and the natural restriction theorem.
  Its plain definitions are public because the signatures use these canonical coordinates;
  the theorem is not used to choose these data.
- Proof imports: `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
  for the sheafified tensor generator calculations; Mathlib
  `DerivedCategory.ExactFunctor` (`Functor.mapDerivedCategoryFactors`) and
  `Localization.Predicate` (`Localization.liftNatTrans`, `natTrans_ext`).

Edge cases checked before writing: r=1 gives the recorded geometric point
Frobenius, with no inverse/sign reversal; n=0 means A_1 rather than the zero
quotient; zero systems and zero transitions retain zero restrictions; unbounded
complexes have all integer degrees quantified; noncartesian systems still use
honest horizontal maps; no flatness of R→A_n is assumed; t and u may differ in
either direction; the target retains all transitions before derived localization.

Searches performed with the prescribed msearch wrapper:

- leanfinder: “Restriction along a point automorphism gives a natural chain map
  on strict quotient linear coefficient systems and descends to derived whole
  module towers”. Eight results: module-presentation scalar restriction,
  HomologicalComplex.restrictionMap_f', restrictionMap_comp, scalar-restriction
  equivalence formulas and AdicCompletion.transitionMap. None is the whole-system
  point-transport assertion.
- loogle: “CategoryTheory.Localization.liftNatTrans,
  SheafOfModules.pushforwardNatTrans”. Zero results for the joint query.
  Both individual APIs were read directly in Mathlib source.
- grep: “point.?[Ss]ystem|transport.*[Dd]escent|natTransΓRes”. Two results, both
  `Mathlib/CategoryTheory/Sites/GlobalSections.lean`, describing natTransΓRes.
  These are ordinary section restrictions, not semilinear systems/descent.
- rg on lean/WeilConjectures and lean/Sheaf for the item id,
  pointSystemTransport and point_system_transport: no existing declaration.
  Further source searches identified and reused the sequence-site, pointwise
  restriction and tensor-comparison declarations described above.

## Second reading by Q10

A separate second pass by the sole dispatcher worker compared the original node
and the final file. No additional agent was started, as the task explicitly
prohibits delegation. Checked the finite-field/prime/extension binders, positive
r and coefficient indexing, independent universes, actual strict source and
whole-tower derived target, canonical coefficient actions, restriction normalization,
A_n-linearity, inverse j formula, tensor transition on x tensor a, completed square,
complex and derived naturality, and finite representative identity. The construction
never derives equality from conservativity of evaluated morphisms.

This pass added the explicit inverse formula, coefficient-square and tensor-generator
clauses and the finite-evaluation equation so that the delivery states every clause
of the node, beyond merely existence of a natural derived arrow. Elaboration repairs
use explicit types and the existing coefficient-sized sheafification conventions;
none changes the mathematical hypotheses. In particular the local irreducibility
attributes on constantSheaf and HasDerivedCategory.standard match the recorded
IntegralOperationsWellDefined module and prevent expansion of those large canonical
constructions during type inference. Every data choice is accompanied by its
uniqueness characterization. The additional stmt_deps name canonical interfaces already used in the statement;
no dependency's record was overwritten. The ownership repair below supersedes the
original theorem citation among those additions.

## Validation

The prescribed scompile.py checked the final module in both its sandbox and its
library namespace against the live published build: clean, 45.8 s and 35.6 s,
respectively, within the unchanged 60 s per-file limit. The delivered file contains
no diagnostic checks, trace options or heartbeat changes. Every variable and
universe is explicitly bound (`autoImplicit false`).

## New nodes

`def-trf-point-restriction-coordinates` owns existing plain definitions in
`Sheaf.Paper.PointAutomorphismRestrictionNatural`: the finite/completed scalar and
coefficient sheaves, their constant scalars and canonical coefficient map, sections
with scalar restriction, sectionwise inverse image, the site arrow and its raw
restriction, plus the additive sections and standard derived-category instances.
The primary declaration is `AlgebraicGeometry.ProEtale.pointRestrictionSections`;
`lean.declarations` lists all eleven coordinate declarations. The node adds no Lean
module, no theorem and no chosen data. Its sources are blueprint proof (3), its
point-factor prerequisite, and the Stacks constructions cited by the existing
module. The eight LeanSearch results were general scalar restriction/sections
ingredients, the Loogle joint query and Mathlib grep both returned zero hits, and
the project grep located this exact existing package. DAG grep found it only
listed under the naturality theorem; neither blueprint search found a definition
owner. The actual queries and results are recorded in the new node.

The new node's hypotheses match the definitions: arbitrary prime and finite
coefficient extension; arbitrary scheme for the sheaves and automorphism
coordinates; any field for sections; none means completion and some n means
exponent n+1; coefficient/site universes are independent. Its raw map is additive
only, with no linearity or naturality assertion smuggled into this definition node.
The naturality theorem supplies those assertions in the consumer's proof.
Identity automorphisms, n=0, arbitrary fields, and unequal universes all remain
allowed. The scalar-ring derived instance uses the standard localization.

## Repair of immutable head 7023c01703ec

H2/theorem-stmt_dep: replaced `lem-weil-point-automorphism-restriction-natural`
in the item's added statement dependencies by
`def-trf-point-restriction-coordinates`, an existing:true definition ownership
record. Kept the theorem in `proof_deps` unchanged. The source module's definitions
do not choose anything from its theorem. The saved packet and current shared
base differ only in the originally permitted `lean` and added `stmt_deps` fields;
the delivery wrapper rebases the repaired packet against the live server.

Also addressed the advisory by citing all three existing definition owners:
`def-pur-integral-finite-pullback` supplies `integralOperationsLevelPullback` and
`integralOperationsPullbackGenerator` from `Sheaf.Paper.IntegralOperationsWellDefined`;
`def-coef-normalized-dvr-tower` supplies `normalizedDVRDerived` from
`Sheaf.Paper.NormalizedDVRTower`; and
`def-sf-scalar-reduction-categories-restriction` supplies `scalarReductionSource`
and `scalarReductionRestriction` from
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`. Their recorded
definitions and signatures were read; no dependency record is changed.

Second reading of the repair by Q10: compared the new node with all eleven
existing coordinate declarations at lines 56-162, including the transitive
Ring/ScalarAt/CoefficientMap definitions. The self-contained statement gives the
actual site arrow, inverse coefficient action, constant/completed scalar maps and
section functor, with no assertion of the naturality theorem. Checked the
consumer uses the recorded coordinates rather than a theorem choice. The
mathematical statement and the complete Lean module are unchanged from the
returned immutable head; the maintainer's clause-by-clause mathematical check
therefore continues to apply. The return explicitly permits the Lean file to stay
unchanged; the redundant imports and standard derived instance are retained.

The initial saved-packet dry run passed and compiled the unchanged module
(commit f1b25ea796e). A fresh dry run validates the repaired ownership records.

The repaired-packet dry run identified that the live blueprint ancestry also
includes `lem-trf-rational-global-frobenius-powers`, absent from the local read
clone. Updated only the new node's `blueprint.from.via` to the live ancestry
printed by preflight; no existing-node metadata or mathematical content changed.
