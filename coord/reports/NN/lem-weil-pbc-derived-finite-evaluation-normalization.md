## Worker report

Existing match; no Lean source is added or modified. The main declaration is
`AlgebraicGeometry.Scheme.completedReductionFiniteEvaluation_exists` in
`Sheaf.Paper.CompletedPullbackReduction` (source line 1128). Its signature is copied
verbatim into `lean.statement`. The other recorded public declarations expose its
normalization predicate, literal universal-counit construction, representative maps,
restriction comparison and selected canonical isomorphism. This is the existing
interface explicitly named by the node's source. All non-`lean` node fields are unchanged.

Sources read: the item's entire nine-step split and its six statement dependencies;
their recorded declarations and the retained integral interfaces; the current blueprint
`main-20261015/.../lemma-weil-pbc-completed-pullback-reduction.proof.md`, paragraph 2;
and `literature/stacks-project/proetale.tex`, lemma-pushforward-Noetherian-case (099N),
including clause (5) and its proof. As the node says, 099N gives context, not the literal
expanded normalization statement. The explicit comparison is already implemented in
`CompletedPullbackReduction.lean`.

Hypothesis and clause correspondence (all names below are in
`AlgebraicGeometry.Scheme`, unless qualified otherwise):

- Arbitrary scheme morphism: the section parameters are
  `{X Y : Scheme.{u}} (g : X ⟶ Y)`, so `Y=T`, `X=T'`. There are no properness,
  Noetherianity, finite-dimensionality or characteristic hypotheses on the schemes.
- Noetherian adic coefficients: `{A : Type (u+1)} [CommRing A]`
  `(d : AdicCoefficientDatum A)`. This extends `CompleteCoefficientDatum A` and
  retains its Noetherian, finitely generated ideal, additive torsion and perfect
  positive quotient hypotheses; `quotientFinite` supplies finiteness of every quotient.
  The small pro-etale site has the existing object/morphism universes; no new universe
  equation or changed site is used. Lean `n : ℕ` denotes exponent `n+1`, including 1.
- `S_{W,n}`, `B_W`, projections and quotient maps are the existing
  `reductionCoefficient W d n`, `pbcAdicCompletion W d`,
  `completedReductionProjection W d n`, `reductionCoefficientMap W d b a hab`.
  The completion is the actual limit of the coefficient sheaves, not a constant ring.
- `G` and its strict-tower form are `completedModulePullback g d` and
  `completedTowerModulePullback g d` in `Sheaf.Paper.CompletedTowerPullback`.
  The latter is actual whiskering on strict functors `ℕᵒᵖ ⥤ pbcModules`, not a
  collection of unrelated derived levels.
- The equality of the projection-defined ring map and the four-corners integral map
  is already `completedCoefficientMap_eq_integralRingIso` (private, in
  `CompletedTowerPullback`, line 152):
  `completedCoefficientMap g d = (d.integralRingIso g).hom`.
  In `FourCorners`, `integralRingIso` is `asIso (d.integralRingMap g)` with its
  specified invertibility proof. Thus this is exactly equality to `integralRingMap`,
  rather than an arbitrary isomorphism of the same rings. The private
  `coefficientMap_isIso` in `CompletedPullbackReduction`, line 234, explicitly has
  type `IsIso (completedCoefficientMap g d)`.
- Exactness is already expressed by `PreservesFiniteLimits` and
  `PreservesFiniteColimits` for each of `completedModulePullback g d` and
  `completedTowerModulePullback g d`. These are the existing private instances
  `completedModulePullback_finiteLimits`, `completedModulePullback_finiteColimits`,
  `completedTowerModulePullback_finiteLimits`, and
  `completedTowerModulePullback_finiteColimits` in `CompletedTowerPullback`, lines
  177-196. The private theorems
  `completedReductionPullback_preservesFiniteLimits`,
  `completedReductionPullback_preservesFiniteColimits`,
  `completedReductionTowerPullback_preservesFiniteLimits`, and
  `completedReductionTowerPullback_preservesFiniteColimits` in
  `CompletedPullbackReduction`, lines 900-925, state these same four exactness facts.
  For additive functors between these abelian categories these are exactness.
- The functors `R_T`, `V_g` and `U_n` are `completedReductionTower Y d`,
  `completedTowerPullback g d`, and their composite with
  `pbcTowerEvaluation X (pbcAdicCompletion X d) n`. `H_n` is exactly
  `completedReductionFiniteTarget g d n`: derived scalar extension followed by the
  finite coefficient pullback `completedReductionFiniteDerived g d n`.
- `Q` is `DerivedCategory.Q`. The actual counits are
  `completedReductionTowerCounit d Y` and `completedTowerPullbackCounit g d`;
  their complex components use `Functor.leftDerivedCounitOnComplex`.
- The literal composite `u_{n,P}` is `completedReductionPulledModelMap g d n P`.
  Its definition applies `completedReductionCompositeCounitNat` to the ordinary
  strict reduction functor, strict-tower module pullback, exact evaluation, their
  two derived functors, and those two specified counits, then takes `.app P`.
  The generic natural transformation's `app` field is exactly evaluation of
  `LG.map (leftDerivedCounitOnComplex F LF εF P)` followed by the second counit,
  and finally `H.mapDerivedCategoryFactors.hom.app ...`. Thus neither counit is
  replaced by a freely chosen comparison. The existing private specialization
  `completedReductionPulledModelNat` (line 964) is the natural transformation on
  complexes with precisely these components. The generic naturality field already
  proves the required naturality; no additional naturality hypothesis is assumed.
- The literal `v_{n,P}` is `completedReductionFiniteModelMap g d n P` (line 756):
  `(completedReductionFiniteDerived g d n).map
    (pbcComplexCounit (completedReductionProjection Y d n) P)` followed by
  `(completedReductionFiniteModules g d n).mapDerivedCategoryFactors.hom.app ...`.
  This is exactly the finite scalar-extension counit and exact pullback localization.
  Its existing natural transformation is the private `completedReductionFiniteModelNat`.
- Invertibility of `u` on ALL K-flat complexes is the existing private theorem
  `completedReductionPulledModelNat_isIso` (line 1028), whose only complex hypothesis
  is `CochainComplex.IsKFlatIndependentCoefficients
    (R := pbcAdicCompletion Y d) P`. Its conclusion is `IsIso` of the natural
  transformation's component, definitionally the specified `u`.
  Invertibility of `v` is the existing private
  `completedReductionFiniteModelMap_isIso` (line 891), with the identical K-flat
  hypothesis and conclusion `IsIso (completedReductionFiniteModelMap g d n P)`.
  Neither statement assumes boundedness or flat terms. These supporting facts are
  already proved in the source; no new stage-2 proofs are supplied. They are private,
  so their short names are source references here, not falsely listed as public
  declarations in `lean.declarations`.
- The exact restriction localization `delta` is the public
  `completedReductionRestrictionFactors X (completedReductionProjection X d n)`.
  Its type is `DerivedCategory.Q ⋙ pbcDerivedRestrict φ ≅
    (pbcRestrict φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q`.
- `E_n` is the recorded `completedReductionOrdinaryComparison g d n`.
  It is the unique generator-normalized witness from the dependency's
  `completedReductionOrdinaryComparison_exists`. This retains its exact local
  section normalization, not merely some ordinary natural isomorphism.
- Existence AND uniqueness of `e_n` are the literal `∃! e : ... ≅ ...` in
  `completedReductionFiniteEvaluation_exists`. Its source is `R_T ⋙ V_g ⋙ ev_n`;
  its target is `completedReductionFiniteTarget g d n ⋙
    pbcDerivedRestrict (completedReductionProjection X d n)`. In particular it
  retains restriction from the finite target ring to the completed target ring.
- The predicate `HasCompletedReductionFiniteEvaluationNormalization g d n e`
  quantifies over every complex `P` and then ONLY its K-flatness. It asserts
  `completedReductionPulledModelMap ... ≫ Q.map(E_n(P)) =
    e.hom.app (Q.obj P) ≫ Res.map(completedReductionFiniteModelMap ...) ≫ delta.hom.app ...`.
  Lean's `≫` is left-to-right composition, so this is exactly the paper's
  `Q(E_n(P)) u = delta Res(v) e(QP)`. The ordinary isomorphism is explicitly
  applied termwise using `NatTrans.mapHomologicalComplex ... (.up ℤ)`.
- The named canonical comparison is `completedReductionFiniteEvaluation g d n`,
  defined as `(completedReductionFiniteEvaluation_exists g d n).exists.choose`.
  Its chosen specification is the displayed normalization. Uniqueness prevents
  replacing it by an arbitrary automorphism of the target.
- The source and target of this natural isomorphism are the FULL derived categories.
  There is no `IsDerivedCompleteIntrinsic`, boundedness or flat-term binder on the
  input. The quantified K-flat predicate is the independently sized sheaf-tensor
  notion from the dependency, not a pointwise-flat substitute.

Dependency declarations read and reused:

- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`,
  `completedReductionModuleTowerFunctor`, `completedReductionTower_properties`,
  finite coefficient sheaves, projections, quotient maps, and scalar-extension pair.
- `Sheaf.Paper.PbcQbarCompletedPullback`: the recorded `pbcQbarCompletedPull` was
  read. Its record explicitly retains the general integral strict-tower interface
  by public import. This item uses that integral interface in
  `Sheaf.Paper.CompletedTowerPullback`, namely the module/tower pullbacks, their
  universal derived pairs and counits. No Qbar, constructibility, field or scheme
  finiteness hypotheses from the separate rational restriction are imported into
  this statement.
- `Sheaf.Paper.CompletedPullbackReduction`: the finite-interfaces record's
  `completedReductionFiniteTarget`, finite module pullback and fixed model maps;
  and the ordinary comparison dependency's `completedReductionOrdinaryComparison_exists`
  and selected `completedReductionOrdinaryComparison`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, the total-tensor acyclicity
  predicate used in the representative normalization, at site universes `u+1,u`
  and coefficient universe `u+1`.
- `Sheaf.Paper.FourCorners`: `AdicCoefficientDatum.fourCorners` and the actual
  coefficient comparisons `AdicCoefficientDatum.integralRingMap`,
  `integralRingMap_isIso`, `integralRingIso`, and `projection_comm`.

Edge cases checked: `n=0` is exponent 1, never exponent 0. Zero quotient rings,
zero modules and zero complexes are allowed by `AdicCoefficientDatum` and these
module categories. Both schemes may be empty; there is no nonemptiness condition.
The morphism may be an identity or arbitrary. K-flat complexes may be unbounded
and need not have flat terms. The derived input may fail completeness; the
comparison precedes `Rlim` and never uses a completeness condition. Completed
and finite coefficient module categories stay distinct via explicit restriction.
The universal-pair choices are tied to their counits; the comparison choice is
from unique existence with the specified representative equation.

Searches made before recording the match:

- `msearch.py ... leanfinder`: "Derived finite evaluation of a strict reduction
  tower commutes with pullback, uniquely normalized by universal derived counits
  on unbounded K-flat complexes". Eight generic results, including
  `Functor.mapDerivedCategoryFactorsh`, `Functor.mapDerivedCategoryFactors`,
  `Functor.mapDerivedCategoryFactorsh_hom_app`, and
  `Functor.mapDerivedCategorySingleFunctor`; none is this scheme-specific comparison.
- `msearch.py ... loogle`: `CategoryTheory.Functor.mapDerivedCategoryFactors,
  CategoryTheory.Functor.leftDerivedNatIso`; zero hits.
- `msearch.py ... leansearch`: "derived finite evaluation pullback reduction tower
  natural isomorphism determined on K flat complexes". Eight generic results,
  including `Functor.leftDerivedNatIso`, `Functor.rightDerivedNatIso`,
  `CategoryTheory.compEvaluation`; no exact scheme-specific result.
- `msearch.py ... grep`: `completedReductionFiniteEvaluation|
  completedReductionCompositeCounitNat|leftDerivedNatIso`. Two Mathlib hits,
  both in `Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean`, for the generic
  `leftDerivedNatIso` construction.
- `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `completedReductionFiniteEvaluation|completedReductionCompositeCounitNat|
  HasCompletedReductionFiniteEvaluationNormalization`: the exact public theorem
  and definitions occur in `Sheaf/Paper/CompletedPullbackReduction.lean`;
  consumers reuse them. No upstream declaration with these names.
- `grep -rn` for the item id on `lean/WeilConjectures`: no hits.
  `rg` on `dag/lean_names_upstream.json` for the comparison and supporting names:
  no hits. `scompile.py --source Sheaf.Paper.CompletedPullbackReduction` confirmed
  the live server source has the same comparison, normalization and helper results.

No statement correction, disputed statement, missing notion, dependency repair or
new node. The supporting private declarations are identified explicitly above so
that the review does not mistake the central theorem for a bare unnormalized
isomorphism or overlook its already-established auxiliary clauses.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
