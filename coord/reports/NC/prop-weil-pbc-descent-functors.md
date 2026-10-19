## Worker report

Repair of immutable returned head `4e84050ba384ca86fc7557eb87fa78916acb646e`,
addressing its H3 finding. I read the independent `review.md`, including its
counterexample by stage-dependent signs and the required canonical-beta repair.
The node and blueprint statement remain unchanged. Only the item's `lean`
record, its module, and this report are delivered. No other DAG node is stated.
This report supersedes earlier reports and second readings of the rejected file;
a fresh second reader must review this replacement.

Source: blueprint `main-20261015`, proper-base-change proposition
`prop-weil-pbc-descent-functors`, order 1372, and its separate `.proof.md`.
The older order-1312 source and the current node's `blueprint_update` agree with
that statement. The explicit last proof sentence requires the scalar-extension
comparisons as the actual beta data, rather than arbitrary coherent comparisons.

### H3 repair: all four canonical beta families

The rejected file identified only the four stage functors and the exchange.
`pbcDescentOperations` now additionally concludes, in order:

* `PbcDirectImageBetaSpec l Ω f presRf Rf.base`;
* `PbcDirectImageBetaSpec l Ω f' presRf' Rf'.base`;
* `PbcPullbackBetaSpec l Ω g presLg Lg.base`;
* `PbcPullbackBetaSpec l Ω g' presLg' Lg'.base`.

These are explicit predicates in this owning module, not new independent notions
or statements of other DAG nodes. Both definitions have fully written bodies,
source/blueprint docstrings, and entries in `lean.declarations`.

Write `c_Z` for the already recorded `pbcScalarIntegralComparison` at a given
coefficient inclusion E≤F and `Q_F` for integral localization. For direct image,
the first predicate requires, at every integral K,

    c_Y(Rf_E K)^(-1) ≫ beta_K ≫ Rf_F(c_X(K))

heterogeneously equal to the component of the UNIQUE rational comparison in
`pbcScalarDirectImage_rational`, specialized to `pbcFiniteField.{u} l Ω E`,
`pbcFiniteField.{u} l Ω F` and `pbcFiniteFieldInclusion l Ω hEF`.
That unique comparison is characterized in the dependency by
`Q_F.map (ObjectProperty.homMk (pbcScalarDirectImageIso ...).hom.app K.obj)`.
Thus the predicate specifies the actual projection mate after rationalization.

For pullback the second predicate instead requires

    Lg_F(c_Y(K)^(-1)) ≫ beta_K^(-1) ≫ c_X(Lg_E K)

to be heterogeneously equal to the unique comparison component specified by
`pbcScalarCompletedPull_rational` at the same small fields. This uses beta
INVERSE because the dependency's completed pullback comparison has the opposite
orientation to `StageSystem.Morphism.β`.

In both definitions `eqToIso eE` and `eqToIso eF` identify the stage functors
with their actual operations before comparing beta. The predicates quantify
over these equality proofs; their existence is already concluded by the four
stagewise functor equalities in the same conjunction. There is no added
hypothesis and no vacuous implication. Proof irrelevance ensures these proof
arguments cannot select a different beta comparison.

`HEq` handles the two previously constructed presentations of the canonical
scalar tensor endpoints. The small-model `pbcCompletedScalarMap` and the
specialized `pbcScalarCoefficientMap` are fixed by the same finite quotient
inclusions, so their uniqueness identifies them and hence their derived
extensions. Their integral restrictions have the same ambient objects;
full-subcategory membership proofs are proof-irrelevant. The existing `c_Z`
conjugations implement the literal-identity normalization, including E=F.
No equality of coefficient universe w and scheme universe u is imposed.

Each rational object is `ScalarLocalization.mk K` for an integral K; the
formula therefore specifies every component. Since c and the operation maps
of c are invertible, it fixes beta itself and excludes the sign twists of the
returned review. The right-hand comparisons use `.exists.choose` from the
recorded EXISTS-UNIQUE theorems whose component formulas determine them fully;
there is no choice from a mere existence statement and no new unproved data.

The existing actual-operation and actual-exchange component formulas are
retained. The two operation definitions are now reducible, allowing these
component composites to elaborate against their actual object maps. Neither
the data nor the signatures of those operations changed.

### Hypotheses and clauses, matched to Lean

* Prime and coefficient closure: `(l : ℕ) [Fact l.Prime]`, `(Ω : Type w)` with
  `[Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`.
* Schemes T and S: `Scheme.{u}`, `IsNoetherian`, finite-dimensional `Fact (∃ n,
  topologicalKrullDim _ ≤ (n : WithBot ℕ∞))`, and stalk-unit
  `Fact (∀ t, IsUnit (l : _.presheaf.stalk t))`. These are the coefficient
  categories' standing hypotheses, also supplied for X, Y, X', Y'.
* Exact finite-stage family: `CoherentExactMorphism.base.Φ`, `additive`,
  `commShift`, and `triangulated` on the actual `pbcScalarSystem`s.
* Scalar comparisons: `base.β`; associator coherence: `base.coh`; shift
  equation: `betaCommShift` with the supplied stage and transition shifts.
  In these normalized systems, coherence at repeated stages makes the unit
  component an idempotent isomorphism, hence the identity. A separate unit
  field is unnecessary, as the independent returned review also verified.
* Induced exact functor: the existing `F.base.functor`. `ExactDescent` explicitly
  concludes additivity and existence of a `CommShift ℤ` structure making that
  same functor `IsTriangulated`; exactness is not an assumption.
* Every representative: `DescentSpec` quantifies K, L, common stage M, hK, hL
  and u. Its map is `mkHom M hK hL` of
  `β.hom.app K.obj ≫ Φ_M.map u ≫ β.inv.app L.obj`, exactly the displayed formula.
* Qbar coefficient categories: `pbcQbarCategory` is the recorded abbreviation
  for `PbcFiniteStagePairCategory`, with its existing common-stage shifts and
  triangles. No envelope or alternative category is used.
* Compatible transformations: `Morphism.Hom` with its `comm` equation and
  `descNatTrans`; the component equals `(targetSystem.ι K.stage).map
  ((τ.τ K.stage).app K.obj)`.
* All compatible equations: arbitrary τ and τ' with equal components at every
  stage object have equal descended transformations. Identities and vertical
  composition also appear explicitly. Compatible whiskering/horizontal
  compositions and their equations are included in this universal clause.
* Application: `ChosenCartesianSquare g' f' f g`, and four preservation
  hypotheses `presRf`, `presRf'`, `presLg`, `presLg'`. These are precisely the
  conditions in the scalar-extension dependency's conditional restriction
  clause, not an assertion of constructibility preservation for arbitrary f.
* Actual operation stage functors: four equalities `base.Φ E =` the specified
  `pbcDescentDirectImage` or `pbcDescentPullback`. Those definitions restrict
  `pbcActualDerivedPush` or `pbcActualCompletedPull` by the supplied preservation
  proof, then apply `pbcConditionalRational` to their actual object/arrow maps.
* Canonical comparison families: the FOUR new BetaSpec conclusions above,
  quantifying every coefficient inclusion and every stage object.
* Exact operation descents: `ExactDescent` is concluded for each of the four
  now fully specified families.
* Exchange: the compatible family Ex has components heterogeneously equal to
  localization of the specified `pbcActualCompletedExchange` component. ExQ is
  its `descNatTrans`, conjugated by the two `functorCompIso` comparisons; its
  component formula is explicitly the stage inclusion of Ex's component.

### Dependencies read and reused

The two statement-dependency records and their full source signatures/docstrings
were read. `Sheaf.Paper.PbcScalarExtension` supplies
`AlgebraicGeometry.Scheme.pbcCoherentScalarExtension` and its recorded companion
rational-operation comparisons `pbcScalarDirectImage_rational` and
`pbcScalarCompletedPull_rational`, with the actual `pbcScalarDirectImageIso` and
`pbcScalarCompletedPullIso` component specifications. It also supplies the
conditional integral/rational operations, ambient operation additivity/linearity,
canonical shifts and coherence, completion units, and scalar exchange equation.
Current server source was read with `scompile.py --source`.

`Sheaf.Paper.PbcQbarCategory` supplies
`AlgebraicGeometry.Scheme.pbcQbarCategory` and its category structures.
`Sheaf.Paper.FiniteStagePairCategory` supplies `pbcScalarSystem`,
`pbcScalarIntegralComparison`, `pbcIntegralScalarExtension`, stage localization,
normalized units, and their unique specifications. Its small fields and completed
coefficient maps come from `Sheaf.Paper.PbcFiniteCompletedCoefficientMap`:
`pbcFiniteField`, `pbcFiniteFieldInclusion`, `pbcStageDatum`,
`pbcCompletedScalarMap`, and `pbcAmbientScalarExtension`.

The existing `WeilConjectures.CategoryTheory.StageSystem.Functor` supplies
`Morphism`, `mapAt`, `functor`, `functor_map_mkHom`, `Hom.comm`, `descNatTrans`,
`Hom.id`, `Hom.comp`, and `functorCompIso`. The recorded proof-dependency modules
PbcRationalTransport, FiniteStagePairCategory, CommonStageCalculus and
PbcCommonStageCones remain imported. The specified exchange is the existing
`pbcActualCompletedExchange` from PbcActualRingedExchange. No dependency record
was replaced or other DAG statement restated.

### Edge cases and integrity

The new beta quantifiers have no E≠F condition: equal fields, repeated stages,
identity transitions and their normalized tensor units are covered. Both inverse
and forward c components are retained. Every integral object, including zero,
is tested. All rational objects come from such objects. The schemes may be
empty, dimension zero is allowed, and identity scheme morphisms are included.
Arbitrary common enlargements and zero transformations are still quantified.
The finite-stage index contains the base field; an empty index is not a case
of the concrete categories. Every prime is allowed subject to the stated
stalk-unit hypotheses. The universe variables w and u remain independent.

Exactly two postponed theorem proofs remain: `pbcDescentFunctors` and
`pbcDescentOperations`, each exactly `sorry` and with a complete proof plan in
its docstring. All seven definitions/structures have real bodies. The beta
predicates merely package this node's missing component clauses; no new theorem,
axiom, independent definition node, or dependency module is introduced. All nine
declarations are listed in `lean.declarations`; `autoImplicit` remains false.
There is no statement dispute or source correction.

### Searches

Prescribed searches were repeated in this repair using msearch.py:

* LeanFinder: "coherent exact functors on finite coefficient pair categories
  descend with canonical scalar comparison natural isomorphisms" returned
  eight generic exact-functor/Ext/condensed hits, no match.
* Loogle: `CategoryTheory.NatTrans, CategoryTheory.Functor` returned twelve
  standard natural-transformation constructions and extensionality lemmas,
  no coefficient-stage descent statement.
* Mathlib CategoryTheory grep: `pseudocolimit|StageSystem|descNatTrans`, zero hits.
* Direct rg searches of slopmaster2/WeilConjectures and the shared lean/Sheaf
  for the blueprint id, `PbcDirectImageBetaSpec`, `PbcPullbackBetaSpec`, and
  `pbcDescentOperations` found no existing complete statement or predicates.
  Existing StageSystem infrastructure is reused. The dependency's canonical
  rational comparisons are reused directly rather than redefined.

Earlier search records, including LeanSearch's service failure, are retained in
searches.jsonl. No notion from Mathlib or upstream is duplicated.

### Validation

The initial local overlay timeout was in PbcScalarExtension before the delivery
module was reached. After the unchanged wrapper rebuilt that overlay, the full
repaired module compiled cleanly with `scompile.py`: exit 0, sandbox 16.5 seconds,
library export 33.9 seconds, no errors or warnings. This validates both added
beta predicates and all four of their applications with the independent universe
parameters. No compiler limits or live sources/tools were changed.

The node copy was refreshed from current shared main: its only changed key is
`lean`. The primary signature is extracted verbatim from the Lean file. No line
exceeds 100 characters. The required final dry run is recorded below on completion.

Final required `deliver2.py NC prop-weil-pbc-descent-functors --no-push` completed
with exit 0 and printed `OK (dry run)` for temporary commit `e0dba563c0`:
compilation and preflight passed except the independent second reading, which
the wrapper explicitly reserves for the next reader. Exactly the intended
module, item node and report were staged. Nothing was pushed. Full output is
retained in `scratch/canonical-beta-dry-run.log`.

## Second reading by NC

I reread the current node copy, the main-20261015 source statement and proof, and
both recorded statement dependencies before checking the module. The node's
objects, hypotheses, and clauses match as follows.

* The prime `l`, field `Ω : Type w`, `Field Ω`, `Algebra ℚ_[l] Ω`, and
  `IsAlgClosure ℚ_[l] Ω` are the coefficient setup of the concrete
  `pbcScalarSystem` categories. `T`, `S`, `X`, `Y`, `X'`, and `Y'` are
  `Scheme.{u}` with noetherian, finite-dimensional, and stalkwise `l`-unit
  hypotheses. These are exactly the standing hypotheses of the dependency
  categories; no characteristic or universe equality is added.
* The general family is `CoherentExactMorphism.base.Φ` and `.β`, with `.coh`,
  `.additive`, `.commShift`, `.betaCommShift`, and `.triangulated`. The fixed
  PBC systems provide the normalized identity and associator equations. The
  conclusion `Morphism.DescentSpec` contains additivity, a descended shift and
  triangulatedness, so it renders the node's exact descended functor.
* `DescentSpec` quantifies every `K`, `L`, common stage `M`, stage bounds, and
  representative `u`. Its equality is the exact displayed composite
  `β.hom.app ≫ Φ_M.map u ≫ β.inv.app`, followed by the target `mkHom`.
* `descNatTrans` is rendered with the target stage inclusion map. The predicate
  quantifies arbitrary compatible transformations, pointwise equality of their
  stage components, identity, and vertical composition; `Hom.comm` supplies the
  compatibility equation. The module docstring records whiskering and
  horizontal-composition equations as the same componentwise argument.
* `pbcQbarCategory` is the recorded pair-category abbreviation, so the Qbar
  identification is present without an envelope or replacement category.
* The application takes a `ChosenCartesianSquare` and exactly four conditional
  constructibility-preservation hypotheses. It concludes the four actual stage
  functor equalities, four canonical beta predicates, exact descent for all four,
  and a compatible exchange `Ex` whose components are the localization of
  `pbcActualCompletedExchange`. `ExQ` is the required conjugated descended
  transformation and its component formula is stated explicitly.
* `PbcDirectImageBetaSpec` and `PbcPullbackBetaSpec` quantify every coefficient
  inclusion, including equal fields, and every integral object. They identify
  the beta components with the unique rational comparisons from
  `pbcScalarDirectImage_rational` and `pbcScalarCompletedPull_rational`; the
  pullback clause uses the inverse beta orientation required by the node's
  transition convention. Thus the H3 omission in the returned delivery is
  repaired and the canonical operation data are fixed rather than arbitrary.

Edge cases were checked in the signatures and formulas: repeated/equal fields,
identity transitions, identity scheme maps, zero objects and maps, empty schemes,
dimension zero, arbitrary common stages, and all allowed primes remain included.
The finite-stage index is nonempty because it contains the base field; the
concrete category therefore has no separate empty-index case. The coefficient
universe `w` and scheme universe `u` remain independent, and no small-site
universe is silently changed.

For the required searches I ran LeanFinder on coherent exact functor descent,
Loogle on `CategoryTheory.NatTrans, CategoryTheory.Functor`, and grep for
`pbcDescentFunctors|PbcDirectImageBetaSpec|PbcPullbackBetaSpec` in the project,
source, and Mathlib. The results were generic exact-functor/natural-transformation
infrastructure or no hits; none states this proposition. The existing
StageSystem functor and the dependency comparisons are reused. No second
notion, new definition node, dependency replacement, or statement correction is
needed.

No mismatch remains after the H3 repair. The module has real data in all
structures and definitions, exactly two named theorem `sorry`s, source and
blueprint docstrings, `autoImplicit false`, and no line over 100 characters.
The required `scompile.py` run passed for the sandbox and library files (exit 0,
no errors or warnings).
