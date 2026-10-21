## Worker report

The module `Sheaf.Paper.RationalPullbackCompositionCoherence` states
`AlgebraicGeometry.Scheme.rationalPullbackCompositionCoherence` and
`AlgebraicGeometry.Scheme.rationalPullbackIdentityCoherence`, both with whole-proof
`sorry`. The two `HasRationalPullback…Coherence` definitions spell out their conclusions
as coefficient equations followed by existential comparisons with tensor, derived-counit,
completion-unit and rationalization normalizations. These are descriptions of the maps
in this very statement, not new independent mathematical notions. Three real section
helpers spell out the ordinary pullback tensor unit, pullback of a scalar, and scalar
multiplication with explicit section types. There are no hollow data definitions.

Source read: Bhatt–Scholze PDF, printed p. 62, Remark 6.8.15. Its module pullback is
inverse image followed by extension along the actual coefficient structure map. The
node's eight-step proof expands its composition/identity compatibility using Stacks
03CB, 0D6D, 07A4 and 099N and reflector-unit normalization. That eight-step argument
is included in the composition theorem's docstring, and the identity specialization
has its own complete proof docstring. No node statement has been corrected or disputed.

Hypotheses, objects and clauses:

- Prime l: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]`
  and `[FiniteDimensional ℚ_[l] E]`. The existing `pbcIntegralDatum l E` and
  `pbcUniformizer l E` supply its lifted integer ring and chosen uniformizer.
- X, X', X'': `{X Y Z : Scheme.{u}}`, with `g : Y ⟶ X`, `h : Z ⟶ Y`.
  The mathematical g composed with h is Lean `h ≫ g`.
- Each scheme is noetherian: `[IsNoetherian X]`, and the corresponding Y/Z instances.
  Finite dimension is `[Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]`, and similarly Y/Z.
  Invertibility of l is `[Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]`, similarly Y/Z.
  The identity theorem and predicate generalize only the X instances they actually use.
- Small pro-etale site: existing `X.ProEt`, `ProEt.topology X`, `proEtaleBaseChange g`;
  site objects retain universe u+1 and morphisms u. No universe equality is assumed.
- Completed coefficients B_X and E_X: `pbcAdicCompletion X (pbcIntegralDatum l E)`
  and `rationalCoefficientSheaf l X E`. `RationalModuleRealization.integralIso` and
  `localizationIso` identify these with the specified inverse limit and its sheaf
  localization; its normalization equations are retained, not replaced.
- Module sheaves/tensor/derived/cohomology: the existing `pbcModules`, `pbcExtend`,
  `pbcDerivedExtend`, Mathlib `DerivedCategory`, and `DerivedCategory.Q`. The realization
  data already include its cohomology and constructibility clauses. These are not extra
  conclusions or assumptions introduced here.
- C_X with compatible etale origins: `PbcBoundedConstructibleComplete X
  (pbcIntegralDatum l E)` with its published property. Q and the raw category are
  `pbcRationalization … (pbcUniformizer l E)` and `PbcRationalCategory …`.
  No idempotent completion and no category of arbitrary continuous coefficients is substituted.
- J and F: `sX : RationalModuleRealization l E X` (and sY/sZ), whose `objects` and
  `fractions` are exactly J(QK)=F(K) and J(f/varpi^n)=varpi^(-n)F(f).
  `rationalPullScalar l E sX` is the recorded inclusion used in F.
- P_g and completed P_g: the published `pbcActualDerivedPull g (pbcIntegralDatum l E)`
  and `pbcActualStrictCompletedPull (pbcIntegralDatum l E) g`. The existing
  `ag.integral.completedFunctor l E` is their restriction to the actual integral category.
- G_g and alpha_g: `rationalPullDerived l E g ag.rationalCoefficient`, and `ag.alpha`.
  `ag`, `ah`, `ac` range over the recorded normalized comparison data. Their
  `coefficient_square`, `module_unit`, `derived_normalization`, `alpha_normalization`,
  `raw_objects` and `raw_fractions` fix all the data; the theorem does not take an
  unconstrained natural isomorphism as an extra assumption.
- Integral coefficient composition: the first four conjuncts of
  `HasRationalPullbackCompositionCoherence` state finite coefficient composition,
  composition of `completedCoefficientMap`, its equality after every
  `pbcAdicProjection`, and the localized coefficient composition. They explicitly insert
  `(proEtaleRingInverseImageComp h g).hom`. The projection equation ends at
  `completedCoefficientComponent`; no inverse image/limit interchange is claimed.
- Ambient tensor formula: `moduleComp` is constrained on all m,e',e'' on base-changed
  charts, including `Over.pullbackComp` to identify the charts. `rationalCoherenceUnit`
  inserts 1 tensor m; the right side multiplies e'' by `rationalCoherenceScalar … e'`,
  the actual localized structure map applied to the pulled-back e'. This is the node's
  e'' tensor e' tensor k ↦ e'' d_h(e') tensor k. These local generators determine the
  sheafified balanced map. The inverse of the isomorphism inserts 1.
- K-flat representative computation: the `ambientComp` equation with
  `rationalPullComplexCounit` and `NatIso.mapHomologicalComplex moduleComp` specifies
  the derived comparison by the ordinary balanced one. It holds for every cochain
  representative and in particular for flat-term K-flat representatives, where the
  computation counits are invertible. It is the canonical derived-counit square,
  without choosing representative objects for the derived category.
- Conjugation by specified gamma: the `integralComp` equation is
  P_h(gamma_g) followed by gamma_h and integralComp = ordinaryComp followed by gamma_hg.
  Here ordinaryComp is the inverse of the published `pbcActualDerivedPullCompIso`.
  It is the reflector-unit equation fixing the completed compositor, before cancellation.
  The existing comparison makes the actual strict units invertible on these objects.
- Rationalized compositor: `rawComp` has each QK component fixed by Q of integralComp,
  with only the transports from the recorded `raw_objects` equalities.
- Requested composition diagram: the last conjunct is literally equality of natural
  transformations `whiskerRight rawComp.hom sZ.J ≫ ac.alpha.hom` and
  `whiskerLeft ag.rawPull ah.alpha.hom ≫ whiskerRight ag.alpha.hom G_h ≫
  whiskerLeft sX.J ambientComp.hom`. Its domain is the entire raw category.
- Identity coefficient clauses use the existing `proEtaleRingInverseImageId` on every
  finite quotient, on the actual limit, and on its localization. `moduleId` sends
  e tensor the unit-section of m to e times m restricted along `Over.pullbackId`.
  Its derived-counit equation fixes `ambientId`. `integralId` is normalized by
  gamma_id followed by integralId = `pbcActualDerivedPullIdIso`. `rawId` is Q of that
  integralId on QK. The last conjunct is the equality of natural transformations
  `a.alpha.hom ≫ whiskerLeft sX.J ambientId.hom = whiskerRight rawId.hom sX.J`.
  Thus conjugation preserves the ordinary identity removing the inserted 1.

Dependency declarations read and used (names in `AlgebraicGeometry.Scheme` unless noted):

- `Sheaf.Paper.RationalModuleRealizationFunctor`: `RationalModuleRealization`,
  `rationalModuleRealizationFunctor` and their full normalization signatures/docstrings.
- `Sheaf.Paper.RationalRealizationPullbackComparison`: `RationalPullIntegral`,
  its `completedFunctor`, `RationalRealizationPullbackComparison`,
  `rationalRealizationPullbackComparison`, `rationalPullModule`, `rationalPullDerived`,
  `rationalPullComplexCounit`, `rationalPullScalar`.
- `Sheaf.Paper.PbcQbarCompletedPullback` publicly retains `PbcActualStrictPullback`:
  `pbcActualStrictCompletedPull`, `pbcActualStrictCompletedPullUnit`,
  `pbcActualCompletedPullback_tower`; no common-stage Qbar object replaces C_X.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`, coefficient ringSystem,
  completedRing and quotient projections, and its published datum-indexed aliases.
- `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete` and its
  underlying `PbcBoundedConstructibleComplete`; `Sheaf.Paper.PbcRationalCategory`:
  `PbcRationalCategory`, `pbcRationalization` and the canonical scalar action.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `FiniteLocallyClosedStratification`; `Sheaf.Paper.ContinuousConstructibleModule`:
  `AlgebraicGeometry.ProEtale.IsContinuousConstructible`. The realization module retains
  the node's finite-stratification locally finite-free rational constructibility clause.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing its coefficient constructions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`; Mathlib DerivedCategory.Basic,
  HomologySequence and Sites.Proetale: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`, `Scheme.ProEt`.
- Proof imports: `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`,
  `CategoryTheory.ConstantCompletion.equivalence`,
  `CategoryTheory.ReflectedCompositor.unit_normalization`, `wfCompletionReflector`,
  `CategoryTheory.ringedPushforward_completion`, and
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Existing inverse-image, localization and site-composition interfaces enter through the
  recorded comparison module. The duplicate WeilConjectures/Sheaf site-composition owners
  are not both imported explicitly.
- The following definition nodes are added to stmt_deps (allowed by brief §5):
  `def-weil-pbc-ambient-ringed-exchange`, for the published ordinary integral composition
  and identity maps in its publicly retained `Sheaf.Paper.PbcActualRingedExchange`;
  `def-per-proetale-ring-inverse-image-comparisons`, the new ownership node for the
  canonical `proEtaleRingInverseImageComp` and `proEtaleRingInverseImageId`. It records
  those unchanged real-data definitions with `existing: true`. The theorem node
  `lem-weil-pbc-profinite-coefficient-inverse-image` is not a statement dependency:
  no theorem choice is used to construct these two comparisons. There are no dependency modules.

Edge cases checked: arbitrary g,h (no smoothness, flatness or properness), identity
maps, repeated schemes, zero module/zero tensor sections, the empty scheme and empty
stratifications, first positive coefficient quotient (`n=0` means exponent 1), and raw
fractions of every denominator exponent including 0. The formula explicitly includes
all e',e'' and not just scalar 1. No isomorphism of completed or rational structure
maps is assumed. The local site and coefficient universe conventions are preserved.
The natural-transformation equations quantify on all raw arrows through their actual
functors, whose recorded fraction equations are retained. The theorem does not require
full faithfulness of J.

Searches (2026-10-21):

- msearch.py leanfinder: “Rational realization of completed integral pullback respects
  composition and identity via normalized completion units”: 8 unrelated completion/
  valuation hits; no matching statement.
- msearch.py leansearch: “Derived rational module pullback comparison respects identity
  and composition after completion”: 8 hits, ordinary sheaf pullback identity laws,
  adic module-completion functoriality, scheme-module pseudofunctor laws and unrelated
  scalar constructions; no normalized integral/rational realization statement.
- msearch.py loogle `SheafOfModules.pullbackComp`: 5 hits, ordinary sheaf-module
  pullbackComp, two identity laws, pullback_assoc and its conjugacy equation.
- msearch.py grep `pullbackComp|pullback_assoc|completion.*[Uu]nit` in
  `Algebra/Category/ModuleCat`: 10 ordinary presheaf/sheaf pullback hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: rational/coherence and
  completed/composition searches found the integral canonical comparators in
  PbcActualRingedExchange, the normalized realization comparison, and scalar-field
  comparison coherence; no theorem for the present realization/alpha maps.
  The literal node-id search in WeilConjectures and exact searches for all new names
  in Mathlib, WeilConjectures and Sheaf returned no declaration.
- The existing ring identity was found in ProfiniteCoefficientInverseImage; it is
  reused. An initially considered isomorphism-inverse-image section comparison has
  a transported presheaf target and was not substituted for a sheaf-ring identity.

Verification: every compile uses the prescribed scompile.py wrapper. Definitions
were revised to keep section types explicit and to package the long conclusion as
propositions, avoiding expensive generated structure projections. The complete
single module, including both sorry statements, is compiled; no file splitting,
combined-source compile, global build or live source edits occur. Final preflight
and delivery results are recorded below when available.

## Second reading by Q16

This is the author's clause-by-clause self-audit, not a claim of an independent
worker review. The dispatcher brief prohibits starting another agent and assigns
independent review to the maintainer. I reread the node and the complete module:
composition direction is h ≫ g; ordinary composition uses the inverse of the
published integral comparison; completed composition retains the original strict
tower unit; both raw normalization transports follow raw_objects in the forward
source and inverse target direction. Identity uses the canonical sheaf-ring
identity, not the differently typed presheaf identification. Tensor coefficients
are arbitrary local sections and the equations concern natural transformations on
all raw fractions. No hypothesis is added and no clause is omitted. No source or
DAG correction is required.

Initial complete dry run: deliver2.py --no-push returned OK for commit 2b3670bf984
(preflight and per-file compile, nothing pushed). Subsequent revisions retain the same
mathematical signatures and avoid unfolding the two conclusion predicates at their
sorry theorem declarations. Final dry run and push are performed on these exact files.

## New nodes

`def-per-proetale-ring-inverse-image-comparisons` owns exactly the existing
`AlgebraicGeometry.Scheme.proEtaleRingInverseImageComp` and
`AlgebraicGeometry.Scheme.proEtaleRingInverseImageId` in
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage` (lines 173 and 162).
For arbitrary scheme morphisms f:X→Y and g:Y→Z its composition arrow is
`proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1} ≅
proEtaleSheafInverseImage g CommRingCat.{u + 1} ⋙
proEtaleSheafInverseImage f CommRingCat.{u + 1}`; its identity arrow is
`proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1} ≅ 𝟭 _`.
The actual bodies use `conjugateIsoEquiv` on the specified sheaf adjunctions and
`Functor.sheafPushforwardContinuousComp'` / `sheafPushforwardContinuousId'`
for `MorphismProperty.Over.pullbackComp` / `pullbackId`. Thus the new statement's
mate normalization matches the existing definitions clause by clause, without
adding hypotheses. Identity, repeated schemes and empty schemes remain included;
commutative coefficient rings need not be finite. The object/morphism universe
split is unchanged. The source is Stacks 098T(2), giving direct image by base
change on charts, and 098U, giving composition from that description; both were
opened in local proetale.tex. No definition is rewritten and no module is added.

Searches on 2026-10-21: msearch LeanSearch and LeanFinder used “Canonical
composition and identity natural isomorphisms of inverse image functors on ring
sheaves over small pro-etale sites as mates of base change comparisons”. Each
returned 8 hits on general sheaf-module pullback or categorical comparisons, not
these specialized declarations. msearch grep for
`proEtaleRingInverseImage(Comp|Id)|sheafPushforwardContinuous(Comp|Id)` returned
12 general Mathlib hits. Project rg found the two existing definitions and their
consumers; no WeilConjectures match. Exact DAG searches and inspection of every
definition-node lean record found no owning definition node. The theorem node
lists these helpers but is not their definition owner. blueprint_refs.py search
“inverse image composition” found 0 nodes. Raw msearch result records are retained
in the new node's mathlib_searches. Reusing these declarations is therefore required;
the new DAG node supplies their missing definition ownership only.

## Repair of return H2 (head ef2a70e15342)

The initial saved-packet dry run passed as commit 1b0a4c5fba3 against current main.
I retained the entire Lean module and its theorem signatures. The independent
return identifies one semantic DAG fault not detected by that dry run: the
statement cited a theorem only for its plain helper definitions. I replaced that
added theorem dependency by the new definition node above, with existing:true
records for exactly the unchanged helpers. The original main-branch stmt_deps
are preserved, and the already-landed ambient-ringed-exchange addition is retained.
No mathematical statement or source definition changes.

Second reading of the repair by Q16: I reopened both helper bodies, the item's
coefficient clauses, and both final natural-transformation equations. Composition
uses the comparison in the direction inverse-image-of-composite → iterated
inverse image; identity uses inverse-image-of-identity → identity. The newly
recorded declarations have exactly those types. They are real conjugateIsoEquiv
constructions, with no `.choose` from the profinite inverse-image theorem. The
new node depends only on the existing inverse-image definition node, so it creates
no dependency cycle. The unchanged module still renders the coefficient, tensor,
derived-counit, completed-unit and rationalized composition/identity clauses
described in the Worker report. The only requested H2 defect is repaired.
