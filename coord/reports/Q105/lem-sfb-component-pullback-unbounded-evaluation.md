## Worker report

The new module `Sheaf.AlgebraicGeometry.ComponentPullbackUnboundedEvaluation` states
`AlgebraicGeometry.ProEtale.CondensedRing.component_pullback_unbounded_evaluation`.
Its only postponed proof is this theorem, with the five DAG proof steps in its docstring.
All helper definitions have real data. There are no new nodes or dependency repairs.
The natural-language statement and its accepted proof split are unchanged.

Source read: Hemo--Richarz--Scholbach, *Constructible sheaves*, Section 3 and the paragraph
before (4.1), Proposition 4.3(1), its proof and equation (4.2), printed pages 8--9.
The source factors the component morphism through the condensed point and calculates
pullback by evaluation on the component quotient. This item states the module evaluation
and ordinary unbounded exact-evaluation version already specified by its DAG split.

Hypothesis and clause correspondence:

- The arbitrary commutative condensed ring is `(Λ : Profinite.CondensedRing.{u})`
  with `[IsCommMonObj Λ.X]`. No topological-ring presentation is assumed.
- The base affine w-contractible scheme is `(W : Scheme.{u}) [IsAffine W]`
  with `[IsWContractibleRing Γ(W, ⊤)]`. The existing affine component quotient is
  `affineComponentSpace W`, retaining its quotient topology.
- The site is exactly `Scheme.ProEt.topology W`, on `W.ProEt`. Its object universe
  is `u+1`, its morphism universe `u`; abelian coefficients and section modules use
  `u+1`. The ordinary derived categories use the already published Grothendieck
  localization instances. No equality of site object and arrow universes is imposed.
- The coherent profinite slice is
  `(coherentTopology Profinite.{u}).over (affineComponentSpace W)`. Its coefficient
  is the existing `profiniteCoefficient Λ.X (affineComponentSpace W)`, defined by
  `overPullback`; this is precisely q_S^*Λ. The theorem supplies continuity,
  braiding and exactness of the fixed `componentInverse W` as existential conclusions,
  not additional hypotheses. That inverse is the Kan-extension/sheafification functor
  of `componentTests W`, chosen from the relative component theorem's characterized
  functor. There is no arbitrary replacement functor.
- The coefficient identification is the ring-object isomorphism `α`. The `β` clause
  identifies q_S^* followed by the component inverse with `upperStarFromPoint W`.
  `NatTrans.IsMonoidal β.hom` and `α.hom.hom = β.hom.app Λ.X` fix its coefficient
  normalization and say that α is the comparison supplied by p_W = q_S π_W.
- The fixed module inverse image is `componentModules Λ.X W α`, and its ordinary
  derived counterpart is `componentDerived Λ.X W α`, both reused from the landed
  evaluation model. These are not new definitions of pullback.
- Every test is `(U : W.ProEt) [IsAffine U.left]`
  with `[IsWContractibleRing Γ(U.left, ⊤)]`. The helper `componentAffineObject W U`
  uses the existing `Scheme.ProEt.componentObject` on its affine qcqs object, and
  `componentAffineObjectMap f` is its existing map on connected components.
- `ComponentPullbackUnboundedEvaluation` quantifies simultaneously over all tests.
  Its `a U` is an isomorphism between the actual section rings, giving
  Λ_S(T→S) ≅ (p_W^*Λ)(U). The first ring is Λ(T): the existing profinite coefficient
  is restriction to Prof/S, so sections at T→S are the sections of Λ at T. This
  statement does not introduce an unrelated coefficient ring.
- `e U : componentSourceSections Λ W U ≅ componentEvaluationTarget Λ W α U (a U)`
  is a natural isomorphism of module-valued functors. Its inverse is the displayed
  rho:(F_W M)(U)→M(T→S); its hom is in the requested pullback direction. The target
  is viewed over the source ring by `ModuleCat.restrictScalars (a U).hom.hom`, so
  linearity is part of its type. Naturality in M is part of `NatIso`.
- The first equation in the proposition is naturality in every test map f:U→V.
  It explicitly intertwines M's component restriction and F_W M's restriction.
- The second group of equations quantifies over every b:U→componentTests(E) and
  component map c:T→E, requiring that c really is induced by b pointwise. It says
  that a and e take restriction along c to the Kan coprojection indexed by b,
  written using `componentAbelianAdjunction W`. This fixes the canonical map,
  rather than asserting existence of an unnormalized abstract isomorphism.
- Both source and target evaluations preserve finite limits and finite colimits:
  the four existential `PreservesFiniteLimits`/`PreservesFiniteColimits` fields.
  Source evaluation at T→S is Γ(T,-|T): localized-site restriction is sectionwise
  (`SheafOfModules.overFunctor` on the slice), followed by terminal evaluation.
  Thus this is also the requested interpretation using restriction to Prof/T.
- `IsIso ...rightDerivedFunctorUnit` for both evaluations states that arbitrary
  unbounded representatives compute right derived sections termwise, canonically.
- `δ` is a natural isomorphism of entire derived functors, from source right-derived
  evaluation to component pullback followed by target right-derived evaluation,
  with scalar restriction. Its equality to `componentEvaluationDerivedIso ... (e U)`
  fixes normalization on every representative: that definition composes the canonical
  right-derived/termwise comparisons with `mapDerivedCategoryNatIso e` and the
  composition comparisons. Consequently the induced chain map has degree n component
  `(e U).hom.app M^n`. It is natural in all derived objects K, and test-map naturality
  follows by applying localization to the explicit preceding test-map equation.
- At U=W the canonical b:W→W×_S S induces c=id_S. The normalization equation specializes
  exactly to the ordinary adjunction-unit pullback of global sections. Identity tests
  have not been omitted.

Dependencies read and used:

- `WeilConjectures.RingTheory.ProEtale.WContractible`, `IsWContractibleRing`, including
  its w-strictly-local inheritance and extremally disconnected component quotient.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`
  and `Scheme.ProEt.topology` (the recorded general-site binding).
- `Sheaf.Paper.ComponentRelativeProfiniteSite`, `affineComponentSpace` and
  `component_relative_profinite_site`, including the universal mapping property,
  finite clopen presentations and final geometric-morphism factorization.
- `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing` (the arbitrary
  ring-object encoding), and the section-ring reconstruction publicly reexported
  through the existing evaluation model.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`, the
  transparent general-site abbreviation of Mathlib `SheafOfModules`; the existing
  evaluation model's `sectionModuleEquivalence` identifies the internal module-object
  presentation with this exact sectionwise module category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`, used for the ordinary unbounded categories.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`,
  `ringedSiteZerothHypercohomologyOfUniverses`: its recorded construction is H⁰ after
  K-injective right-derived global sections. The present entire-object comparison
  uses the same unbounded `rightDerivedFunctor` convention before taking H⁰.
- Added statement dependency `def-zl-condensed-lisse-evaluation-model`, already landed:
  `Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel`, `profiniteCoefficient`,
  `componentTests`, `componentInverse`, `componentModules`, `componentDerived` and
  `Evaluation.sections`. These are the exact existing constructions required here.
  Adding its ID records reuse; it does not change any statement hypothesis or clause.
- Public import `Sheaf.AlgebraicGeometry.AffineComponentSiteProjection` supplies the
  existing component object and induced map. The proof imports are the published
  clopen partition, geometric module transport and inverse-image exactness, exact and
  derived w-contractible sections, and contractible derived tensor evaluation modules.
  The two Mathlib proof-dependency APIs (localization and sheaf-pullback adjunction)
  are already public imports of the statement APIs. The relative-component-lift
  comparison has no recorded module and therefore contributes no additional import.

The size-convention dependency is metatheoretic and has no declaration; universes above
implement its instruction. The instructed example CompactObject module is now a withdrawn
empty module; its node was read, and the current `module`/`public import`/public-section
conventions were used instead of copying withdrawn content.

Edge cases checked: empty W, empty U, zero condensed ring and zero module; U=W with
its identity arrow; identity and composite test maps; arbitrary complexes nonzero in
both arbitrarily positive and negative degrees. No Nonempty, Nontrivial or boundedness
binder is present. Empty coverings force zero sections, so the comparison specializes
to the zero-complex isomorphism, including coefficients whose empty section ring is zero.
There is no source or statement dispute.

Searches actually run for this item:

- msearch leansearch: `exact evaluation of sheaves of modules on a weakly contractible
  scheme and connected component pullback`: eight hits, including
  `SheafOfModules.evaluation` and `sheafSectionsNatIsoEvaluation`; no component theorem.
- msearch leanfinder: `Component pullback of module sheaves evaluated on weakly
  contractible affine schemes equals evaluation on their profinite connected components,
  naturally and on unbounded derived categories`: eight hits, mostly module pullback/free
  sheaf lemmas and `CondensedMod.ofSheafProfinite`; none states this theorem.
- msearch loogle: `SheafOfModules.evaluation, Functor.mapDerivedCategory`: zero hits;
  Loogle reported unknown identifier `Functor.mapDerivedCategory`, so this query did not
  establish nonexistence. Direct source inspection found the exact functor API.
- msearch grep: `component.*[Ee]valuation|[Ee]valuation.*component`, Mathlib/CategoryTheory:
  eight generic evaluation hits, no component-site theorem.
- rg of `component.*evalu`, `component.*pullback` and related patterns in project and
  upstream sources found the existing component and lisse model modules described above.
  Exact node-ID search in upstream WeilConjectures found no theorem for this item.
  Exact proposed-name search in Mathlib, WeilConjectures and Sheaf found no collisions.
  Existing constructions are reused, and the newly stated result is the full
  all-tests linear and unbounded evaluation statement, not the lisse equivalence.

Validation: prescribed scompile.py checked both sandbox and final module names cleanly;
no error and no warning. No global build or direct repository/Git mutation was run.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
