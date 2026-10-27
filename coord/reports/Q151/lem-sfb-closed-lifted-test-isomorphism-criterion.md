## Worker report

Item: lem-sfb-closed-lifted-test-isomorphism-criterion. The module is
`Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion`, namespace
`AlgebraicGeometry.ProEtale.ClosedLiftedTestIsomorphismCriterion`.
It states the node in eight named theorems, each proved only by `sorry`, and constructs
one map from an actual degree-zero module morphism. No node statement or dependencies
were changed; no new independent notion or dependency repair was needed.

Hypotheses and clauses:

- Commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`
  with `[MonObj Λ] [IsCommMonObj Λ]`. This is the unbundled form of the recorded
  `Profinite.CondensedRing`; no continuous-function presentation is assumed.
- Pulled-back coefficients: every module category is `Mod (Sheaf
  (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)`.
  `condensedRingObj` is the underlying object of the recorded `coefficientRing`.
- Small-site and coefficient sizes: `Scheme.{u}`, `Profinite.{u}`, sites in object
  universe `u+1`, and abelian coefficients `Ab.{u+1}`. The site's object and morphism
  universes are not identified. All variables are explicit; `autoImplicit` is false.
- Closed affine immersion: `A : Type u`, `[CommRing A]`, `I : Ideal A`,
  `closedMap A I = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.
  This specifies precisely Spec(A/I) → Spec A, with no finiteness of I.
- Affine ind-etale basis and specified lift: `V : (Spec (.of (A ⧸ I))).AffineProEt`
  and `(Scheme.AffineProEt.closedSiteLift A I).obj V`. No alternative lift is chosen.
- The test family is rendered inline by the two `IsWContractibleRing` conditions
  on the global rings of V and its specified lift, avoiding a second test-family
  definition. Affineness follows from `AffineProEt`.
- Covering by tests: `closed_lifted_tests_cover` supplies a presieve `R` whose generated
  sieve belongs to the restricted affine pro-etale topology and whose every domain
  satisfies both test conditions. This is a covering by exactly the stipulated tests,
  with no arbitrary-small family universe or nonempty-family requirement.
- Quotient and geometric fibre: `closed_lifted_test_geometry` asserts `IsPullback`
  for the specified inclusion and structural maps, and a ring equivalence from the
  quotient of the lift's global ring by `I.map` of the structural ring map to Γ(V).
  Its equation on every quotient class identifies it with the actual inclusion's
  global-section map. Thus this is the specified C/IC identification, not an arbitrary
  abstract ring equivalence.
- Henselian pair: the same theorem asserts `HenselianRing` for that very global ring
  and that same extended ideal. This is the recorded henselian-pair notion.
- Exact evaluation on internal modules: `closed_lifted_test_evaluation_exact` gives
  both `PreservesFiniteLimits` and `PreservesFiniteColimits` for `Mod.forget` followed
  by underlying abelian sheaf evaluation at the test. For an additive module-evaluation
  functor these say exactness; the internal/sectionwise module equivalence preserves
  these same sections and their kernels/cokernels.
- Joint detection on unbounded objects: `closed_lifted_tests_detect_isomorphisms`
  quantifies over arbitrary K,L in the full `DerivedCategory`, and a morphism b.
  IsIso of `(sectionsOver Λ V.hom).map b` for every test implies `IsIso b`.
  `sectionsOver` is exact pullback followed by the ordinary right-derived module
  sections, hence precisely RΓ(V,-) with values in `DerivedCategory Ab.{u+1}`.
- Arbitrary affine f and bounded-below K: the main theorem has `[IsAffine X]`,
  `f : X ⟶ Spec (.of A)`, an arbitrary cartesian presentation `XZ,h,fZ,w`,
  and `K : DerivedCategory.Plus` of the specified internal modules. It imposes no
  integrality, lisseness, properness, or additional bounds.
- T and T0 and their canonical restriction: `testRestriction Λ A I w.toCommSq V`
  uses the actual pullbacks of f along the lift and fZ along V. The cartesian square
  identifies the latter with X ×_U V. Its definition uses the actual induced closed
  test-fibre map `testMap`, the derived adjunction unit `restrictionOver`, and canonical
  composition comparisons. The hypothesis `hK` asserts IsIso of its component at K.
- Specified exchange: the conclusion is `IsIso ((exchange Λ w.toCommSq).app K.obj)`.
  The imported `exchange` is `Adjunction.squareExchange` for the canonical exact-derived
  adjunctions; `square` is the pullback composition comparison. This is exactly the
  prescribed counit adjunct, not merely existence of some isomorphism.
- Naturality in K: `closed_exchange_naturality` is the natural-transformation equation
  at any map `t : K.obj ⟶ L.obj`, with K,L bounded below.
- Square isomorphisms and pro-etale base change: `closed_exchange_base_change_naturality`
  retains all four vertical cube maps `a,v,t,k` and its four cartesian faces `wf,ws,wh,wZ`.
  Its displayed equation compares the exchange along the original closed immersion,
  then the exchange for `wZ`, with the base-change comparison for f followed by the
  localized closed exchange, using `square` for the source/target compositions.
  `[WeaklyEtale v]` is exactly a base object of the small pro-etale site; no assumption
  of weak etaleness of the closed immersion is imposed. Isomorphisms of squares are
  included by taking the four vertical maps to be isomorphisms.
- Entire parameter objects and further parametrization: that cube equation quantifies
  over every scheme U' and every weakly etale v:U'→U, with no affine hypothesis on U'.
  In particular set U' to the domain and v to the structural map of
  `(profiniteToProEtOf U).obj Q`, for any `Q : Profinite.{u}`. Apply the same theorem
  a second time with U' replaced by its entire profinite parameter object. No point
  of Q, section of v, nonemptiness of Q, or clopen subset is selected. The canonical
  pullback comparisons in the equation supply the composition identifications.
- Arbitrary scalar map: `c : Λ ⟶ Λ'` with `[IsMonHom c]`, and commutative ring-object
  structures on Λ'. No flatness or injective-preservation hypothesis is imposed.
- Actual degree-zero module map: M,N are ordinary internal module objects and
  `t : M ⟶ (Mod.comap (coefficientMap c X)).obj N`. `degreeZeroCoefficientMap` is
  the map of `DerivedCategory.singleFunctor _ 0` followed by the canonical exact
  restriction-of-scalars comparison. Its data is explicit, without `sorry` or choices.
- Scalar/exchange square: the first equation in `closed_exchange_coefficient_naturality`
  compares exchange after the canonical source pullback/scalar comparison and
  `restrictPush c f` with scalar restriction of the Λ' exchange followed by
  `restrictPush c fZ` and the canonical target pullback/scalar comparison.
  The second equation is naturality at the actual induced degree-zero map. Combining
  these equations gives precisely the commuting exchange square for t:M→Res N.
- Direct comparisons and ordinary extension unit: `restrictPush` is reused from the
  model, defined by `rightDerivedPullback` of the ordinary section identity
  `comapLowerStarIso`. No invertibility is asserted. Specializing N to
  `(Mod.extendScalars (coefficientMap c X)).obj M` and t to the ordinary
  `Mod.extendRestrictAdjunction` unit makes `degreeZeroCoefficientMap` definitionally
  the model's `scalarUnit`, i.e. x↦1⊗x. No derived scalar extension replaces it.
  Coefficient equations on parameter objects are the same coefficient theorem for
  the localized cartesian squares, related by the preceding cube equation.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, transparently
  `Mon (Sheaf (coherentTopology Profinite) Ab)`; used in its unbundled presentation.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, and `profiniteToProEtOf`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `ModObj`, `Mod.forget`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward`; its body is the total right-derived
  functor of `lowerStar`. The publicly imported derived module framework provides
  the actual K-injective adjunction, not derived abelian pushforward.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  here its concrete quotient-spectrum case is fixed, not additional input data.
- `WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift`:
  `Scheme.AffineProEt.closedSiteLift`.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`:
  `Scheme.AffineProEt`, `AffineProEt.topology`, `AffineProEt.toProEt`.
- `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: recorded henselian terminology;
  `HenselianRing` is Mathlib's exact henselian-pair class.
- `def-weil-size-convention` is the recorded metatheoretic convention, with no
  declaration to import; its compatible sizes are instantiated as described above.
- `Sheaf.Paper.ClosedTestDerivedExchangeModel`: `pull`, `adj`, `square`, `exchange`,
  `closedMap`, `testRestriction`, `sectionsOver`, `restrict`, `restrictPush`, and
  the canonical comparison maps. This already-listed proof dependency supplies the
  canonical arrows needed to state the item; it is publicly imported for that use.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `CondensedRing.derivedComapUpperStarIso`.
- Every recorded proof-dependency module available in the clone is imported, directly
  or through the public model imports. The Mathlib leaves use Mates, Pretriangulated,
  ExactFunctor and DerivedCategory; the w-contractible cover theorem lives in the
  already imported WContractible module. There is no proof import cycle.

Searches for an existing exact statement:

- msearch LeanFinder: “Closed lifted w contractible tests jointly detect isomorphisms
  of derived internal condensed module sheaves”. Eight results: discrete/solid
  condensed modules and constructors, no test/exchange criterion.
- msearch Loogle: `"Sheaf", "IsIso"`. Twelve results: generic sheafification and
  presheaf isomorphisms, no lifted-test statement.
- msearch grep: `(closed|henselian).*(wContract|contractible|exchange)`. Three results,
  minpoly and contractible closed balls, irrelevant to this assertion.
- msearch LeanSearch: “Closed lifted w contractible ind etale tests jointly detect
  isomorphisms in the derived category of internal condensed module sheaves”. Eight
  results: generic localization, condensed categories, discrete modules, and limits;
  no match.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` with the closed/henselian,
  wContract/contractible/exchange patterns located the closed-test model and the
  integral closed-base-change consumer, but no conservative criterion or its full
  coherence assertion. Exact node-id grep in `lean/WeilConjectures` found none.
- Read the full canonical-map signatures in the existing model before using them;
  no independent map or duplicate module-category definition was written.

Edge cases checked before writing: I=0 gives the identity closed subscheme; I=A gives
an empty closed subscheme, where test covers and detection are still meaningful.
The covering presieve allows an empty cover of an empty object. X may be empty;
zero coefficients and zero complexes are allowed. The main bounded-below hypothesis
is not imposed on joint detection. No finite generation of I or nontrivial-ring
hypothesis is present. Profinite Q may be empty; localization uses its entire object.
Coefficient maps may be nonflat and t may be zero; no inverse to restrictPush is used.

Validation: scompile.py compiled the final module separately as a sandbox and as its
library module, both clean (about six seconds each), without errors or warnings.
The first probe's missing explicit base argument to `AffineProEt.topology` was repaired.
Every theorem retains exactly `by sorry`; only the degree-zero induced map has real data.
No statement is disputed and no source-based statement correction is needed.

## Second reading by Q151

Author's second reading, not a claim of independent review: reopened the node and the
complete module, including every theorem signature. I checked the clause correspondence
above against the node's four paragraphs. The main possible pitfalls were dropping
unbounded joint detection, replacing the specified mate by some isomorphism, imposing
weak etaleness on s, replacing the ordinary scalar unit by derived tensor, or assuming
the direct scalar comparison invertible. None occurs in the final signatures.
The base-change theorem's two paths have common source k* s* Rf* and common target
R(fZ')* h'* a*; the pullback-square comparison appears inversely on the target and
source identifications in exactly those directions. The coefficient square's source
is s'* Rf* N after scalar restriction and its target is R(fZ)* h* Res N; both paths
include the canonical coefficient pullback identifications in their natural direction.
The second equation supplies the actual M[0]→Res N[0] input; together they are the
stated coefficient compatibility, including the ordinary extension unit. The general
cube statement includes isomorphisms and entire profinite localizations even when the
parameter object is not affine. The only compile repair was the explicit base scheme
in topology application; it changed no mathematical hypothesis or clause.
