## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.space_infinitesimal_lift_pseudotorsor`
in `Sheaf.AlgebraicGeometry.SpaceInfinitesimalLiftPseudotorsor`. The item statement,
proof, and proof dependencies are unchanged. Its statement dependencies gain the new
relative-differential definition and the already landed interfaces actually used.
There is no correction, disputed statement, affineness restriction, or existence of lifts.
Both modules have compiled through scompile.py, separately and in dependency order.

Hypotheses and objects, clause by clause:

* `S : Scheme.{u}` and `X Y : AlgebraicSpace S` use the recorded scheme and fppf-sheaf
  algebraic-space definitions. `f : X ⟶ Y` is the natural transformation over S.
* `hf : MapIsLocallyOfFinitePresentation f` is the existing compatible-etale-chart test,
  using the recorded `AlgebraicGeometry.LocallyOfFinitePresentation` on scheme maps.
* `T₀ T : Over S`, `j : T₀ ⟶ T`, and `hj : IsFirstOrderThickening j.left` encode the
  square-zero closed immersion over S. No scheme is required to be affine.
* `a₀ : yoneda.obj T₀ ⟶ X.obj.obj` and `b : yoneda.obj T ⟶ Y.obj.obj` are the two
  specified maps over S. `comm` is exactly `a₀ ≫ f.hom.hom = yoneda.map j ≫ b`.
* `relativeDifferentialModule f` uses the actual inverse-image structural ring map
  `cotangentRingMap f` on the existing affine basis, the existing sheafified differential
  construction `SheafDifferentials.omega`, and the inverse of the actual basis restriction.
  `relativeDifferentialSection` transports ds by that equivalence's inverse counit.
  `HasInfinitesimalDifferentialCharts f` explicitly asserts agreement with the recorded
  scheme `g.left.relativeDifferentials` on every compatible pair of etale scheme charts.
* `infinitesimalDifferentials f T₀ a₀` is E: the existing `moduleTensorPullback` of this
  differential module along the actual morphism represented by a₀. Its tensor sections
  are `moduleTensorSection`, with the specified adjunction unit.
* `M : ThickeningSiteModel (infinitesimalSchemeMap j)` is a normalized presentation of
  the common etale site, with cartesian reduction maps and the actual quotient on rings.
  `I : SquareZeroIdeal M` is a presentation of the actual kernel: its inclusion is
  injective, has precisely that kernel image, and its scalar law is the quotient action;
  its square is zero. The theorem supplies `I.obj.IsQuasicoherent`, not a new assumption.
  The existential site/kernel presentation accommodates any first-order j; it does not
  assume the site equivalence or an unspecified ideal as input.
* `infinitesimalHom f T₀ a₀ I.obj` is the existing internal Hom `SheafOfModules.homObj`.
  Its sections are module homomorphisms on localized etale sites, not just homomorphisms
  of the section modules. `infinitesimalTranslationPresheaf` is that Hom transported
  through the normalized thickening equivalence and restricted to scheme etale tests:
  this is j_* Hom(E,I_et).
* The theorem's existential `H : T.left.Modules`, `_hH : H.IsQuasicoherent` and `e`
  present the restriction H in the node together with its canonical comparison back to
  j_* Hom(E,I_et). Precisely, e compares the recorded associated etale sheaf of H with
  the literal internal Hom direct image; `IsInfinitesimalTranslationComparison` requires
  linearity through the actual reduction-ring map. Restriction of this comparison to
  Zariski opens, and the recorded tensor-open-section identification, identifies H with
  the restriction specified by the node. Thus H is a representative of that specified
  module, not an arbitrary quasi-coherent group used as a translation group. This
  formulation retains the isomorphism and scalar comparison rather than an equality
  of differently constructed module objects.
* `InfinitesimalLifts` has exactly the two required equations. Its second equation is
  on the actual scheme pullback `pullback j (infinitesimalTestMap T U)` in Over S.
  This represents the sheaf fibre product. `infinitesimalLiftPresheaf.map` composes
  with the map of test schemes. `Presheaf.IsSheaf` is on `T.left.smallEtaleTopology`.
* `act` acts by the associated abelian etale sheaf of H. The first two equations
  specify zero and addition, the third specifies naturality under every site morphism,
  and `Function.Bijective (fun h ↦ act U h a)` is required for every supplied lift a.
  It does not assert a lift, even locally.
* `IsInfinitesimalAddition` fixes the derivation interpretation and its sign: for all
  compatible affine target charts, reduced chart maps, lifted chart maps, and functions s,
  the new ring map sends s to its old image plus `I.inclusion` of h applied to 1 tensor ds.
  The differential and tensor section are the actual canonical constructions. The formula
  quantifies over all chart lifts, including all restrictions; formal etaleness of the
  target chart ensures these test maps locally exist. It does not replace a canonical
  derivation with an unconstrained map or an unnormalized isomorphism.

Universes: schemes and rings remain in u; the full etale site has objects in u+1.
Internal Hom on the full site has section universe u+1. Its comparison with the u-valued
associated etale sheaf uses only `AddCommGrpCat.uliftFunctor.{u+1,u}`; it does not identify
site object and morphism universes, restrict tests, or lift the structural rings.

Dependency declarations read and used:

* Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms.
* Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, its small etale site,
  structure sheaf and Modules. Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `LocallyOfFinitePresentation`; Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties:
  `MapIsLocallyOfFinitePresentation`, whose full signature is the chart test.
* WeilConjectures.AlgebraicGeometry.Thickening: `IsFirstOrderThickening`.
* WeilConjectures.AlgebraicGeometry.Modules.Differentials:
  `Scheme.Hom.relativeDifferentials`, with its scheme-morphism parameter and docstring.
* Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules`, transparently Mathlib
  `SheafOfModules`; Sheaf.AlgebraicGeometry.CoherentFiniteType exposes Mathlib
  `SheafOfModules.IsQuasicoherent`, the predicate used here, rather than its conjunction
  with finite type or the distinct coherence predicate.
* Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.Etale`, `smallEtaleTopology`.
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `fst`, `snd`.
* WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf:
  `Scheme.Modules.etaleTensorSectionsSheaf`; its actual sections are tensor pullback
  global sections, with restrictions already fixed in EtaleTensorSections.
* Sheaf.AlgebraicGeometry.SpaceSquareZeroStalkData: `SquareZeroIdeal`;
  Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData: `ThickeningSiteModel`.
* Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: `moduleTensorPullback`,
  `moduleTensorSection`, and their prescribed adjunction unit.
* Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction: `schemeRestriction`.
* Sheaf.AlgebraicGeometry.SpaceCotangentRingMap: `cotangentRingMap`;
  Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: `smallModuleEquivalence`.
* Sheaf.CategoryTheory.Sites.InverseImageDifferentials: `SheafDifferentials.omega`
  and `derivation`; WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom:
  `SheafOfModules.homObj` and the localized module-hom interpretation.

Already stated proof dependencies are imported privately: AlgebraicSpaceFpqcSheaf,
FpqcFinerThanEtale, SchemeZariskiEtaleQuasiCoherentEquivalence,
ModulePullbackPushforwardAdjunction, and Mathlib.CategoryTheory.Adjunction.Limits for
`Adjunction.leftAdjoint_preservesColimits`. The other proof-only dependencies currently
have no Lean record and introduce no additional notion needed to type this statement.
Their proof roles are spelled out in the main theorem's five-step docstring.

Edge cases checked: empty T and empty etale tests (the lift sheaf then has its required
unique empty-domain section); an object with no lift (the orbit assertion quantifies
only over an existing a); j an identity and I=0 (zero translations, unique possible lift);
f an identity (zero relative differentials and at most one lift); arbitrary nonaffine
T (all tests and all restrictions remain); arbitrary characteristic (no field or
characteristic assumption); zero modules; charts which are not surjective. The chosen
site/kernel presentations assert no global lifts into X.

Searches made before writing: msearch.py leanfinder query "For a locally finitely
presented morphism of algebraic spaces the sheaf of square zero lifts is a pseudo
torsor under the quasi coherent module of derivations" returned generic presheaf
Derivation/HasDifferentials declarations, not this space statement. Loogle
`liftOfDerivationToSquareZero` returned the square-zero ring derivation-to-lift API
and its formulas, not the sheaf theorem. LeanSearch "relative differentials of a
morphism of algebraic spaces and sheaf of lifts across a square zero thickening"
returned generic differential presheaves and ring linearization declarations. Msearch
grep `PseudoTorsor|liftOfDerivationToSquareZero|relativeDifferentials` in
AlgebraicGeometry returned zero Mathlib matches. Direct rg in WeilConjectures and
Sheaf found the scheme differential module, the generic sheaf differential module,
and the normalized space cotangent ring map, but no space relative differential
specialization or this pseudo-torsor. The exact blueprint-id search in WeilConjectures
returned no declaration. DAG and blueprint_refs searches found generic
`def-sfb-sheaf-differentials`, which is reused, but no node for this space specialization.
The new node records raw current search outputs and the local-search findings.

## New nodes

`def-sfb-space-relative-differential-module` defines the relative differential module
of an algebraic-space morphism and its universal differential on the existing affine
basis, from Stacks 08TP, 0618, 0619, 05ZF. Its two declarations are real constructions,
with no postponed data and no theorem obligations. It uses the existing generic
`SheafDifferentials.omega` and `derivation`, `cotangentRingMap` and affine-basis
restriction equivalence. The scheme-only recorded relative differential declaration
cannot accept a space morphism; the DAG searches found only the generic sheaf notion
and the scheme notion. The new node's three search kinds are recorded verbatim.

## Second reading by Q01

Repair reading: I reopened the item node, the complete theorem signature, both
Lean modules, and the cited Stacks clauses, and checked each hypothesis and
conjunct in order.

1. The ambient objects are exactly the node's `S`, `X Y : AlgebraicSpace S`,
   morphism `f : X ⟶ Y`, and hypothesis
   `hf : MapIsLocallyOfFinitePresentation f`; no finiteness assumption is added.
2. The thickening data are exactly `T₀ T : Over S`, `j : T₀ ⟶ T`,
   `hj : IsFirstOrderThickening j.left`, maps `a₀` and `b` into `X` and `Y`,
   and the displayed commutative equation
   `a₀ ≫ f.hom.hom = yoneda.map j ≫ b`.  The Lean binder and equation use
   precisely those objects.
3. The first conclusion is `HasInfinitesimalDifferentialCharts f`, with the
   chart agreement encoded by the existing scheme differential module.  Its
   definition supplies the stipulated `Nonempty` chart isomorphism; this is
   only the chart-test clause and is not silently strengthened to a chosen iso.
4. The second conclusion is
   `Presheaf.IsSheaf T.left.smallEtaleTopology
   (infinitesimalLiftPresheaf f j a₀ b)`.  The presheaf is the defined one, and
   `InfinitesimalLifts` retains both equations: reduction along `j` gives `a₀`
   and composition with `f` gives `b`.
5. The existential site data are exactly
   `M : ThickeningSiteModel (infinitesimalSchemeMap j)` and
   `I : SquareZeroIdeal M`; the conjunct `I.obj.IsQuasicoherent` is present
   verbatim.  The square-zero ideal is the actual kernel object on the
   cartesian thickening model, not an arbitrary ideal or a mere existence.
6. The next existential binds `H : T.left.Modules`, its supplied
   `_hH : H.IsQuasicoherent`, and the module isomorphism
   `e : (Scheme.Modules.etaleTensorSectionsSheaf H).obj ⋙
   AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
   infinitesimalTranslationPresheaf f a₀ M I`.  The `u+1` ulift is retained,
   with no forced equality of site and coefficient universes.  The following
   `IsInfinitesimalTranslationComparison f a₀ M I H e` is a separate conjunct,
   so both the sheaf comparison and its module structure are required.
7. The action existential has exactly the type
   `∀ U : T.left.Etale, H(U) → InfinitesimalLifts ... U →
   InfinitesimalLifts ... U`, rendered in Lean by the displayed
   `etaleTensorSectionsSheaf` object and the `InfinitesimalLifts` presheaf.
8. Its four laws were checked separately: zero acts as the identity; addition
   acts by iterated addition; restriction along every `r : V ⟶ U` commutes
   with the action and with the sheaf restriction on coefficients; and, for
   every existing lift `a`, `fun h ↦ act U h a` is `Function.Bijective`.
   The last clause asserts orbit bijectivity and supplies no existential lift.
9. The final conjunct is the stated `IsInfinitesimalAddition f a₀ b M I H e
   act`, including the source's derivation sign convention (the
   `IsInfinitesimalAddition` formula is the Stacks 0618/0619 one).  No sign,
   naturality, or scalar clause is dropped.
10. Edge cases checked against the exact binders include empty tests, no
    existing lift, identity thickening and zero ideal, identity morphism,
    zero module, non-affine tests, arbitrary characteristic, and charts that
    are not surjective.  These do not change the statement or introduce a
    hidden existence premise.

The dependency audit now records the three definition owners used by the
statement (`def-trf-scheme-algebraic-space`,
`def-sfb-space-small-ringed-model`, and `def-sfb-space-quasi-coherent-algebra`).
The two theorem nodes removed from `stmt_deps` remain in `proof_deps` (and the
scheme/enlarged-site theorem remains available to the relative-differential
helper where its proof construction needs it), exactly as requested.  The Lean
source and its declaration signature are byte-identical to the delivered
version; this repair changes only DAG metadata and this independent
clause-by-clause report.
