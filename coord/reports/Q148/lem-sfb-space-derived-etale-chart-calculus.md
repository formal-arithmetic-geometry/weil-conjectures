## Worker report

Item: `lem-sfb-space-derived-etale-chart-calculus`, group Q148, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`.
The 14 recorded declarations jointly state the complete node. The primary attachment is
`AlgebraicGeometry.AlgebraicSpace.space_derived_etale_chart_calculus`; it states the
quasi-coherence-preservation clause. There are nine postponed named theorems and five
canonical helper definitions. No definition contains a sorry. Every theorem has the
source, blueprint owner and its relevant natural-language proof in its docstring.
No mathematical statement correction, disputed statement, dependency-interface repair,
or new DAG node is needed.

Hypotheses and clauses, checked against the node:

* Base scheme: `S : Scheme.{u}`. Spaces: `X Y Z T : AlgebraicSpace S`. Thus all maps
  are maps over the same S, in the existing full category of fppf sheaves.
* Structure sheaves, module categories and unbounded derived categories are the existing
  `SmallModules`, `DerivedModules`, `smallModuleEquivalence`, `smallStructureSheaf`
  and `DerivedCategory`. These are the equivalent small ringed models of the original
  small étale module topoi, with the original section universe u. `HasDerivedCategory.{w}`
  binds the arbitrary chosen localization morphism universe. No category instance is chosen
  from a Nonempty witness and no alternative module category is introduced.
* D_QCoh is the existing `derivedQCohProperty`, testing every integer cohomology object
  after the inverse of the module equivalence against Mathlib's `IsQuasicoherent`.
* The functors Lu* and Ru* are exactly `spaceDerivedPullback` (the already fixed
  `derivedTensorPullback`) and `derivedDirectImage`. Their adjunction is the existing
  `spaceDerivedAdjunction`, rather than an arbitrary supplied adjunction.
  `spaceDerivedChart_resolution_computation` asserts invertibility of the existing
  left-derived counit on every flat-term K-flat representative, invertibility of the
  existing right-derived unit on every K-injective representative, and
  `SpaceDerivedAdjunctionNormalized` for that specified adjunction. K-flatness is the
  recorded `IsKFlatIndependentCoefficients`; K-injectivity is Mathlib's `IsKInjective`.
* Every arbitrary `f : X ⟶ Y` and `K : Y.DerivedModules` with
  `hK : Y.derivedQCohProperty K` is covered by `space_derived_etale_chart_calculus`.
  The conclusion is `X.derivedQCohProperty ((spaceDerivedPullback f).obj K)`.
* Étaleness, without surjectivity, is `IsEtale f.hom.hom`.
  `spaceEtaleTensorPullback_exact` asserts finite-limit and finite-colimit preservation
  for the existing transported tensor pullback. Its identification with actual slice
  restriction is the imported, scalar-normalized `moduleTensorPullback_etale_restriction`.
  `spaceEtaleDerivedRestriction` uses Mathlib's `mapDerivedCategory` of this exact functor;
  `spaceEtaleDerivedRestrictionFactors` is its actual termwise factorization.
  `spaceEtaleDerivedRestriction_existsUnique` identifies Lu* with this restriction,
  uniquely by equality with `spaceDerivedPullbackCounit` on EVERY cochain complex.
  Therefore the a* and b* of the source mean exact restriction, not an extra flatness
  assumption or an unrelated derived functor.
* The cartesian square is given invariantly by `f,g,h,f'` and
  `hp : IsPullback h f' f g`, with `hg : IsEtale g.hom.hom`. Here f=u, g=a,
  h=b and f'=u_V. Giving any pullback square includes the specified fibre product up
  to its unique canonical isomorphism; it does not assume the fibre product is a scheme.
* `spaceDerivedChart_etale_baseChange` first asserts `IsEtale h.hom.hom`, then
  gives the unique NATURAL isomorphism
  `derivedDirectImage f ⋙ spaceDerivedPullback g ≅
   spaceDerivedPullback h ⋙ derivedDirectImage f'`.
  Its equation on every `K : X.DerivedModules` identifies it with the mate under the
  specified f'-adjunction of the inverse pullback-square comparison followed by the
  pulled f-counit. This is precisely canonical a* Ru* K ≅ R(u_V)* b* K, including
  naturality in all module morphisms and normalization by the adjunctions.
* `spaceDerivedChartPullbackSquare` gives
  `spaceDerivedPullback f ⋙ spaceDerivedPullback h ≅
   spaceDerivedPullback g ⋙ spaceDerivedPullback f'` from the fixed composition
  comparisons and `sq : h ≫ f = f' ≫ g`. Its components on EVERY L are the second
  required isomorphism. On the étale square the exact-restriction identifications above
  give b* Lu* L ≅ Lu_V* a* L. The definition even covers equal noncartesian paths;
  it asserts no base-change invertibility for direct image in that extra generality.
* A family of schemes is `V : U → Over S`, indexed by arbitrary `U : Type i`.
  Its maps are `a : ∀ j, schemeSpace (V j) ⟶ X`, each étale by `ha` and jointly
  surjective by the existing `IsJointlySurjective` predicate in `hc`.
  `spaceDerivedChart_quasiCoherent_iff_cover` states the two-way test between
  `X.derivedQCohProperty K` and that predicate on every pullback along `a j`.
  These are the small étale modules of the chart schemes; Zariski restriction is not
  incorrectly used as an exact functor on all modules.
* The existing `spaceDerivedPullbackComp` and `spaceDerivedPullbackId` are the
  tensor-normalized composition and identity maps. `spaceDerivedChart_pullback_associativity`
  gives the actual three-map associativity equation, including transport along category
  associativity and the functor associator. `spaceDerivedChart_pullback_units` gives
  BOTH unit equations, with the category equality transports and functor unitors.
* `spaceDerivedChartDirectImageComp` is DEFINED by `conjugateIsoEquiv` for the fixed
  composite and single-map adjunctions, applied to the fixed pullback compositor.
  `spaceDerivedChartDirectImageId` is similarly the conjugate identity comparison.
  `spaceDerivedChart_composition_unit_counit` states BOTH componentwise unit and
  counit equations, for every A and B. Since conjugation preserves identities and
  reverses compositions, these comparisons also inherit associativity and unit laws.

Dependency declarations used (full namespace for space-specific names is
`AlgebraicGeometry.AlgebraicSpace`):

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `Modules`, `structureSheaf`, `pullback`, `etalePullback`, `etaleMap`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, used
  by both the original and small-model module categories.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, specializing
  the actual Mathlib `SheafOfModules.IsQuasicoherent` predicate used by derivedQCohProperty.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`,
  `moduleTensorSection`; the entire normalized model and adjunction signatures were read.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (acyclic-total-tensor predicate),
  with the real small-model commutative structure sheaf supplied as R.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `SmallModules` through its
  imported small ringed model, `DerivedModules`, `derivedQCohProperty`,
  `smallModuleDirectImage`, `derivedDirectImage`.
* `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback`,
  `spaceDerivedPullbackCounit`, `spaceDerivedPullbackComp`, `spaceDerivedPullbackId`.
* `Sheaf.AlgebraicGeometry.SpaceAffineHomComparison`: `spaceDerivedAdjunction`,
  `SpaceDerivedAdjunctionNormalized`, `spaceRightDerivedComplexUnit`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
* `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`:
  `moduleTensorPullback_etale_restriction`, `etale_module_pushforward_restriction`.
* Mathlib `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`,
  `conjugateIsoEquiv`, `Adjunction.comp`, `Adjunction.id`, and functor whiskerings.

The item's stmt_deps only gains five ALREADY LANDED definition nodes corresponding to
these shared derived interfaces and covering notation:
`def-sfb-space-derived-module-calculus`, `def-sfb-space-derived-pullback`,
`def-sfb-space-affine-hom-comparison`,
`def-trf-algebraic-space-jointly-surjective-family`, `def-trf-scheme-algebraic-space`.
Each has its existing usable Lean record. No dependency node is edited. All recorded
stated proof-dependency modules are imported without public; the unstated proof nodes
remain named in the complete proof docstrings and unchanged DAG proof. In particular the
scheme comparison argument is reproduced stepwise in the primary theorem's docstring.

Sources opened: local `literature/stacks-project/spaces-perfect.tex`, the discussion
before and the full statements/proofs of lemma-check-quasi-coherence-on-covering and
lemma-quasi-coherence-pullback (08F2, 08F4); local `sites-cohomology.tex`, full statements
and proofs of derived-pullback-composition, adjoint, derived-pushforward-composition,
and restrict-direct-image-open (0D6D, 07A6, 0D6E, 0D6G).

Edge cases checked before/during writing: empty spaces and empty étale charts; empty
covering family (its genuine joint-surjectivity hypothesis then forces the space empty);
zero complex; negative, zero and positive cohomological degrees; unbounded complexes;
identity arrows and three composable arrows; an étale map which is not surjective;
an arbitrary nonflat f; an algebraic-space fibre product which is not representable by
a scheme; every base characteristic; arbitrary family-index universe i. No properness,
qcqs, separation, flatness of f, or cohomological bound has been added. The small model
has site and coefficient universe u, obtained by the recorded affine-basis equivalence;
this does not force the original small-site object universe u+1 down to u.

Searches made through the prescribed msearch wrapper and direct read-only rg:

* LeanFinder: "Derived pullback and direct image of modules on algebraic spaces etale
  base change quasi coherent cohomology" returned Scheme.Modules.pullback,
  pullbackPushforwardAdjunction, pullbackComp and ordinary pseudofunctor/conjugation
  lemmas. These concern Zariski scheme modules, not this unbounded étale space calculus.
* LeanFinder: "derived module etale algebraic space chart base change" returned ring
  étaleness and scheme étaleness facts, no existing statement.
* LeanSearch: "exact functor left derived category" returned IsLeftDerivedFunctor,
  isLeftDerivedFunctor_of_inverts and derived-functor universal-property declarations.
  These justify the exact-restriction comparison but do not state this node.
* Loogle: "DerivedCategory, CategoryTheory.conjugateIsoEquiv" returned zero hits.
* Mathlib grep through msearch: "AlgebraicSpace|etale.*base.*change" in AlgebraicGeometry
  returned the three lines for étale scheme base-change stability, no space calculus.
* rg of project Sheaf algebraic-space modules found the canonical small model, derived
  modules, SpaceDerivedTensorPullback, SpaceDerivedPullback, SpaceAffineHomComparison,
  and the ordinary étale module restriction theorem. These are reused, not redefined.
* rg of WeilConjectures for the item id, AlgebraicSpace and spaceDerived found no exact
  declaration. rg of both project trees for the proposed helper and main names found no
  collisions. Scheme-only derived/ordinary results are insufficient for the entire node.

Validation: scompile.py compiled both sandbox and intended library module names cleanly
(25.2s and 17.7s on the successful run). The first attempts exposed unqualified Functor
whiskerings and a mistyped import, both repaired. The final delivery dry run below
recompiles the final file with the complete explicit dependency import list.

## Second reading by Q148

This is the worker's separate clause-by-clause second pass, not a claim of an independent
second agent: the dispatcher prohibits spawning agents, and the maintainer independently
reviews the delivery. I reopened the node and final module. The plain existential iso
risk is addressed by specifying the derived counit equation for exact restriction and
the mate equation for direct-image base change. The pullback-square iso is a real
composite of the already normalized comparators. The covering test uses arbitrary
families of actual schemeSpace objects and the existing joint-surjectivity predicate.
Both unit equations and both adjunction equations are present; composition of direct
images is the actual conjugate of the fixed pullback compositor. Every source clause
has its declaration above, and all source hypotheses are preserved. No node fault was
found. The listed five dependencies were added to reference the existing shared notions;
no duplicate notion, missing independent definition node or dependency repair remains.
