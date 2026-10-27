## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceConnectivePerfectSectionsAffine` states
`AlgebraicGeometry.AlgebraicSpace.space_connective_perfect_sections_affine`, with `sorry`
as its entire proof. It adds three data definitions belonging to this statement:
`connectiveSectionsH0` abbreviates the existing zeroth hypercohomology;
`connectiveSectionsOne` constructs the class of the identity of the structure module
using the universal right-derived unit; `connectiveSectionsClass` applies H⁰ RΓ to a
map O[0] → E and evaluates it on that class. There is no new perfectness, derived
pullback, affine, cohomology, or module-category definition, and no definition data
is postponed.

Source read: `literature/stacks-project/quot.tex`,
`lemma-cohomology-perfect-complex`, Tag 08JX, both numbered clauses and the proof.
Clause (2) is specialized to a perfect K, exactly as the accepted node requests.
The unit is `sk-thm-sf-ctf-stability`; this is an auxiliary statement, not that unit's
own statement. No statement correction is needed.

Hypotheses and clauses, in the order of the node:

- Universes: explicit `universe u w`, `S : Scheme.{u}`. The binder
  `[∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]` chooses the common
  localization size for all tests; it is the metatheoretic size convention, not a
  geometric restriction. The equivalent small affine étale model has object and
  morphism universe u and the original u-sized section modules. It avoids imposing
  equality of universes on the original large chart category.
- Algebraic spaces over S and their small étale structure sheaves:
  `B : AlgebraicSpace S`, its `smallStructureSheaf`, and `B.SmallModules` use the
  recorded restriction equivalence of the existing small ringed model. No different
  structure sheaf or replacement module category is chosen.
- Unbounded derived object: `K : B.DerivedModules` is the existing
  `DerivedCategory B.SmallModules`, not a bounded derived subcategory or D(QCoh).
- Perfectness: `hperfect` is exactly
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}` on
  `B.smallStructureSheaf`. It quantifies over local bounded complexes of retracts
  of finite free sheaves, with local ranks and bounds; it is not global finite
  freeness, global boundedness, or a projectivity assumption on all modules.
- Every scheme test: `(T : Over S) (g : schemeSpace T ⟶ B)` ranges over all S-schemes
  with every map to B. Yoneda makes these exactly the node's scheme morphisms T → B.
  T is never required affine, étale, quasi-compact, separated, or nonempty.
- Universal absence of negative cohomology: `hconnective` quantifies over all those
  tests and `(i : ℤ)` with `i < 0`; the conclusion is `IsZero` of the existing
  `DerivedCategory.homologyFunctor` applied to `(spaceDerivedPullback g).obj K`.
  These are the actual cohomology sheaves, not cohomology of global sections.
- K-flat derived pullback: `spaceDerivedPullback` abbreviates the recorded canonical
  total left derived tensor pullback. Its shared counit is computed on flat-term
  K-flat representatives. No freely chosen functor or comparison is a hypothesis.
- H⁰(T,Lg*K): the equivalence target is literally the underlying set of
  `(connectiveSectionsH0 (schemeSpace T)).obj ((spaceDerivedPullback g).obj K)`.
  `connectiveSectionsH0` is the recorded H⁰ RΓ, computed by K-injectives. It is not
  silently replaced by sections of H⁰ or by the unproved local free model.
- Representing space and actual map: `∃ (V : AlgebraicSpace S) (p : V ⟶ B)`;
  `e T g` is a bijection from `{k : schemeSpace T ⟶ V // k ≫ p = g}` onto the
  specified hypercohomology set, for every test T and g.
- Naturality for every test arrow: for `(h : U ⟶ T)` and compatible points kT,kU,
  the final clause gives derived sections sT,sU whose classes are exactly the two
  images under e. Their square is
  `traceDerivedStructureMap (traceSchemeMap h) ≫ sU ≫
    (spaceDerivedPullbackComp g (traceSchemeMap h)).hom.app K =
    (spaceDerivedPullback (traceSchemeMap h)).map sT`.
  `traceSchemeMap h` is the actual Yoneda map. The structure pullback is the canonical
  map adjoint to regular-function pullback and the right-derived unit; the compositor
  is the canonical one fixed by the derived counits. For any E the usual derived
  section identification Hom(O[0],E) ≃ H⁰ RΓ(E) sends a map s to
  `connectiveSectionsClass X s`: apply Hom(O,-) to a K-injective representative;
  degree-zero cycles modulo boundaries are precisely these derived maps, and the
  identity section maps to the class constructed by the right-derived unit. Thus
  existence of sT,sU with this square is exactly the naturality of e under the
  canonical derived-pullback transition, not an arbitrary transition or an extra
  assumption. Pullback of O[0] is canonically O[0], so the square determines sU
  uniquely from sT. This expression avoids introducing another transition functor
  or postponing a helper theorem. It includes identity and composite test arrows.
- Affineness: `MapIsAffine p` is the existing predicate giving an affine representing
  scheme after every affine scheme base change, with its actual cartesian square.
- Finite presentation: the three conjuncts are `MapIsQuasiCompact p.hom.hom`,
  `MapIsQuasiCompact (pullback.diagonal p.hom.hom)`, and
  `MapIsLocallyOfFinitePresentation p`. These are respectively quasi-compactness,
  quasi-separatedness, and the universal étale-chart local finite-presentation test.
- No Noetherian hypothesis: none is present for S, B, V or any test; no uniform bound
  or fixed rank is introduced.

Dependency declarations read and used (public statement imports, directly or transitively):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its small étale site,
  structure sheaf, and `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `HomologySequence`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the existing
  `SheafOfModules.IsQuasicoherent` predicate. No extra QCoh hypothesis is imposed.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  `moduleDirectImage`, their specified adjunction and chart normalization.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`; `ProperCurveModuli`: `MapIsQuasiCompact`.
- Added landed definition owners in stmt_deps: `def-trf-scheme-algebraic-space`
  (`EnlargedEtaleRingedSite.schemeSpace`), `def-sfb-space-small-ringed-model`
  (`smallModuleEquivalence`), `def-sfb-space-derived-module-calculus`
  (`DerivedModules`, `derivedStructure`), `def-sfb-space-derived-pullback`
  (`spaceDerivedPullback`, `spaceDerivedPullbackComp`),
  `def-sfb-relative-dualizing-trace-pair` (`RelativeDualizingTracePair.traceSchemeMap`,
  `traceDerivedStructureMap`, both actually in namespace AlgebraicSpace), and
  `def-sfb-space-affine-quasifinite-properties` (`AlgebraicSpaceAffineQuasiFinite.MapIsAffine`).
  These are existing nodes with landed Lean records; no new nodes are needed.
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`:
  `singleFunctorCompHomologyFunctorIso`; this and the canonical complex/right-derived
  comparisons construct the class of one without any choice of an element.

Every currently stated proof-dependency module is imported as a private proof import,
including the Mathlib matches for affine-target morphisms, finite presentation,
Yoneda and separated-implies-quasi-separated. The as-yet-unstated proof nodes
`lem-sfb-ringed-site-connective-hypercohomology`,
`lem-sfb-space-connective-nonnegative-free-model`, `lem-sfb-space-fppf-qcoh-descent`,
and `lem-sfb-space-affine-locality` supply no module to import. They are proof
prerequisites only, not missing notions in this statement. The docstring carries
all six accepted proof steps, naming the relevant DAG dependencies.

Edge cases checked: K=0 gives the singleton-valued functor represented by B with its
identity; a finite free sheaf in degree zero gives the expected relative vector group;
a complex concentrated in positive degrees again gives singleton sections. Empty
T has a singleton section set, and the empty B has only empty tests. No nonempty
binder removes these cases. Ranks zero, absent degree one, and locally varying
finite bounds are allowed. A nonflat test is included in hconnective and in the
naturality square; no exactness of its ordinary tensor pullback is assumed.
The displayed naturality square has the correct orientation: both sides map
Lh*O_T[0] to Lh*Lg*K, using the compositor from L(hg)* to Lh*Lg*.

Searches actually run:

- `msearch.py ... leanfinder` query: "For a perfect complex on an algebraic space with
  universally vanishing negative cohomology, H0 of derived pullback is represented by
  an affine algebraic space of finite presentation". Eight hits: AffineSpace and
  affine transition/pullback facts; none states the result.
- `msearch.py ... loogle` query:
  `DerivedCategory, Functor.IsRepresentable, AlgebraicGeometry.IsAffineHom`.
  It returned zero hits with `unknown identifier 'Functor.IsRepresentable'`; this
  is a failed query, not evidence that representability notions are absent.
- `msearch.py ... grep` query `perfect.*represent|represent.*perfect|hypercohomology`
  in `AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` for the item id and `perfect.*sections|sections.*perfect`
  found only unrelated Poincaré duality finiteness and affine comparison lemmas.
- `rg` in `lean/Sheaf` for derived pullback, hypercohomology, perfection, structure maps,
  affine maps, and natural transformations found the canonical APIs listed above;
  they are reused. The exact four new declaration names were searched across
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`, with no hits.
- Read all ten initial statement-dependency node statements and Lean/mathlib records;
  opened their source declarations and the six additional definition owners.
  The compact-object example module is now withdrawn; its node binds the identical
  upstream module, and the delivery follows the required current module header.

Validation: `scompile.py NQ lem-sfb-space-connective-perfect-sections-affine` compiled
both the sandbox module and its actual library-module path cleanly (55.4s and 12.3s,
respectively) within the prescribed per-file limits. No warning remains. No statement
fault or STATEMENT-DISPUTED concern was found. The statement DAG additions were checked
for a path back to this item; each is acyclic.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
