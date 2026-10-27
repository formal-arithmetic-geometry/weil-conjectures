## Worker report

The module `Sheaf.Paper.UnitKummerTwoSiteNormalization` states the complete
normalization of the ordinary degree-one Kummer class on the two small sites.
It defines the canonical coefficient arrows and their abelian cohomology maps.
All postponed proofs belong to this node and have source and proof docstrings.
The two lines are aliases of the already published root scalar extensions, not
new copies of the root sheaves, tensors, boundary, or frame class.

Hypothesis and clause correspondence:

- The universe is explicit: `Scheme.{u}`, roots and coefficients in `u + 1`.
  This retains the small sites' object universe `u + 1` and morphism universe `u`.
- The finite commutative ring is `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]`.
  The positive exponent is `m : ℕ`, `hm : 0 < m`; annihilation is `hA : (m : A) = 0`.
  In a unital ring this is precisely `m A = 0`.
- Invertibility on X is `hX : IsUnit (m : Γ(X, ⊤))`. Every scheme is allowed.
  The analogous hY on a pullback is redundant mathematical data: it is obtained
  by mapping hX along `v.appTop.hom`; it imposes no restriction on v or Y.
- Units and roots are the published `gmSheaf`, `rootsOfUnitySheaf`, and
  `proEtaleRootsOfUnitySheaf`. The ordinary short exact Kummer sequence and its
  boundary are `kummerSequence_shortExact` and `kummerδ₀`.
- The etale line `etaleLine` is the underlying abelian sheaf of
  `finiteEtaleTateLine X m A hA`. The pro-etale line `proLine` is the underlying
  abelian sheaf of `finiteRootProTensor A m hm hA X`. These are the existing
  sheafified balanced tensors, with A first in tensor notation.
- `Etale.ordinaryFiniteRootMap` is precisely the etale phi, sending z to 1 tensor z.
  `proInsertion_existsUnique` characterizes the analogous pro phi on every root
  section by `finiteRootProGenerator ... 1 z`; `proInsertion` is that unique map.
  Its construction is the scalar-extension adjunction unit followed by the
  sheafification unit. Thus this definition postpones only proofs, not unspecified data.
- `etaleClass` is H¹(phi_et) delta, verbatim. `proClass` is
  H¹(c_X then phi_pro) comp(delta), using `ProEtale.cartierRootsIso` for c_X and
  `ProEtale.comparisonCohomologyMap` for the canonical comparison.
- The first two additive-law conjuncts of `normalization` say exactly
  kappa(uw) = kappa(u) + kappa(w) on each site.
- `etalePullback` is the scalar-forgetting transport of the published
  `finiteEtaleTwistPullbackData.c ... 1`; its root identification is `.r`.
  `proPullback` is the underlying abelian adjunct of the normalized tensor map d
  in `finiteRootSiteComparison`. Invertibility is included explicitly.
- The ordinary Kummer-sequence conjuncts give both commuting squares for
  `(a,b,b)`, with b = `upperStarGmSheafToGmSheaf v`; b is never assumed invertible.
  The boundary conjunct says H¹(a) v* delta(u) = delta(v*u), where the actual unit
  pullback is `Units.map v.appTop.hom.toMonoidHom u`.
- The two geometric coefficient-square conjuncts compare pullback of phi with
  phi after the root map, on etale and pro-etale abelian sheaves respectively.
- The site coefficient-square conjunct says nu*(phi_et) then sigma = c then phi_pro.
  `comparisonForget` is the underlying-unit adjunction mate; `comparison` composes
  it with the normalized tensorComparison. Invertibility of this abelian arrow is stated.
- The subsequent two conjuncts are v* kappa_X = kappa_Y(v*u) on the two sites,
  using the canonical cohomology pullback and the above root-tensor identifications.
- `compareClass` is H¹(sigma) comp. The next conjunct maps kappa_et exactly to
  kappa_pro. As a composite of additive homomorphisms, it also intertwines addition.
- The last conjunct is the full geometric cohomology square for this coefficient
  comparison, for every degree-one class x, hence in particular for the unit classes.
- `frame_normalization` takes any `PurityFiniteSetting`, any k-scheme X, any unit u.
  The exponent is `P.diagonalExponent = ell^P.level`, not `P.exponent = ell^(n/e)`.
  It applies the underlying tensorComparison to the abelian realization of the
  actual `P.frameKummer X a u` and obtains `proClass` exactly. This is the
  projection-induced finite-root tensor presentation of the published frame twist.
  The equation is oriented from A(1) to the pro-root tensor; invertibility gives
  the node's equivalent opposite orientation. Every positive finite level is retained.
- There are no freeness, flatness, Cartier, nonempty, Noetherian, finite-type,
  or ramification-divisibility assumptions, and no tensor of G_m over Z/m.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `rootsOfUnitySheaf`,
  `kummerSequence`, `kummerSequence_shortExact`, `kummerδ₀`.
- `WeilConjectures.CategoryTheory.Sites.Torsor` and the Gm module it uses:
  `CategoryTheory.Sheaf.Torsor`, `AlgebraicGeometry.Scheme.gmSheaf`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  its retained `Sheaf.H` cohomology encoding, as used in the Kummer module.
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`:
  `Functor.exists_universal_rightDerived_deltaFunctor` (proof dependency).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`; the existing sheaf tensor convention.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparison`;
  coefficient functors `ProEtale.comparisonUpperStar`, `comparisonAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.cohomology`;
  degree-one classes here use the existing Ext-based `Sheaf.H` convention.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityInclusion`.
- `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison`: `finiteRootSiteComparison`,
  `FiniteRootSiteComparisonSpec`, `finiteRootProTensor`, `finiteRootProGenerator`;
  the imported canonical `ProEtale.cartierRootsIso`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `finiteEtaleTwistPullbackData`, including `.r` and `.c`.
- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Coefficient`,
  `constantEtale`, `constant`, `integerToConstant`, `moduleClassToAbelian_bijective`.
- `Sheaf.Paper.PurityFrameClass` and `Sheaf.Paper.PurityFrameKummer`:
  `frameClass`, `frameTwistEtale`, `frameTwist`, `frameKummerEtale`, `frameKummer`.
- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`:
  `comparisonConstantSheafIso`, `comparisonCohomologyMap`,
  `comparisonCohomologyMap_bijective`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `Etale.ordinaryFiniteRootMap`.
- `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`:
  `Etale.RawModuleScalarComparison.forget`, `pullbackIso`.
- The stated proof imports are the ordinary pullback long-exact ladder, degree-zero
  pullback, coefficient functoriality, and site-cohomology pullback modules.

The three additional stmt_deps are already landed definition owners of the root
insertion, concrete frame Kummer class, and scalar-forgetting comparison. No new
DAG node and no dependency repair or statement correction is needed.

Edge cases checked before writing: m=1 forces A=0 and both tensor lines vanish;
the empty scheme has trivial unit class and is included; u=1 and inverse units
agree with additive homomorphisms; arbitrary scheme maps need no G_m isomorphism;
a nonflat coefficient such as Z/2 over Z/4 is allowed; ramified finite levels
with e not dividing n use ell^n and are not excluded. No universe equality was added.

Searches run on 2026-10-23:

- `msearch.py leanfinder`: “Kummer boundary unit class additive natural pullback
  etale proetale tensor one arbitrary finite coefficient ring”. Eight hits,
  all standard etale algebra declarations, not this cohomology normalization.
- `msearch.py loogle`: `AlgebraicGeometry.Scheme.kummerδ₀, CategoryTheory.Sheaf.H.map`.
  Zero hits; the service also reported unknown upstream identifier kummerδ₀.
- `msearch.py grep`: `kummerδ₀|unitKummer|kummerClass`. Zero Mathlib hits.
- `msearch.py leansearch`: “Kummer boundary for units natural under scheme pullback”.
  Eight hits about S-units, valuations and restriction of roots, no match.
- `rg` in the live project's WeilConjectures and Sheaf directories for
  `unitKummer|kummerδ₀|unit-kummer-two-site`: found the ordinary boundary, curve
  specializations, PurityConventions at prime-power levels and the published
  frame construction. None states all exponents and both normalized site squares.
- Read the source of the ordinary scalar insertion and finiteRootSiteComparison;
  these are used directly rather than reproduced. Read Stacks 03PL in
  etale-cohomology.tex and the blueprint frame-independence proof's Unit multiples
  and Elementary shears paragraphs.

## Second reading by Q39

Self-check by the dispatched worker; the prompt forbids starting another agent.
The maintainer's independent mathematical review remains required. Reopened the
node and module and checked the bullet-by-bullet correspondence above. In
particular the ordinary Kummer boundary precedes all scalar extension, the two
geometric coefficient squares are sheaf equalities, b on G_m is a map rather
than an isomorphism, the final comparison square is for all degree-one classes,
and the frame specialization uses ell^n without e dividing n. No change to the
mathematical statement was made. The extra dependency IDs merely name already
published definitions used in these formulas.
