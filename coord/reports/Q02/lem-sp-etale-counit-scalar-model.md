## Worker report

The delivery states `AlgebraicGeometry.Etale.etaleCounitScalarModel` in
`Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel`. Its only theorem has
proof `sorry`. Seven helper definitions give actual functors, chain maps and
comparison maps, assembled from recorded constructions. No data is postponed.
The DAG statement and proof are unchanged. The repaired dependency list now
explicitly includes the five definition owners requested by the maintainer.

Sources read: Stacks `sites-cohomology.tex`, `lemma-K-flat-resolution` (06YS),
`lemma-pullback-K-flat` (0G7E, especially its flat-term hypothesis), and
`lemma-derived-base-change` (06YY, including computation and independence);
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/`
`sk-lem-sp-reduction-exceptional.proof.md`, Charts, especially the integral
summation paragraph. The older snapshot named in the node was not used in place
of the current blueprint. The prescribed CompactObject example is now withdrawn
and contains no declarations; this module uses the current module/public-import
conventions of the recorded fold/scalar and scalar/pullback modules instead.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Field k, characteristic p > 0 | `k : Type u`, `[Field k]`, `[CharP k p]`, `_hp : 0 < p` |
| Prime ell different from p | `[Fact ell.Prime]`, `_hEll : p ≠ ell` |
| Finite commutative coefficient rings killed by powers of ell | `[CommRing A] [CommRing B] [Finite A] [Finite B]`, separate existential annihilator exponents `_hA`, `_hB` |
| Unital A to B | `φ : A →+* B`; no flatness or projective dimension binder |
| Separated finite-type k-schemes U,V | `Scheme.{u}`, `Over (Spec (.of k))`, locally finite type, quasi-compact and separated structure morphisms |
| Separated etale finite-type k-morphism e | `e : U ⟶ V`, `[e.IsOver ...]`, `[Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]` |
| Small ordinary etale sites and Q_R | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)`, `DerivedCategoryModule R T`, `_root_.DerivedCategory.Q` |
| K bounded constructible of finite Tor amplitude | `_hK : DerivedCategory.isBoundedConstructible A V K`, `_hKtor : ∃ a b, DerivedCategory.hasTorAmplitudeIn A V a b K` |
| The same condition on e_A^*K | `_heK`, `_heKtor` on the exact `upperStar ... .mapDerivedCategory.obj K` |
| Any representing cochain complex K_0 | `K₀` and `κ : Q.obj K₀ ≅ K`; this uses the specified representation, not an arbitrary unrelated identification |
| Quasi-isomorphism P to K_0 | `q : P ⟶ K₀`, `[QuasiIso q]` |
| P K-flat and termwise flat | `_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P`, `_hflat : ∀ i, ObjectProperty.flat (P.X i)` |
| Induced eta | `asIso (Q.map q) ≪≫ κ`; eta is not an independent unrelated binder |

Clause-by-clause correspondence:

1. The first four conjuncts assert K-flatness and flat terms of `e_A^*P` and
   `S_Ae_A^*P`. `etaleCounitScalarSource` is literally the composite degreewise
   inverse-image and sum functors. P is an arbitrary integer-indexed complex;
   no boundedness on its terms or chosen interval is imposed.
2. The existential `lam`, `τ` have exactly the displayed source and target
   derived objects. Their inverses are fixed by two equations. The source
   comparison `etaleCounitScalarSourceIso` is the inverse exact factor for sum
   followed by sum of the inverse exact factor for pullback. Thus
   `etaleCounitScalarSourceComputation φ e P η` is
   `T(E_Ae_A^*(η.inv)); T(exact-factor.inv); r_J`.
   The equation for `τ.inv` is `T(η.inv); r_P`. These fix precisely
   lam = `r_J.inv; T(exact factors); T(E_Ae_A^*η)` and
   tau = `r_P.inv; T(η)`. Invertibility is concluded, not assumed.
3. `etaleCounitScalarFirstChain` applies `NatTrans.mapHomologicalComplex` to
   `etaleScalarReassociatedFold φ e` with rho constructed inline by
   `Adjunction.leftAdjointUniq` for the two composite sum/scalar adjunctions. Reading that
   existing definition gives rho followed by sum of
   `(scalarSheafPullbackIso φ e).inv`, followed by the B-counit, with only the
   standard associators/unitors. It is exactly f_P, including its direction.
4. `etaleCounitScalarSecondChain` applies the same degreewise operation to
   `etaleScalarExtendedFold`: A-counit followed by ordinary scalar extension,
   exactly g_P. The two helpers are distinct definitions; this statement
   does not contain an equation asserting f_P = g_P.
5. The next conjunct is `Q.map f_P ≫ τ.hom = lam.hom ≫ Phi(K)`.
   `etaleCounitScalarFirstDerived` expands to `sumCoefficientIso.hom` at
   e_A^*K, sum of `properOpenCoefficientPullbackIso.inv` at K, and the B
   derived sum-adjunction counit at T_VK. The exact pullback comparison
   explicitly transports the recorded `scalarPullbackIso`, rather than
   introducing a free isomorphism.
6. The following conjunct is `Q.map g_P ≫ τ.hom = lam.hom ≫ T_V(v_A,K)`.
   The counit is the existing `derivedEtaleLowerShriekUpperStarAdjunction`.
7. The first quantified conjunct gives naturality of both actual chain maps
   for every chain map `h : P ⟶ P'`. It does not presume h is a quasi-isomorphism.
8. The next quantified conjunct gives naturality of lam and tau for a chain
   map h and derived map `ξ : K ⟶ K'` compatible with the representing eta's.
   Both new comparison isomorphisms must satisfy the same fixed inverse
   equations. Taking `h = 𝟙 P` covers transport of eta (including changing K).
9. The last quantified conjunct compares any other flat-term K-flat model
   P' of K with any representing eta'. It equates both conjugated chain
   maps, separately, with their counterparts for P. There is no required
   direct chain map between the resolutions. Existence of the normalized
   comparison isomorphisms for P' is obtained by the theorem itself with
   K₀ = P', q = identity, and κ = eta'. This is resolution independence.

Dependency declarations and their source modules read and used:

- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` reexports
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`, defined in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. This tests every
  degree-zero module sheaf; no perfectness or flatness of B is substituted.
- `def-pc-cochain-complex-modules`: Mathlib
  `Algebra.Homology.HomologicalComplex`, `CochainComplex`.
- `def-pc-quasi-iso-modules`: Mathlib `Algebra.Homology.QuasiIso`,
  `HomologicalComplex.QuasiIso`, exported as `QuasiIso`.
- `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
  exports the recorded `CategoryTheory.ObjectProperty.flat` interface for
  fixed-ring module-valued sheaves, from
  `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`. Symmetry
  identifies its two exactness tests; it is the existing flatness notion.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
  exports the recorded `CategoryTheory.MorphismProperty.kFlat` interface,
  from `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`.
  Specialization to quasi-isomorphisms is K-flatness, equivalently tensoring
  acyclic complexes remains acyclic. The intrinsic ring-sheaf-only predicates
  cannot take the fixed-ring `Sheaf ... (ModuleCat A)` input; no duplicate
  predicate or alternate coefficient category is introduced.
- `def-pur-etale-scalar-pullback-iso`:
  `Sheaf.Paper.PurEtaleScalarMateProjection`, `scalarPullbackIso`;
  `Sheaf.Paper.ProperOpenCoefficientRefinement`,
  `properOpenCoefficientPullbackIso`, reads it through the exact inverse-image
  comparison. This is a transport of the recorded comparison.
- `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, and Mathlib Q.
- `def-weil-pbc-etale-constructible-sheaf`:
  `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `Scheme.IsConstructibleEtaleModuleSheaf`, used through the existing
  `DerivedCategory.isBoundedConstructible` in
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`.
  It uses finite constant values on strata, not just a privately chosen
  constructibility predicate.
- `def-weil-pbc-etale-sum-extension`:
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`,
  `etaleLowerShriek`, `etaleLowerShriekUpperStarAdjunction`.
- `lem-amb-etale-adjoint-locality`:
  `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`, exports
  `derivedEtaleLowerShriekUpperStarAdjunction`; its exact functors give the
  existing `mapDerivedCategory` objects and counits.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, the recorded generic
  interface is imported; the actual small-etale representative is the existing
  `scalarExtensionRepresentative`, and `scalarExtension` is the existing
  abbreviation, both in `Sheaf.Paper.EtaleDerivedScalarTensor`, reexported
  by the recorded scalar/pullback module. Its underlying chosen adjoint is
  `ProEtale.pbcFixedScalarExtension`.
- `lem-sp-et-proet-coefficient-compatibility`:
  `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`,
  `AlgebraicGeometry.ProEtale.CoefficientCompatibility.sumCoefficientIso`.
- `lem-sp-etale-sheaf-fold-scalar`:
  `Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar`,
  `etaleScalarReassociatedFold`, `etaleScalarExtendedFold`,
  `etaleSheafSumFold`, `etaleSheafFoldScalar`. Its summandwise comparison
  is constructed inline by `leftAdjointUniq` on the two composite adjunctions,
  with right-adjoint comparison `upperStarRestrictScalarsIsoSheaf.symm`.
  The repaired module neither imports the section-normalization theorem module
  directly nor references its `etaleSumScalarIso` declaration.
- `sk-def-sfb-dc-setting`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`;
  the setting is spelled out as binders, without adding a compactification.

Proof-only dependencies are imported: `Sheaf.CategoryTheory.ExactDerivedAdjunction`
(`Adjunction.mapExactDerivedCategory`), `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat`
(`Scheme.etaleSum_preserves_flat_kflat`), Mathlib
`Algebra.Homology.DerivedCategory.ExactFunctor`
(`Functor.mapDerivedCategoryFactors`), `Sheaf.Paper.KFlatRingedToposPullback`
(`SheafOfModules.isKFlat_ringedToposPullback`), and
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
(`AlgebraicGeometry.etaleInverseImageModulesExact`). Their signatures and
source docstrings were read, including the independent site/coefficient
universes of the ringed pullback theorem.

Edge cases checked mathematically before writing:

- e = identity: the construction reduces to the two normalized scalar counits.
- Empty U: the common source is zero and all displayed equations are zero-map
  equations. Nothing assumes a nonempty geometric fibre or test scheme.
- A two-sheet disjoint union: f is extension of the two-summand fold, with no
  change of summand labels. This checks rho's direction and the inverse a^0.
- P = zero, unbounded P, and empty Tor intervals are permitted. No termwise
  boundedness was substituted for cohomological boundedness of K.
- A = Z/ell^2 and B = F_ell: B/A is nonflat and has no finite projective
  dimension in general; the only tensor computations are on K-flat sources.
- Distinct annihilator exponents are permitted by separate existential n's;
  zero coefficient rings and ell^0-annihilated rings are not excluded.
- eta need not be an identity. Its transport is built into both normalized
  inverse equations and the naturality/independence clauses.
- Site objects, morphisms, and coefficients use the existing ordinary small
  etale convention (scheme universe u, coefficient/module universe u+1).

Searches actually run with the prescribed wrapper:

- LeanFinder: `Compute derived etale sum extension scalar comparison and counit
  on a common flat term K flat resolution as chain maps`: 8 results, headed by
  `Algebra.FormallyEtale.of_restrictScalars`, no exact match.
- Loogle: `"KFlat", "counit"`: 0 results.
- Mathlib grep: `KFlat.*counit|counit.*KFlat|counitScalarModel`: 0 results.
- LeanSearch: `Derived change of rings exact etale sum counit common K flat
  complex representative computation`: 8 results, including module flat tensor
  exactness and ordinary etale algebra base change; none states this theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `counitScalarModel`, `counit_scalar_model`, `sumCoefficientIso`, and
  `sheafFoldScalar` found the existing sigma construction and the parent
  `EtaleSumCounitScalar`. The parent asserts equality of the derived
  composites, not their separate computations on arbitrary specified
  resolutions, so it is not an existing match. Follow-up searches for
  `KFlat.*counit|counit.*KFlat|etaleCounitScalar` only found unrelated affine
  computations and coefficient evaluation models. No source declaration
  carries this blueprint id.

No statement correction, new nodes, dependency record repairs, or disputed
mathematics were needed. The recorded flat/K-flat dependency interfaces already
include the fixed-ring versions needed here.

## Self-check

I reread the completed node and module as a separate self-check; the dispatch
brief prohibits starting another agent, and the maintainer performs the
independent review after delivery. This section does not claim an independent
second author; deliver2.py supplies the required direct-delivery review notice.

I checked all binders against the table above. The initial shorthand for finite
Tor amplitude used the general monoidal predicate; I replaced it by the
recorded `DerivedCategory.hasTorAmplitudeIn` with existential endpoints, so
its exact degree-zero sheaf test is visible. I checked the order of both
exact-localization factors in `etaleCounitScalarSourceIso`: Q(sum(pull(P)))
to E(Q(pull(P))) to E(pull(QP)), and hence the inverse equation for lam.
I checked `properOpenCoefficientPullbackIso` explicitly transports the named
`scalarPullbackIso`, and that its inverse gives the direction required for a_e.
The ordinary chain-map helpers invoke the fold dependency's actual maps;
no arbitrary rho is bound. The final two conjuncts were checked separately:
one is naturality/eta transport, the other compares unrelated resolutions
without silently requiring a chain map between them. The identities remain
separate and do not presuppose the sheaf fold equality they will later help
transport. Only the main theorem is postponed; every helper's body is concrete.

## Repair of returned head 5fdb9fcd200b

The maintainer's H2 return approved the mathematical statement and requested two
ownership repairs. Both are implemented, with no other mathematical change.

1. Added precisely these five already recorded base definition nodes to
   `stmt_deps`, with public imports of their recorded modules:

   - `def-weil-pbc-inverse-image`: `upperStar`,
     `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
   - `def-sf-etale-sheaf-scalar-extension`: `ProEtale.etaleSheafExtendScalars`
     and its adjunction, `WeilConjectures.SixFunctors.ProEtale.ScalarExtension`.
   - `def-weil-pbc-constructible-complexes`: `DerivedCategory.isBoundedConstructible`,
     `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`.
   - `def-sp-coefficient-scalar-representatives`: `scalarExtensionRepresentative`,
     publicly exported by `Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin`
     from `Sheaf.Paper.EtaleDerivedScalarTensor`.
   - `def-pur-open-coefficient-normalizations`: `properOpenCoefficientPullbackIso`,
     `Sheaf.Paper.ProperOpenCoefficientRefinement` (already directly imported).

   I read each node's statement, Lean record, and the actual declaration and
   docstring. Each is the precise definition used in the delivered formulas.
   The node's natural-language statement and proof are untouched; this adds
   the missing definition citations as explicitly requested, not a statement
   correction or dependency-module repair. No dependency node is changed.

2. In `etaleCounitScalarFirstChain`, replaced the reference to
   `(etaleSumScalarIso φ e).hom` by its exact `leftAdjointUniq` construction.
   The first adjunction is sum over A followed by scalar extension on V.
   The second is scalar extension on U followed by sum over B, transported
   along `upperStarRestrictScalarsIsoSheaf φ e` in its inverse direction.
   Their left-adjoint comparison goes from scalar extension of sum to sum
   of scalar extension, exactly the rho required by the fold/scalar node.
   Removed the direct import of `EtaleScalarSectionNormalization`. There is
   no new helper declaration, free map, theorem choice, or added theorem
   dependency. The existing `etaleSheafFoldScalar` proof constructs exactly
   this comparison, so its local formulas continue to characterize this rho.

Comparison with current main: the retained returned-head node and current-main
node differed only in `lean` before these repairs; the accepted statement, proof,
and original dependencies agree verbatim. The delivery wrapper refreshes the
current server base and rebases this repaired packet through its normal process.
The main theorem signature and all seven helper signatures remain unchanged.
The one postponed proof is still the original theorem's `sorry`; all helper
data remain explicit. The earlier edge-case checks continue to apply, since
the inlined rho is the identical adjunction comparison.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
