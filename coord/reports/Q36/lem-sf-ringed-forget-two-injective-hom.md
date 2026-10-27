## Worker report

The module `Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom` states the general
ringed-site comparison and its native Frobenius specialization. Nothing is proved:
`ringedRepresentatives`, `ringed_forget_two_injective_hom`, and
`native_two_injective_hom_model` have `sorry` proofs. The structures package the
clauses of this item; they do not select objects from these existence assertions.
`augmentation`, `underlyingHomBifunctor`, and `forgetKInjective` contain real data
or direct applications of existing declarations, with no postponed data.

Hypotheses and clauses, matched individually:

- The two sites have independent object/morphism/coefficient universes `c,v,r`
  and `d,vd,s`; their module universes are `max c v r` and `max d vd s`.
  `HasSheafify` and `WEqualsLocallyBijective` are the existing general-site
  interface for the abelian module categories. The two independent derived
  morphism universes are `wb` and `wa`, with explicit `HasDerivedCategory`.
  No equality of site, coefficient, or derived universes is imposed.
- The commutative coefficient sheaves are `R : Sheaf J CommRingCat` and `R'`.
  Their module categories are the dependency's `RingedTensorModules`, which
  transparently uses `ringedSiteModules` and Mathlib `SheafOfModules`.
- `U` has exactly these module-category endpoints. `U.Additive`,
  `PreservesFiniteLimits U`, and `PreservesFiniteColimits U` express additive
  exactness. The family `∀ A : Type (max c v r),
  PreservesLimitsOfShape (Discrete A) U` expresses all small products, including
  the empty product. It does not require preservation of arbitrary limits.
- `h` is an isomorphism of bifunctors, from `SheafOfModules.homFunctor` followed
  by `U` to that same recorded sheaf-Hom construction on `U` of both variables.
  Thus it specifies natural *internal sheaf* Hom comparisons. There is no
  substitution of global Hom groups or arbitrary maps between sheaves.
- `U.PreservesKInjectiveComplexes` is the stated K-injective-preservation
  hypothesis, using the existing class. `SB,TB,βB,_coherenceB` and the analogous
  target parameters give precisely the fixed closed adjunction, actual K-flat
  tensor comparison, signed symmetry and total-tensor coherence required in the
  first paragraph. These are the existing dependency structures, not copies.
- `Comparison.source` and `.target` are normalized representative systems for
  the actual `derivedInternalHomOfUniverses`. `Representatives.iso K I` computes
  it on every source complex and every K-injective target. In particular it
  computes it on the two K-injective representatives in the node. For arbitrary
  derived objects and specified representative isomorphisms, transport this iso
  by the recorded bifunctor's `mapIso`; no restriction to chosen representatives
  is made. `RingedRepresentatives.normalization` fixes this iso by the actual
  localization factorization `coefficientHomResolutionIso` and actual target
  augmentation, ruling out an unspecified automorphism of RHom.
- `Representatives.naturality` gives the simultaneous source/target square.
  Set its target map to identity and its source map to a resolution `t:K°→J`:
  its right arrow is exactly `Q(Hom(J,I)→Hom(K°,I))`, in the direction of the
  node. `Representatives.inverts` says this localized precomposition is
  invertible. With source identity it also covers target replacement. Both
  squares compose, and can be composed with inverse quasi-isomorphisms. The
  K-injective derived-Hom bijection makes these squares natural on derived
  arrows and independent of representative lifts, not only chain maps.
- `Comparison.derived` is the natural isomorphism χ on the product of the
  opposite source and ordinary target derived categories. It is an actual
  natural isomorphism, not objectwise `Nonempty`.
- `Comparison.chain` is its natural chain-level comparison.
  `Comparison.projection` fixes every degree-n, source-p product projection
  to `U.map (homComplexπ ...) ≫ h.hom.app ...`. Thus the comparison is the
  product-preservation comparison followed by the specified sheaf-Hom maps.
  The imported `homComplex_d_π` is the exact differential
  `d_I f - (-1)^n f d_J`; the product factors are the actual `homObj` sheaves.
- `Comparison.representative` identifies χ with localization of this specified
  chain comparison on every two-K-injective pair, with both actual
  `mapDerivedCategoryFactors` isomorphisms included. Together with naturality,
  this states replacement and inverted-quasi-isomorphism compatibility.
- The native specialization is in the *actual*
  `ProEtaleWeilSheaf k₀ l X = IsoAlgebra (WeilSheaf.frobeniusPullback ...)`,
  not fixed pairs in a derived category. `Field k₀`, `Finite k₀`, `Fact l.Prime`,
  `Fact (ringChar k₀ ≠ l)` and the three structure-morphism properties
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` give exactly the final
  specialization's field, prime, and separated finite-type scheme hypotheses.
  Its geometric fibre uses the native framework's fixed algebraic closure;
  its Frobenius is the geometric Galois Frobenius of that framework.
- `TwoInjectiveHomModel.coefficients` identifies the native locally finite-span
  continuous functions with functions locally valued in a finite intermediate
  extension. The functions themselves are unchanged, so pointwise addition,
  multiplication, and precomposition restrictions agree. This supplies the
  coefficient interpretation required by the node, not a new coefficient ring.
  The completed-coefficient comparison and finite-subextension coefficient
  dependencies are imported directly.
- `TwoInjectiveHomModel.source` is the product-total standard-sign model for
  the existing native `ihomBifunctor`. Its `π`, `product`, `differential`, and
  `map_projection` fields characterize precisely the complex transported from
  the twisted action site's sheaf-Hom model: products, their projections,
  the signed differential, and componentwise pre/postcomposition determine it
  up to its unique projection-preserving chain isomorphism. This description
  avoids choosing another presentation of the action site or another sheaf Hom.
  `.target` uses the existing `AdicSheaf.ihom`, via `underlyingHomBifunctor`.
- `.sign` starts at the native `CochainComplex.bifunctorHomObj` itself.
  `.sign_projection` is exactly multiplication by `(n*p).negOnePow` on its
  p-th projection in degree n. The imported `bifunctorHomObj_d_π` is exactly
  the row-sign differential `(-1)^p(d_I f^p - f^(p+1)d_J)`. The target
  `StandardModel.differential` has the standard cohomological sign.
  `.sign_naturality` includes both complex variables.
- All these native projections and isomorphisms are morphisms in the native
  fixed-pair category. Their equivariance is therefore part of their types.
  `ihom_obj_str` is the existing precise formula for the action
  `theta_I g_T^*(f) theta_J^(-1)` (with its comparison isomorphism); no extra
  arbitrary action is postulated.
- `.hom`, `.representatives`, `.native`, and `.native_normalization` identify
  this model with the existing `derivedHom`, including the actual chosen
  `kInjectiveRep` and `bifunctorRHomOfComplexObjIso`, not just an unrelated
  isomorphism of derived objects. `.underlyingHom` and
  `.underlyingRepresentatives` describe the corresponding internal derived Hom
  on native continuous-coefficient modules by this same representative property.
- `.chain`, `.chain_projection`, `.derived`, and `.derived_representative`
  give the native forgetting comparison, its specified underlying internal-Hom
  map `ihomFunctorCompForgetIso`, and its localization normalization.
  `DerivedCompatibility` simply writes the same representative square with a
  generic exact functor, to avoid repeatedly elaborating a large formula.
  `forgetKInjective` explicitly specializes the already existing exact
  orbit-induction criterion, shrinking the AB4 index universe to the countable
  product index. No K-injective-preservation assumption is added to the native
  specialization.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` (Mathlib's category).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory`; `...ExactFunctor`: `Functor.mapDerivedCategory` and
  `mapDerivedCategoryFactors`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homFunctor`, `homObjMap` and their local-map meaning.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; `...DerivedCategory.KInjective`:
  `IsKInjective.Qh_map_bijective` and `quasiIso_iff`.
- `WeilConjectures.Algebra.Homology.HomComplex` and `...HomComplexComponents`:
  `homComplexFunctor`, `homComplexπ`, `homComplex_d_π` and projection universality.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` reexports
  `derivedInternalHomOfUniverses`, its comparison and representative declarations.
  The ordinary-module abbreviation is not used on a sheaf category.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `CoefficientClosedStructure`, `CoefficientTensorModels`; its Hom representative
  dependency gives `coefficientHomResolution` and `coefficientHomResolutionIso`.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `RingedTensorModules`, `RingedDerivedTensorCoherence`;
  `...RingedDerivedTensorHomAdjunction`: the fixed native adjunction normalization.
- `Sheaf.CategoryTheory.TwistedActionRingedSite`: `presentation` and its
  `Presentation` data, including exact orbit induction and the contragredient Hom.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`:
  `PreservesKInjectiveComplexes`, `Adjunction.preservesKInjectiveComplexes`;
  `...IsoAlgebra`: the existing specialized orbit-induction criterion.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`; and
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `geometricFrobenius`.
  The native framework supplies their fixed-closure presentation directly.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `padicAlgClCondensedRing`; `Sheaf.Paper.CompletedCondensedCoefficients`:
  `completedCondensedAlgebraicClosure` and its finite-field colimit cocone.
- `WeilConjectures.WeilSheaf.LowerShriek`: the recorded native framework entry;
  `WeilConjectures.WeilSheaf.DerivedHom`: `ihomBifunctor`, `derivedHom`;
  its public imports supply `ihom_obj_str`, `ihomFunctorCompForgetIso`,
  `ProEtaleWeilSheaf`, `WeilSheaf.frobeniusPullback`, `AdicSheaf`, and
  `adicConstantSheaf` with its `locallyFiniteFunctions` section interpretation.
  `WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom` supplies
  `kInjectiveRep`, `kInjectiveRepIso`, `bifunctorRHomOfComplexObjIso`;
  `...Algebra.Homology.BifunctorHomComplex` supplies the native differential.
- The proof-only imports retain `QuasiIsoHomComplexMap`, its independent-universe
  extension, and `BifunctorHomHomotopyExact`, following the node's proof plan.

Edge cases checked: both site and module universes remain independent, as do the
chosen derived-category universes. The complexes are unbounded and indexed by all
integers. No boundedness, finite-rank, lissity, constructibility, nonzero coefficient
ring, or inhabited site is imposed. Empty products are included. Zero complexes
and zero maps are allowed. Negative n and p use `Int.negOnePow`, not natural-number
powers. In characteristic two all signs become the identity. At p=0 or n=0 the
sign normalization is the identity, and the n=0,p=1 test distinguishes the native
and standard differentials, as the accepted split requires. The native coefficient
condition is vacuous on an empty underlying space and otherwise uses genuine
neighbourhoods, not arbitrary subsets. Source resolutions need no K-flatness.

Searches (all through the prescribed Q36/item wrappers or the named source trees):

- LeanFinder: "An exact functor preserving products and internal sheaf Hom
  preserves derived internal Hom using K injective resolutions". Eight hits,
  mostly `mapDerivedCategoryFactors` and exact-functor Ext maps; none states this
  normalized internal-Hom and native sign comparison.
- Loogle: `SheafOfModules.homObj, Functor.mapDerivedCategory`. Zero hits;
  service reports `SheafOfModules.homObj` unknown. Direct source inspection
  found the upstream internal-sheaf-Hom API and uses it.
- LeanSearch: "Derived internal sheaf Hom commutes with an exact functor
  preserving products and sheaf Hom using K injective representatives".
  Eight hits including `sheafHom`, prestack Hom and injective-resolution
  comparisons, none this unbounded internal product-total statement.
- Mathlib grep wrapper: `PreservesKInjectiveComplexes|bifunctorRHom|homComplex`
  in `Algebra/Homology`. Twenty-five hits, on ordinary Hom complexes and exact
  functors; no matching theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for two-injective forgetting,
  `homComplex.*(forget|comparison)`, `forget.*HomComplex`, and the proposed
  declaration names. Existing `HomComplexInternalHomComparison` has the exact
  sign conversion for ordinary module sheaves with equal site universes, but
  does not accept the native module-object fixed-pair category or supply this
  two-site normalized forgetting theorem. `DerivedHomSingleResolution` covers
  a degree-zero source and bounded-below target, not this statement. Existing
  native `derivedHom` is the functor to be compared, not the comparison theorem.
- Literal item-id search in `WeilConjectures` and upstream name index found no
  existing declaration carrying the item. No new mathematical notion or repair
  of a dependency was needed. The source read is the current blueprint `latest`
  paragraph and local Stacks 0A95/08J7, together with the live native definitions.

## Second reading by Q36

Second pass by this dispatcher worker, with the JSON node and final Lean source
open; the brief forbids starting another agent. The maintainer's independent
review is still required and is not represented as completed here.

I checked each item paragraph against the declarations listed above. Corrections
made during the pass: changed the overly strong all-limits hypothesis to the
family of product-shape preservation instances; added the actual chosen
closed/K-flat/symmetric structures to the general theorem binders; normalized
both representative systems by the fixed localization factorization; added the
native coefficient interpretation and the native derived representative square.
The latter was factored verbatim into `DerivedCompatibility`; no equation was
removed. I checked the inverse direction on the source localization factor in
both representative squares, and the sign map starts at the native complex,
with exponent n*p as required. The native result assumes separated finite type,
while the general theorem has no scheme hypothesis. No statement correction,
dropped clause, new node, or dependency-node change is proposed.

Validation: the final source is compiled through `scompile.py`; delivery preflight
and its additional compile are run with `deliver2.py --no-push` before the push.
