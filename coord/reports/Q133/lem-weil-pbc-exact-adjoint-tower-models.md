## Worker report

The delivery states `CategoryTheory.ExactAdjointTowerModels.exists_models` in
`Sheaf.CategoryTheory.ExactAdjointTowerModels`. Its sole postponed theorem is
`exists_models`, with the entire twelve-step node proof in its docstring. No theorem
is proved. The node is unchanged except for `lean`.

The conclusion is `Nonempty (Models G)`. `Models`, `DerivedModel`, and
`NormalizedRoos` are transparent structures packaging exactly the choices and
assertions described below. They make no choices from an unproved existence theorem.
`tower` abbreviates the existing pointwise functor construction, and
`negativeCoordinates` constructs the existing shifted-cone coordinates. These are
helpers of this node, all recorded in `lean.declarations`, rather than independent
new mathematical notions. No new DAG node or dependency repair is needed.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Two small sites in one universe | `{C D : Type u}`, `[SmallCategory C]`, `[SmallCategory D]`, `τ`, `σ` |
| Sheaves of rings, including noncommutative rings | `R : Sheaf τ RingCat.{u}` and `S : Sheaf σ RingCat.{u}`; no commutativity instance |
| A=Mod(R), B=Mod(S) | The recorded `ringedSiteModules.{u} R` and `ringedSiteModules.{u} S` |
| Ordinary unbounded derived categories with chosen Q | The four `HasDerivedCategory.{w}` binders select the localization and morphism universe, as in the recorded derived-category interface; `DerivedCategory.Q` is used throughout |
| Additive F and G, F left adjoint to G | The two functor binders, `[F.Additive]`, `[G.Additive]`, and `adj : F ⊣ G` |
| F preserves short exact sequences | `hF : ∀ E : ShortComplex ..., E.ShortExact → (E.map F).ShortExact` |
| Strict towers and levelwise G | `ℕᵒᵖ ⥤ A` and `tower G`, the latter using `Functor.whiskeringRight` then `mapHomologicalComplex (.up ℤ)` |
| Integers in all complex degrees, with no boundedness condition | Every complex is `CochainComplex ... ℤ` |
| K-injective means maps from acyclic complexes are null-homotopic | Existing `CochainComplex.IsKInjective`, whose defining field is precisely this condition |
| Universal total right derived functors, computed on K-injectives | The four `DerivedModel` fields of `Models`; each model has its functor, unit, `IsRightDerivedFunctor` universal property, and `on_injectives` |
| Every X has q:X→I, a quasi-isomorphism to a K-injective with injective degree terms | `Models.resolution`, quantified over every X |
| Every such choice has J=G^Tow I, K-injective and degreewise injective | The first two conjuncts of `Models.kInjective`, for every K-injective, degreewise-injective I; J is the explicit expression `(tower G).obj I` |
| Each I_n and GI_n is K-injective | The next conjunct of `kInjective`, quantified over `n : ℕ` |
| L_I, L_J, P_I, P_J, G(L_I), G(P_I) are K-injective | The remaining six conjuncts of `kInjective`; L is `limit I.asFunctor`, P is the recorded `roosP I` |
| QJ computes R(G^Tow)(QX), by the unit and q | First existential isomorphism of `computes`; its hom followed by R(G^Tow)(Qq) equals the tower unit at I |
| Q(L_I) computes Rlim_A(QX), by the unit and q | Second isomorphism of `computes`, with the corresponding unit equation |
| Q(L_J) computes Rlim_B(R(G^Tow)(QX)) | Third isomorphism of `computes`; its equation uses the target-limit unit and the image of the tower unit, and transports back along Rlim_B(R(G^Tow)(Qq)) |
| Q(G(L_I)) computes RG(Rlim_A(QX)) | Fourth isomorphism of `computes`; the equation is the composite of the G unit and RG of the source-limit unit, transported back along RG(Rlim_A(Qq)) |
| Products QP_I and QP_J represent countable derived products | `Models.products`: the actual fans with the Q-images of their actual projections are limiting, using `Nonempty (IsLimit (Q.mapCone ...))` |
| c:G(P_X)≅P_(G^Tow X), for every tower complex | The natural isomorphism `Models.c`, with no K-injective restriction |
| beta:G(L_X)≅L_(G^Tow X), for every tower complex | The natural isomorphism `Models.beta`, with no K-injective restriction |
| c and beta characterized by their projections | `c_components` and `beta_components` give exactly c followed by pi_n = G(pi_n), and beta followed by lambda_n = G(lambda_n) |
| Q(c) is the derived product comparison with components RG(p_n) | `derived_product_components`, together with `products` and the invertibility of the units on P_I and I_n, gives precisely those components under the unit identifications |
| cG(s_I)=s_Jc | `shift_commutes`, using the recorded `towerProductShift`; Lean composition is written left to right |
| cG(1-s_I)=(1-s_J)c | `difference_commutes`, using recorded `roosU`, hence recorded `towerTransitionEndomorphism` |
| Naturality for strict tower chain maps | c and beta are natural isomorphisms of functors on the entire strict tower-complex category; every derived unit is a natural transformation |
| Naturality for localized morphisms between K-injective representatives | `localized_maps` supplies a chain representative of every localized morphism and independence of representatives for source products/limits and all four source/target comparison functors. Applying Q to the naturality equations of c and beta therefore gives well-defined naturality for every such localized morphism. The natural unit transformations and the equations in `computes` give the unit identifications' naturality |
| No exact-product assumption in these assertions | All preceding fields occur without an exactness premise; `HasExactLimitsOfShape (Discrete ℕ)` appears only as premises of `exact_products` |
| Exact countable products in both categories | The two premises of `Models.exact_products` |
| H_T=Cone(1-s_T)[-1], with the prescribed coordinates | Existing `roosF`, `roosχ`, and `roosU`, not a second cone construction |
| j_T is exactly (0,lambda), and is a quasi-isomorphism | Existing `roosι`; `NormalizedRoos.quasiIso` quantifies over K-injective, degreewise-injective T. The coordinate formula is already `roosι_χ` in the dependency |
| Negative-difference fibre and its sign isomorphism (y,x)↦(-y,x) | Existing `ExactProductsRoos.fibre`; `NormalizedRoos.sign` and `sign_coordinates`, with an actual constructed `negativeCoordinates` |
| The sign map carries the negative inclusion to j | `inclusion_sign`, including the canonical identification of the two ordinary-limit constructions |
| The normalized comparison supplied by the exact-products lemma | `NormalizedRoos.negative` and `negative_normalization` state exactly its natural comparison and unit equation |
| kappa_T is that comparison composed with the inverse sign map | `comparison_sign : comparison = isoWhiskerRight sign.symm Q ≪≫ negative` |
| kappa_T Q(j_T)=eta^lim_T | `normalization`: `Q.map (roosι X) ≫ comparison.hom.app X = L.unit.app X` |
| On K-injective T the unit identifies Q(L_T) with Rlim(QT) | `DerivedModel.on_injectives` for sourceLimit/targetLimit, applied to I and J; the latter's K-injectivity is in `kInjective` |
| Rotated cone triangle has maps r,1-s,b, with r(y,x)=x and b(z)=(z,0) | The recorded `roosProj`, `roosU`, and the third arrow of `CochainComplex.mappingCocone.triangle (roosU I)`, with the localization shift comparison; these are the actual canonical arrows, not existential free maps |
| Transport that triangle along Q(j_T) | `NormalizedRoos.triangle` chooses an isomorphism e whose hom is exactly Q(j_T), uses Q(j_T r) as its first arrow and b followed by the shifted e inverse as its last arrow |
| The resulting triangle is unit-normalized | `unit_triangle` transports instead to Rlim by kappa. Its first arrow is kappa inverse followed by Q(r), its last is Q(b) followed by the shifted kappa, and `normalization` fixes the identification with the ordinary-limit triangle by the actual unit |

The only interface subtlety was that `roosLimitFunctor` takes the limit in complexes,
while `ExactProductsRoos.ordinary` applies the ordinary limit in each degree. These
are canonically isomorphic but not definitionally equal: Mathlib chooses their
limit cones separately. `NormalizedRoos.ordinary` includes this isomorphism, and
`ordinary_components` fixes it by the actual degreewise limit projections. Both the
negative-fibre normalization and `inclusion_sign` include this transport. No arbitrary
comparison is substituted, and neither existing dependency is modified.

Dependency declarations read and used (the listed proof-only modules are imported
without `public`):

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, and its localization and shift structures.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `Functor.Additive`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
- `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`:
  `CategoryTheory.towerProductShift` and `towerTransitionEndomorphism`.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosP`, `roosPmap`, `roosU`,
  `roosχ`, `roosProj`, `roosι`, `roosInclusion`, `roosLimitFunctor`.
- `Sheaf.Algebra.Homology.ExactProductsRoosComparison`:
  `CategoryTheory.ExactProductsRoos.product`, `fibre`, `ordinary`, `comparison`,
  and `comparisonIso`.
- `Mathlib.CategoryTheory.Limits.Shapes.Products` and `.Countable`:
  `piObj`, `Pi.π`, `Pi.lift`, `Pi.map`, `HasCountableProducts`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`:
  `SheafOfModules.isGrothendieckAbelianOfUniverses`.
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`:
  `CategoryTheory.smallModuleDiagrams_isGrothendieckAbelian`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`:
  `CochainComplex.injective_kInjectiveResolutionFunctor_obj_X`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`: `Abelian.functorCategoryAbelian`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`:
  `Adjunction.preservesKInjectiveComplexes`.
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`:
  `Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits`.
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`:
  `CategoryTheory.tower_evaluation_isKInjective`.
- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`:
  `CochainComplex.termwise_product_isKInjective_and_isLimit`.
- `Mathlib.CategoryTheory.Adjunction.Limits`: `Adjunction.rightAdjoint_preservesLimits`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective` and `.quasiIso_iff`.
- `WeilConjectures.Algebra.Homology.RoosComplex`: `CategoryTheory.roosComplex_quasiIso`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and its imported triangulated
  structure; `CochainComplex.mappingCocone.triangle` supplies the actual rotated arrows.

Edge cases checked before writing: empty small sites and the resulting zero module
categories; the zero ring and zero complexes; identity and zero adjoint functors;
identity and zero tower transitions; all integer degrees including negative degrees;
and noncommutative coefficients. Zero transitions give u=1 and an acyclic cone, so
j from the zero limit has the correct behavior. Identity transitions give the usual
compatible diagonal inclusion, with the sign change fixing its zero first coordinate.
No boundedness, enough-points, commutativity, or exact-product hypothesis is silently
assumed. The indexing equivalence n↦n+1 covers precisely all positive tower levels.
The localization instances specify the chosen derived categories, rather than a new
mathematical restriction or an extra equality between site universes.

Searches for an existing complete statement:

- `msearch.py ... leanfinder`: query "An exact left adjoint and its right adjoint give
  simultaneous K injective tower inverse limit and product models with normalized Roos
  comparison". Eight hits: `Adjunction.hasExactLimitsOfShape`, a Nöbeling exactness
  lemma, adic-completion exactness, condensed and light-condensed AB4* facts, condensed
  solidification, and a Serre-quotient comparison. None states the simultaneous result.
- `msearch.py ... loogle "CategoryTheory.Adjunction, CochainComplex.IsKInjective"`:
  OK, zero hits.
- `msearch.py ... grep
  "preservesKInjectiveComplexes|isKInjective.*[Pp]roduct|[Pp]roduct.*isKInjective"`:
  OK, zero Mathlib hits. The project's separate exact-adjoint and product lemmas are
  present and used, rather than restated.
- `rg -n 'exact.adjoint|ExactAdjoint|tower.*[Mm]odel|[Mm]odel.*tower'
  lean/WeilConjectures lean/Sheaf`: found the separate exact-adjoint criterion,
  `TowerEvaluationKInjective`, the downstream direct-image normalization, and unrelated
  arithmetic tower models. No complete statement for this node exists.
- `grep -rn 'lem-weil-pbc-exact-adjoint-tower-models' lean/WeilConjectures`:
  no match. The newly chosen namespace and main declaration have no source match.

No `STATEMENT-DISPUTED` issue was found. No statement correction, additional node,
or dependency module is delivered. Every compile uses the prescribed `scompile.py`.
During elaboration repair, a diagnostic option caused an expected linter warning and
was removed; no diagnostic options or increased limits remain in the delivered file.

## Second reading by Q133

A separate rereading pass in this worker opened the node statement and the complete
module and checked the correspondence table above. No additional agent was started,
as the dispatcher explicitly prohibits it; the maintainer provides the independent
review of the delivery.

The pass verified all eight listed families of K-injective complexes, injectivity
of the degree terms of both I and J, all four unit-based computation isomorphisms,
the actual localized product fans, and the restriction of exact-product assumptions
to the last field. It checked the direction of every composition in the product and
limit projection equations and in the shift/difference equations. It checked that
naturality is an assertion for every strict tower complex, and that every localized
morphism between K-injectives has a representative with independence of its choice.

The sign comparison is explicitly from the negative-difference fibre to the positive
strict cone, with diagonal entries (-1,1) in (y,x) coordinates. The rereading retained
the canonical ordinary-limit transport introduced during compilation and checked
that it occurs in both needed normalization equations. It restricted the three
K-injective Roos assertions to degreewise-injective representatives, matching exactly
the I and J in the node. The triangle's first arrow, third arrow, and both transports
are fixed, including the localization shift comparison. The one sorry remains only
the whole proof of the named theorem and is accompanied by the node's complete proof
plan. All source-level variables and universes are explicitly bound.
