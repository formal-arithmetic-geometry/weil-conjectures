## Worker report

The module `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization` states
`lem-pur-supported-constant-exchange-normalization` in six theorem declarations, all with
`sorry`: `presentation`, `scheme_normalization`, `site_normalization`,
`sectionMap_existsUnique`, `compareSectionMap_existsUnique`, and `comparison_square`.
All names below are in `AlgebraicGeometry.SupportedConstantNormalization` unless qualified.
The main declaration is the two-square assertion; `lean.declarations` records every
supporting clause and every helper. The natural-language node, its dependencies and its
proof are unchanged. No statement correction, dependency repair or new DAG node is needed.

Sources read: Stacks `etale-cohomology.tex`, `lemma-shriek-base-change` (03S6) and
`lemma-ses-associated-to-open` (095L), including their proofs; the current blueprint
`main-20261015`, `sk-prop-a1-kummer/thm-pur-affine-line-orientation.proof.md`, geometric-fibre
and final etale-origin comparison paragraphs; the node's eight-step refinement and the
source/docstrings of its recorded dependencies. The requested CompactObject example module
has been withdrawn and now contains no declarations; its recorded existing upstream compact
object declaration was inspected, and the normal live module header/docstring convention is
used here.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Fixed finite coefficient datum A=A_(E,n) | Every assertion binds `P : WeilConjectures.PurityFiniteSetting.{u}` and uses exactly `P.Coefficient`, the existing ULift of `P.Ring=O_E/(varpi_E^n)`. The field, prime, finite extension and positive level are fields of this existing structure; no new ring or coefficient datum is supplied. |
| Schemes and arbitrary h | `Z Z' X X' : Scheme.{u}` and `h : X' ⟶ X`, with no finiteness, smoothness, properness, field-structure or quasi-compactness assumption on these schemes or h. The node explicitly allows arbitrary schemes; only its coefficient datum is used. |
| Closed immersions and their complement | `i : Z ⟶ X`, `i' : Z' ⟶ X'`, `[IsClosedImmersion i]`, `[IsClosedImmersion i']`; `i.openComplement.ι` and `i'.openComplement.ι` are their actual complementary opens. Their open-immersion instances are inherited. |
| Chosen Cartesian square and g | `sq : ChosenCartesianSquare g i' i h`, carrying the specified fibre-product isomorphism and both projection equations. This is the recorded square definition, not just a commutativity assumption. |
| Small sites, constant rings, ordinary modules | `Site false X=X.Etale`, `Site true X=X.ProEt`; `topology` selects the recorded topologies. `Modules A pro X` is `Sheaf (topology pro X) (ModuleCat.{u+1} A)`, the existing fixed-scalar presentation of modules over the constant ring. It retains site object universe u+1, morphism universe u, and coefficient/module universe u+1. The existing `sfIntrinsicModuleEquivalence` realizes this presentation in the recorded intrinsic ringed-site category; no alternate module notion is constructed. |
| A_T and P_(T,W)=i_*A_W | `constant` is `constantSheaf` of `ModuleCat.of A A`; `supported` is exactly `(push A pro i).obj (constant A pro Z)`. |
| Actual rho | `restriction false i` reuses `Etale.supportedConstantUnit`; its pro-etale branch is the recorded `Scheme.proEtaleConstantDirectImageMap`, extending the scalar-preserving constant-presheaf map by sheafification. |
| Actual epsilon | `epsilon` is the open-adjunction transpose of `unitIso.inv`, hence the counit after the canonical identification of the restricted coefficient with A_U. Both `openAdj` branches are the existing adjunctions with geometric inverse image. |
| L=h_et^-1 and h_proet^-1 | `pull A false h` and `pull A true h` are the existing `Etale.upperStar` and `ProEtale.upperStar`, with their actual `upperStarLowerStarAdjunction` stored by `adj`. |
| L=nu_X^-1 | `compare A X` is the recorded `ProEtale.comparisonUpperStar`. Its actual `comparisonAdjunction` is used to define `compareSigma`. |
| q and its version on the open/closed scheme | `unitIso` selects the published constant-sheaf pullback identifications; `compareUnit` is `ProEtale.comparisonUpperStarUnitIso`. They are actual scalar-preserving isomorphisms, not parameters. |
| Each L exact | The first two conjuncts of `scheme_normalization` and `site_normalization` state `PreservesFiniteLimits` and `PreservesFiniteColimits` for precisely the functors above. In the abelian module categories these give exactness. |
| rho is a cokernel on both sites | `presentation P pro i` gives `w : epsilon ≫ restriction = 0` and `Nonempty (IsColimit (CokernelCofork.ofπ restriction w))`, for both Boolean values and any closed pair. Source and target pairs are obtained by separate instantiation. |
| Canonical open comparison carries L epsilon to epsilon' | `openBackward` is the inverse-oriented canonical comparison: transpose `q_U.inv ≫ L_U(unit) ≫ square.inv`. The open part of `scheme_normalization` asserts its invertibility and `openBackward ≫ L(epsilon) ≫ q = epsilon'`. This is equivalent to the node's forward-isomorphism equation, with both constant identifications included. `compareOpenBackward` and the corresponding conjunct of `site_normalization` do the same for nu. |
| Complementary open base change | In `scheme_normalization`, the open assertion quantifies over `gU` and `sqU` identifying the two actual complements in the given geometric base change. These are in the conclusion, so they are not extra hypotheses restricting the closed exchange statement. Any such identification yields the same canonical comparison. |
| Actual canonical closed exchange | `exchange false sq` directly reuses `Etale.supportedConstantExchange`, hence the recorded `Etale.baseChangeMap`; the pro-etale branch is `adj i'.homEquiv (square.hom ≫ L_Z(counit) ≫ q_Z)`. `gamma` is the same adjunction mate using the inverse of the recorded site comparison on i. Neither is defined by choosing an arbitrary iso. |
| d invertible | `IsIso (exchange ... sq)` and `IsIso (gamma ... i)` in the two normalization statements. |
| d L rho = rho' q | Lean composes in diagrammatic order: `pull.map restriction ≫ exchange = unitIso.hom ≫ restriction`, and `compare.map restriction ≫ gamma = compareUnit.hom ≫ restriction`. |
| Uniquely characterized, actual exchange | The last conjunct of each normalization statement quantifies over every arrow d between the same endpoints, and asserts that the normalization equation implies equality to the concrete mate just defined. |
| lambda defined on every module sheaf | `sectionMap_existsUnique` and `compareSectionMap_existsUnique` give uniquely determined natural transformations between the existing `Sheaf.supportedSectionsFunctor` kernels. Their conditions say that composing with the target kernel inclusion is the source kernel inclusion followed by the actual unit section map (`sigma` or `compareSigma`). `sectionMap` and `compareSectionMap` choose these unique maps. This use of existence determines the data up to equality; no unspecified object or freely chosen transformation is introduced. |
| Same closed pair for nu | `compareSectionMap P i` uses `sections false i` and `sections true i`, both with exactly i and its complement. |
| Coherent k | `comparePullback A h` is definitionally the recorded `ProEtale.supportSiteComparisonCoefficientPullbackIso`, whose source defines it as the conjugate of the sectionwise-identical composite right adjoints. |
| Closed-exchange square | First conjunct of `comparison_square`: `N'.map c_e ≫ gamma' = k.hom.app P ≫ H_p.map gamma ≫ c_p`, exactly the node's displayed equation in Lean's order. |
| Supported-section square | Second conjunct of `comparison_square`, for every `M : Modules P.Coefficient false X`: `lambda_H ≫ lambda_N' ≫ sections.map(k_M) = lambda_N ≫ lambda_Hp`. Every intermediate target is the module inverse image displayed in the node. |
| No quasi-compactness or other finiteness | None of the six signatures introduces such assumptions; the open complements need not be quasi-compact. |

Dependency declarations used (their full signatures and docstrings were read):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `Ring`,
  `Coefficient`, and its existing commutative-ring structures.
- `Mathlib.AlgebraicGeometry.Scheme`, `.Morphisms.ClosedImmersion`, `.OpenImmersion`,
  `.Sites.Etale`, `.Sites.Proetale`: `Scheme`, `IsClosedImmersion`, `IsOpenImmersion`,
  `Scheme.smallEtaleTopology`, `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare` and `toCommSq`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`; size is the recorded
  metatheoretic convention and is expressed by the explicit universes.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is intrinsic
  `SheafOfModules`; its fixed-scalar realization is the existing
  `Scheme.sfIntrinsicModuleEquivalence` in
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`. The latter defines its
  `sfIntrinsicExtensionByZero` by transporting precisely the pro-etale `shriek` used here.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, and `Etale.upperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleSheafInverseImage`,
  `Scheme.proEtaleConstantDirectImageMap` and the recorded intrinsic
  `Scheme.proEtaleConstantModuleDirectImage`. The fixed-scalar `ProEtale.upperStar` and
  `lowerStar` used here are its underlying Kan/sheafification and precomposition
  constructions from the module it publicly imports.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` and
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`:
  `openImmersionLowerShriek` and `openImmersionLowerShriekUpperStarAdjunction` on each site.
  The intrinsic pro-etale adjunction is read in
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison` and
  its module specialization; their fixed-scalar functor and adjunction are
  `ProEtale.comparisonUpperStar`, `comparisonAdjunction` from the published source.
- `WeilConjectures.SixFunctors.BaseChange.Square`: `Etale.squareUpperStarIso` and
  `Etale.baseChangeMap`; the existing constant specialization is
  `Etale.supportedConstantExchange` in
  `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`, along with
  `Etale.supportedConstantUnit`. These convenience declarations are reused rather than
  copying their constructions.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `Sheaf.supportedSectionsFunctor`,
  `Etale.supportRestrictionArrow`, `ProEtale.supportRestrictionArrow`, and the published
  `supportSections` specializations. The etale statement here uses the same general kernel
  in modules, while the recorded etale `supportSections` specializes to abelian groups.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `ProEtale.supportSiteProEtaleComparisonSquare`,
  `supportSiteComparisonCoefficientPullbackIso`, and its adjunction/right-image data.
- Existing constant identifications: `Scheme.upperStarConstantSheafIso`,
  `ProEtale.constantSheafCompUpperStarIso` in
  `WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation`, and
  `ProEtale.comparisonUpperStarUnitIso` in
  `WeilConjectures.SixFunctors.ProEtale.Comparison`.

Every stated proof-dependency module is imported as required, without `public` unless its
interface also occurs in a signature or definition. In particular the intrinsic pro-etale
constant presentation, exact constant-module inverse image, ordinary open comparisons,
open unit normalization, localized ringed-site identity and the adjunction-mate lemmas
remain available to stage 3. No dependency interface was replaced or repaired.

Edge cases checked against the actual terms: Z empty (supported constant zero and full
open complement), Z=X (empty open and constant restriction identifies with the full
constant), h the identity, X' empty, nonreduced closed subschemes, disconnected schemes,
non-quasi-compact complements, zero module M, arbitrary rather than etale-origin pro-etale
M in `sectionMap_existsUnique`, and arbitrary module M for site comparison. Cokernel
uniqueness and monic support inclusions handle the zero cases. The coefficient level
n>=1 is retained in P. No independent universe is constrained to equal a different site
universe, and `autoImplicit` is disabled. The wrappers select existing constructions;
the actual mate and unit formulas, rather than unspecified map parameters, fix all maps.

Searches actually run through msearch.py:

- LeanFinder: "Canonical closed supported constant sheaf inverse image exchange normalized
  by constant restriction and commuting etale proetale comparison square". Eight hits,
  including `Scheme.restrictFunctorΓ`, `Scheme.restrictFunctorΓ_inv_app`,
  `SheafedSpace.IsOpenImmersion.invApp_app`, and locally constant/TopCat comparisons;
  none states the closed mate normalization or either square.
- Loogle: `CategoryTheory.Sheaf, CategoryTheory.IsIso`. Twelve sheafification,
  locally-bijective and sheaf-compose isomorphism hits; no matching assertion.
- Mathlib grep: `supportedConstantExchange|closedConstantExchange|supportSections`.
  Zero hits.
- LeanSearch: "Exact inverse image of the supported constant module has a unique closed
  exchange preserving constant restriction, commuting with etale proetale comparison and
  sections with support". Eight hits, including `StructureSheaf.res_const`,
  `ModuleCat.Tilde.res_const`, `Scheme.IdealSheafData.support_comap` and module restriction
  comparisons; none is the required theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for supported/constant/exchange terms:
  found and reused the canonical etale `supportedConstantUnit` and `supportedConstantExchange`,
  the pro-etale constant presentation, and the coherent inverse-image comparison.
  `SupportedCupFunctoriality.functorialCupExchange_existsUnique` only asserts a uniquely
  normalized isomorphism; it does not identify the prescribed mate or give these squares.
  `SupportedHomPullback` contains a derived transport interface for a different node and
  is a consumer of this item; it was read but is not imported or used. Grep of the item id
  in `lean/WeilConjectures` found no implementation. The new namespace was absent from
  the project and `dag/lean_names_upstream.json`.

Validation: scompile.py compiled this module in both its sandbox and real module names
against the published live build. The latest completed run had no errors and no warnings
(14.2 s sandbox, 25.7 s library). All six postponed proofs are named and mapped to this
node, and have source/proof docstrings. All definitions have real constructions; only the
uniquely determined kernel transformations use the node's postponed existence proofs.
No `STATEMENT-DISPUTED` issue was found. The required deliver2.py --no-push run passed
server compilation and maintainer preflight (dry-run commit 1b97875efa3).

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
