## Worker report

The module `Sheaf.SixFunctors.ComparisonOpenTensorCoherence` states
`AlgebraicGeometry.ProEtale.comparison_open_tensor_coherence` with `sorry`.
Its two definitions contain actual compositions of existing canonical natural
isomorphisms; neither chooses an unspecified arrow. The node statement, dependencies,
proof and proof dependencies are unchanged. No new nodes or dependency repairs are needed.

The source was read in `literature/stacks-project/sites-cohomology.tex`,
`lemma-j-shriek-and-tensor` (0GL1) and `lemma-pullback-tensor-product` (07A4),
in `sites-modules.tex`, `lemma-j-shriek-and-tensor` (0E8I), and in the current
blueprint's `sec-six-functors/sk-thm-sf-pf-proetale/thm-sf-pf-proetale.proof.md`.
The blueprint paragraph says comparison preserves tensor, pullback, compact support
and the projection maps. The node is its open-factor equality, not the entire
projection-formula theorem. The five proof steps are included in the theorem docstring.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Finite discrete commutative ring Λ | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. The fixed-ring `ModuleCat Λ` presentation uses only the discrete coefficient ring; no choice of a topology enters the functors. |
| Schemes and open immersion j : U → X | `{U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]`. |
| Small representatives in one larger universe | The existing `U.smallEtaleTopology` and `Scheme.ProEt.topology U` (and X versions) have objects in `u+1` and morphisms in `u`; coefficient modules have universe `u+1`, and the standard derived categories live in `u+2`. No equality of site object and morphism universes is imposed. |
| Ordinary unbounded derived categories of constant-Λ module sheaves | `Etale.DerivedCategoryModule Λ U` and `Etale.DerivedCategoryModule Λ X`; the pro-etale targets are `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u+1} Λ))`. This is the existing fixed-ring presentation of the same module sheaves, as explained below. |
| Arbitrary K and N | The two object binders have no boundedness, constructibility, support, or Tor condition. |
| Exact comparison A_T | `D(comparisonUpperStar (ModuleCat.{u+1} Λ) T)`, the localization of the degreewise exact inverse image. |
| Degreewise canonical extension comparison e_F | `.hom.app F` of `mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso (ModuleCat Λ) j`. Its definition is `mapDerivedCategoryCompIso.symm`, `mapDerivedCategoryNatIso` of the recorded `openImmersionLowerShriekComparisonUpperStarIso`, then `mapDerivedCategoryCompIso`. This is precisely the requested degreewise descent. |
| Tensor comparison t_T | `.hom.app G` of `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso (ModuleCat Λ) F`. This is the already published comparison of the strong monoidal inverse image, via `leftDerivedTensorComparison`, computed using K-flat representatives. It specializes the generic tensor-pullback interface; it is not an arbitrary tensor isomorphism. |
| Canonical a_j | `comparisonOpenDerivedPullbackIso Λ j`: localize the recorded `supportSiteComparisonCoefficientPullbackIso`, with canonical exact-to-left-derived comparisons before and after. Its direction is `L(j_e^*) ⋙ A_U ≅ A_X ⋙ L(j_p^*)`, so its component is `A_U(j_e^*N) ≅ j_p^*(A_XN)`. |
| h = (1 tensor a) composed with t_U | `comparisonOpenTensorIso Λ j K N` composes the component of the existing tensor comparison with `.mapIso ((comparisonOpenDerivedPullbackIso Λ j).app N)` under the functor `(derivedTensor ... U).obj (A_U.obj K)`. |
| Canonical gamma^e and gamma^p | The `.inv` components of the two published `derivedOpenImmersionLowerShriekProjectionIso`s. Their `.hom` goes from `j_!(K tensor Lj^*N)` to `j_!K tensor N`; the node requires the inverse direction. |
| Left composite | `A_X.map gamma_e ≫ e.hom.app (K tensor Lj_e^*N) ≫ D(j_!p).map h.hom`. Lean composition is diagrammatic, the reverse written order of the TeX function-composition notation. |
| Right composite | `t_X.hom.app N ≫ ((derivedTensor ... X).map e_K).app (A_X.obj N) ≫ gamma_p`. Mapping `e_K` by the curried tensor and evaluating at `A_X N` is exactly `e_K tensor 1`. |
| Common source and target | The compiler checks both sides from `A_X(j_!e K tensor N)` to `j_!p(A_U K tensor Lj_p^*(A_X N))`. The final `N` occurs after the entire canonical comparison pullback, not before it. |
| Naturally in K and N | This is an equality at every pair of arbitrary objects, of components of composites of the published bifunctorial natural transformations. Each helper is an explicit composition of natural isomorphisms and functorial `mapIso`; no independent component arrows are quantified over. |
| No boundedness, constructibility, properness or finite Tor amplitude | None is a binder. The helper that uses preservation of flat sheaves assumes only the same finite coefficient ring, which supplies the existing Noetherian coefficient instance. |

Dependency declarations read and used (full signatures and docstrings were inspected;
where the local source was absent, the published source was read with `scompile.py --source`):

| Dependency | Module and declaration |
| --- | --- |
| `def-weil-open-immersion` | `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`. |
| `def-weil-pbc-derived-categories` | `WeilConjectures.AlgebraicGeometry.DerivedCategories` and `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `AlgebraicGeometry.Etale.DerivedCategoryModule`; the former's recorded torsion predicate is not needed for this node. The category and coefficient module are publicly available through the dependency import closure. |
| `def-weil-pbc-proetale-modules` | `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`, `finiteCoefficientEtaleRealization`, `finiteCoefficientRealization`, `finiteCoefficientEtaleRealization_isEquivalence`, `finiteCoefficientRealization_isEquivalence_ring`, and `finiteCoefficientDerivedComparison`. The published exact realizations identify the fixed-ring sheaf encoding with modules over the constant/continuous-function ring sheaves. The open projection and extension-comparison dependencies already use precisely this fixed-ring encoding. There is no replacement coefficient category or second definition. |
| `lem-sf-comparison-pullback-exact` | `Sheaf.Paper.ComparisonPullbackExact`: `AlgebraicGeometry.comparisonPullbackExact`, establishing exactness of the same `comparisonUpperStar`. |
| `lem-cbc-proetale-extension-zero-comparison` | `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`: `openImmersionLowerShriekComparison_coherence` and the recorded canonical `openImmersionLowerShriekComparisonUpperStarIso`. Its existing degreewise localization is in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover`: `mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso`. |
| `lem-weil-pbc-extension-by-zero-exact` | `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: `Etale.preservesFiniteLimits_openImmersionLowerShriek`, with the additive and left-adjoint colimit instances for the same functor. |
| `lem-cbc-proetale-extension-zero` | `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`: `proEtale_extension_by_zero`, `openExtensionCochain`; the projection interface uses this same exact fixed-coefficient extension. |
| `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` | `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`, including its unique K-flat representative characterization. The specialized existing tensor comparison is `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso` in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal`. |
| `lem-weil-pbc-comparison-pullback` | `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: `supportSiteComparisonCoefficientPullbackIso`, whose right-adjoint comparison is identity on sections of the common chosen fibre products. The helper uses this recorded declaration directly. |
| `lem-pur-etale-open-derived-tensor` | `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`: `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`, inverse components. |
| `lem-cbc-extension-zero-projection-formula` | `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`: `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso`, inverse components. |
| Additional proof dependency `lem-sf-open-tensor-normalization` | `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`; imported for proof only. The unit/counit normalization fixes the canonical open maps used in proof steps 2 and 4. |

The existing `Etale.leftDerivedUpperStarIsoMapDerivedCategory` and
`ProEtale.leftDerivedUpperStarIsoMapDerivedCategory` are used only to align the
exact restriction convention with the published projection formula's `Lj^*`.
Their maps are the canonical left-derived-to-degreewise comparisons. The source
isomorphism of the pullback helper is passed with explicit functor arguments so
Lean searches for the published additive instances rather than for unreduced aliases.
This changes no mathematical data.

Edge cases checked before writing: the empty scheme and empty open, the identity
open immersion, zero ring, zero input complex, and complexes unbounded in either
direction. All existing operations accept them; there is no nonempty/nontrivial,
properness, boundedness or finite-amplitude binder. The equality uses the actual
section-normalized comparison for identity maps as well as arbitrary open
immersions. The scheme universe and coefficient universe retain the standard
successor relationship; no site smallness is forced by an added equality.

Searches for an existing statement:

- `msearch.py ... leansearch "The etale pro etale comparison commutes with the canonical tensor projection formula for extension by zero"`: eight results about scheme pullbacks, formally etale algebras and Kahler differentials; no sheaf projection-map coherence statement.
- `msearch.py ... leanfinder "Etale to pro etale comparison preserves the canonical derived tensor projection formula for open extension by zero"`: eight etale-algebra/differential results; no match.
- `msearch.py ... loogle '"comparison", "tensor"'`: five results, about sifted colimits and distributive monoidal categories; no match.
- `msearch.py ... grep 'comparison.*[Tt]ensor|[Tt]ensor.*[Cc]omparison' CategoryTheory`: thirteen hits about products, coproducts and monoidal closed functors; no etale/pro-etale open coherence.
- `rg` of the source project's `SixFunctors/ProEtale`, the framework under `lean/WeilConjectures/SixFunctors/ProEtale`, and `lean/Sheaf` for comparison/tensor and derived-comparison patterns: found the canonical `ComparisonMonoidal`, `OpenCover` and `LowerShriekComparison` ingredients used here. `LowerStarProjectionComparison` concerns `Rg_*`, and `ProjectionFormula` proves invertibility with bounded-constructible hypotheses, not the present equality for arbitrary objects.
- Search of the source project for the node id: no existing declaration of this item. Searches in Mathlib, the source project, `lean/Sheaf` and `dag/lean_names_upstream.json` for all three proposed declaration names: no collision.

Validation: `scompile.py NE lem-sf-comparison-open-tensor-coherence` compiled the
complete module in both sandbox and library contexts, cleanly (7.5 s and 8.0 s).
There is one postponed theorem, matching this DAG node, and two fully constructed
definitions. No statement is disputed and no node correction is needed.

## Second reading by NE

Author's second pass for the direct-delivery workflow; the maintainer supplies the
independent review. I reopened the node and the final module and checked every row
above against the actual binders and both composites. In particular, I checked the
three directions that could silently change the equality: both gamma maps use
`.inv`, the extension comparison uses `.hom`, and the restriction comparison goes
from `A_U Lj_e^*` to `Lj_p^* A_X`. The final curried tensor map is `e_K tensor 1`.
The pullback helper is the localization of the recorded section-normalized map,
with only the two canonical exact/left-derived identifications inserted. K and N
remain arbitrary, and the only ring hypotheses are commutativity and finiteness.
No missing mathematical hypothesis or conclusion clause was found. Compilation
repairs added the existing etale flatness instance import and made functor arguments
explicit; they did not alter the node or add a hypothesis.
