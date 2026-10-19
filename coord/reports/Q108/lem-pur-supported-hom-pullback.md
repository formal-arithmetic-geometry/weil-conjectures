## Worker report

Item: `lem-pur-supported-hom-pullback`, Q108, stage 2.
Module: `Sheaf.Paper.SupportedHomPullback`.
Main declaration: `AlgebraicGeometry.supportedHom_pullback`.

The module states the node without changing its natural statement or dependency list.
The main theorem has `sorry`; all helper definitions contain real data. There are no
additional postponed theorems. The helper structures package the canonical objects and
normalization equations belonging to this node; they do not introduce an independent
mathematical notion requiring a new definition node.

The source was read directly: Milne, Section 9, Example 9.5 on printed p. 66 and the Ext
proof of Theorem 9.4 on p. 67; the current blueprint affine-line orientation proof's final
etale-origin transport paragraph. Milne identifies Hom from the supported constant with
the restriction kernel by evaluation at 1. The node expands its pullback compatibility
and the analogous pro-etale construction; all nine proof steps are carried in the main
theorem's docstring.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node clause | Lean rendering |
| --- | --- |
| The finite datum of def-pur-conventions, A=A_{E,n} | `P : WeilConjectures.PurityFiniteSetting.{u}`, and `P.Coefficient`, the existing universe lift of `P.Ring`; no replacement coefficient ring. |
| Schemes X, X', Z, Z' and arbitrary h | `{Z X Z' X' : Scheme.{u}}`, `h : X' ⟶ X`. There are no finite-type, separation, compactness, characteristic or smoothness binders on these schemes or h. |
| Closed i and i' | `i : Z ⟶ X`, `[IsClosedImmersion i]`, and the corresponding primed binders. |
| The Cartesian closed pair with g | `g : Z' ⟶ Z`, `_sq : ChosenCartesianSquare g i' i h`. This retains the chosen pullback identification and its projection equations; it also covers a literal fibre product. |
| The actual complement | The pair constructors use `i.openComplement`, with `Etale.supportRestrictionArrow i` and `ProEtale.supportRestrictionArrow i`. |
| Bounded-below complex F of ordinary etale A-modules | `F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))`. This is the recorded ordinary-module encoding, with cohomological boundedness and without constructibility or finite-Tor conditions. |
| Every integer a | `a : ℤ`; no nonnegative-degree restriction. |
| H_Z^a(X,F) | `SupportHomPair.group`, defined by the existing `Sheaf.supportedSectionsFunctor`, `rightDerivedFunctorPlus`, and `DerivedCategory.Plus.homologyFunctor`. The etale coefficient specialization is the same kernel construction; the pro-etale specialization is the recorded `derivedSupportSections i P.Coefficient`. |
| The supported constant i_*A_Z | `etaleSupportHomPair.supported` uses `Etale.lowerStar` on `P.constantEtale Z`; the pro-etale pair uses `ProEtale.lowerStar` on the exact recorded `P.constant Z`. It is underived direct image, embedded by `DerivedCategory.singleFunctor ... 0`. |
| Canonical chi isomorphism | `SupportHomPair.Identification.chi` is an additive equivalence from the actual supported group to the specified derived Hom. `naturality` covers every derived coefficient map. `normalization` fixes it on every bounded-below injective representative and every Hom cocycle by evaluation of `constantRestriction ≫ f` at 1. `cycleClass` uses the existing canonical `supportSequenceModelIso`, and `cocycleMorphism` uses the published `Cocycle.fromSingleMk`, localization and cochain shift. Thus this is the canonical identification, with no scalar ambiguity. |
| Canonical h^{-1}, nu^{-1}, adjunction units | The three transport abbreviations fix `Etale.upperStar`, `ProEtale.upperStar`, and `ProEtale.comparisonUpperStar`, together with their exact recorded adjunctions and actual site functors. No arbitrary inverse-image functor is assumed. |
| Canonical g^{-1}A_Z=A_Z' | `Transport.constantIso_spec` fixes the coefficient comparison by its adjunct: `supportHomConstantDirectImage`, constructed by sheafification of constant scalar sections. It sends each scalar to the same scalar. |
| Canonical c:h^{-1}i_*A_Z ≅ i'_*A_Z' | `Transport.closedIso`, with `closedIso_spec`: `L.map rho ≫ c.hom = constantIso.hom ≫ rho'`. The source and target are exactly the two underived supported constants. The closed constant restriction is epic, so this equation uniquely determines c; the source proof identifies it with the adjoint closed exchange. The Cartesian arrow g is forced by the monomorphism i and the square; no extra choice of g is hidden. |
| Canonical pullback on supported groups from the localization sequence | `Transport.supportUnit_spec` fixes the map on kernels by kernel inclusion, the actual inverse-image adjunction unit at the final site object, and restriction along the terminal base-change arrow. The terminal and open site arrows are unique in these scheme-site cases. `Transport.derivedMap` applies the existing `rightDerivedFunctorPlusBaseChange` to this exact transformation. It therefore is the same derived kernel map used by localization functoriality, without requiring inverse image to preserve injectives. |
| chi'(h*alpha)=h^{-1}(chi(alpha)) composed with c^{-1} | `Transport.Compatible` quantifies over every `x : S.group F a`. Its left side is target chi of degree-a homology of `derivedMap`. `homMap` on the right first applies the degree-zero image of `closedIso.inv`, then `mapDerivedCategorySingleFunctor`, the actual exact derived inverse image of the morphism, and `commShiftIso a`. The first conjunct of the final four clauses is the etale equality. |
| Same equality on pro-etale sites for F_proet=nu_X^{-1}F | The second conjunct is `p.Compatible ... ((ProEtale.comparisonUpperStar ... X).mapDerivedCategoryPlus.obj F) a`. The coefficient is explicitly the image of the same F; the main assertion does not replace it by arbitrary descending data or assume a comparison isomorphism. |
| nu^* formula on X with gamma | The third conjunct is `v.Compatible (chiE i) (chiP i) F a`; `v.closedIso` is gamma, with its own constant-restriction normalization. |
| Likewise on X' | The fourth conjunct is `v'.Compatible` on the actual etale pulled-back object `h^{-1}F`. |
| Comparison commutes with h* | The first part of `SupportHomSquareCoherent` is the equality of the two derived supported-section maps, with target transported by `supportHomDerivedComparison`. The latter is obtained from the published inverse-image comparison and the canonical derived composition comparisons. Applying any homology functor gives the required square on groups. |
| Comparison commutes with c | The second part of `SupportHomSquareCoherent` is the explicit equation between `nu_X' c_et` followed by gamma_X', and the published pullback-comparison followed by `h_proet gamma_X` and c_proet. Its component is evaluated on the exact supported constant. |
| Etale equality is carried to the pro-etale equality | The four compatibility formulas, the two coherent squares, and naturality of target chi express precisely this transport with its coefficient comparison. Both formulas are stated together for the same F, a and square. |
| No finiteness or purity hypothesis | No such hypotheses occur. In particular no property of h other than being a scheme morphism is used as a binder. |

Canonical data are existentially introduced together with normalization equations. This
is deliberate: the dependency theorem `supported_cohomology_hom` records a `Nonempty`
natural isomorphism, not a named normalized chi. Selecting any such isomorphism would
leave the node's assertion ill-specified. Here every identification is fixed by its
value on all injective cocycles, every constant comparison by constant sections, every
closed exchange by epic constant restriction, and every kernel map by its inclusion.
No definition chooses data from an unnormalized existence theorem. This supplies the
normalization needed by this item, while using the dependency theorems in its proof plan.

The pro-etale convention `P.constant Z` is `nu_Z^{-1}(P.constantEtale Z)` rather than a
second constant-sheaf definition. The pair retains this exact recorded object. Its
constant restriction uses `ProEtale.comparisonUpperStarUnitIso` to identify that object
with the ordinary rank-one constant; hence it has exactly the required constant-1
normalization. There is no substituted coefficient sheaf.

Dependency declarations inspected and used (or imported as proof inputs):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, `.constantEtale`, `.constant` and their existing coefficient instances.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
- The recorded derived-category interface: ordinary `DerivedCategory` and
  `DerivedCategory.Plus` on `Sheaf ... (ModuleCat ...)`, as in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `Sheaf.supportedSectionsFunctor`,
  `Etale.supportRestrictionArrow`, `ProEtale.supportRestrictionArrow`, the module
  specialization of the recorded kernel and derived functors.
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `Etale.closedSupportHom`;
  `Sheaf.Paper.SupportedCohomologyHom`: `ProEtale.supported_cohomology_hom`.
- `Sheaf.AlgebraicGeometry.SupportLongExact`: `Sheaf.supportSequenceModelIso` and the
  adjunction-unit/kernel description in `SupportSequencePairNatural`; the node's
  `exists_support_longExact` is the localization-functoriality proof input.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: the original-site comparison
  adjunction (`Scheme.proEtaleSiteComparisonModules` specializes the same
  `ProEtale.comparisonAdjunction`).
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `ProEtale.supportSiteComparisonCoefficientPullbackIso`, with the actual base-change
  and comparison functors. Its recorded identity/composition/square coherence is retained.
- `WeilConjectures.SixFunctors.ProEtale.Comparison`:
  `ProEtale.comparisonUpperStarUnitIso`; the original small-site `ProEtale.upperStar`,
  `lowerStar` and adjunction come from the published `UpperLowerStar.Defs`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`:
  `Functor.rightDerivedFunctorPlusBaseChange`; Mathlib exact derived functors and
  the source's bounded-below restriction supply all single, shift and composition
  comparisons. `Sheaf.CategoryTheory.Abelian.RHomDerivedRoof` supplies the canonical
  roof/cocycle proof input.

All stated proof dependencies are imported as proof inputs. The only unstated proof
dependency, `lem-pur-proetale-supported-constant-presentation`, has no module to import;
it remains a named DAG prerequisite in the unchanged proof plan. No dependency module
is delivered and no dependency's record is changed.

Edge cases checked before writing: empty closed subscheme (zero supported constant and
zero kernel), full support and empty complement (ordinary global cohomology), empty X
and X', zero coefficient object F, all negative a and a=0, the identity and arbitrary
nonfinite h, non-quasi-compact open complement, and coefficient level n=1. No branch or
binder excludes these. The source proof uses the constant presentation, not a general
pro-etale recollement assertion. The site object universe is u+1 and its morphism
universe is u throughout; no equality of these universes is imposed.

Searches made before introducing the interface:

- `msearch.py ... leansearch`: “The natural isomorphism between cohomology with support
  and derived morphisms from the supported constant sheaf commutes with inverse image
  and site comparison”. Eight hits: constant/sheaf-composition comparisons,
  pushforward-composition maps, sheaf Hom, and injective-resolution naturality. None
  states the supported-Hom pullback assertion.
- `msearch.py ... leanfinder`: “The canonical identification of supported cohomology
  with Hom from the constant sheaf supported on a closed subscheme commutes with
  pullback and etale proetale comparison”. Eight hits, chiefly structure-sheaf
  restriction and `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`;
  no supported derived identification.
- `msearch.py ... loogle`:
  `CategoryTheory.Abelian.Ext.mapExactFunctor, CategoryTheory.Functor.rightDerivedNatTrans`;
  zero hits.
- `msearch.py ... grep`: `support.*[Hh]om|[Hh]om.*[Ss]upport` under Mathlib CategoryTheory;
  only two unrelated projective/injective extension `isSupported` hits.
- `rg` over the named upstream and side `lean/Sheaf` trees for supported Hom and support
  pullback: found and read `ClosedSupportHom`, `SupportedCohomologyHom`,
  `SupportedKummerSupportHomNaturality`, `SupportLongExact`, `SupportSiteComparison`,
  and `SupportComparisonPullbackCoherence`. The Kummer theorem only covers its etale
  cone models and does not give this ordinary derived Hom/group assertion with the
  pro-etale and site-comparison clauses. The support site-comparison module does not
  identify supported groups with Hom and therefore is not the present statement.
- `rg` for the exact item id in upstream: no match. Name search in
  `dag/lean_names_upstream.json`, upstream and side sources for the new declaration
  and helper names: no existing declarations.

No statement fault or `STATEMENT-DISPUTED` finding was identified. The existing
non-normalized identification records do not by themselves specify chi; this delivery
provides the source's injective-cocycle normalization explicitly rather than silently
choosing an arbitrary isomorphism.

Validation: compile every delivered Lean file through the prescribed `scompile.py`,
then the prescribed `deliver2.py --no-push` preflight and compile. Compiler findings are
repaired before delivery; final results are recorded below.

## Second reading by Q108

Author's second pass, not an independent agent review: the dispatcher explicitly
requires this worker to deliver itself and prohibits starting another agent. The
maintainer performs the independent review. Continuity arguments are supplied explicitly by the existing site-continuity
witnesses, avoiding inference through packaged site projections. The pair abbreviations
expose the same existing site data. These add no assertion or hypothesis. The source and node were reread alongside
the full signature. Checked that all four equalities are present; pro-etale coefficients
are explicitly nu_X inverse image of F; the primed comparison uses h inverse image of
that same F; the comparison of constants uses the inverse of c in the Hom map; shifts
use the exact functor's published comparison; and both commuting squares use the
published comparison of composite inverse images. Checked that the object on the Hom
source is underived i_* of the recorded coefficient unit, placed in degree zero.

The second pass also checked the two independent site universes, negative degrees,
absence of finite-type hypotheses, naturality in all derived coefficient morphisms,
and normalization on every injective representative. The full statement contains no
let binders, local notation, local instance, unbound implicit variable, arbitrary-map
hypothesis or purity isomorphism. No natural-statement or DAG change was needed.

Final single-file validation: `scompile.py Q108 lem-pur-supported-hom-pullback`
passed both the sandbox and final library-module checks, with no errors or warnings.
The final file has exactly one `sorry`, on `AlgebraicGeometry.supportedHom_pullback`.

Delivery dry run: `deliver2.py Q108 lem-pur-supported-hom-pullback --no-push`
returned `OK (dry run)` at commit `8ea1c8e5f7`: preflight passed and the final module
compiled cleanly. Only the item's Lean record, its new module, and this report were staged.
