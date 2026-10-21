## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleLocalizedRingMateGraphEvaluation` states
`AlgebraicGeometry.Scheme.proEtaleLocalizedRingMateGraphEvaluation`. Its eight helper
definitions expand the mate, restricted ring isomorphism, graph, identity-object
identification, section map, integer-unit comparison, additive comparison and pulled
section map. All definitions have real data; the sole theorem has proof `sorry`.
No DAG statement or dependency record is changed.

Hypotheses and clauses, checked against the node and the source:

- A scheme B and a weakly etale site object u : V → B are `{B : Scheme.{u}}`
  and `(V : B.ProEt)`. This retains site object universe u+1 and Hom universe u;
  the sheaf values are in u+1. No finiteness, open immersion, monomorphism or
  coefficient finiteness hypothesis is present.
- R and S are arbitrary `Sheaf (ProEt.topology ...) CommRingCat.{u+1}`. The input
  `β` is an isomorphism from the specified `proEtaleSheafInverseImage` of R to S.
  That functor is the ring-object version of the same Kan/sheafification functor
  defining the recorded `AlgebraicGeometry.ProEtale.upperStar` on abelian sheaves.
- The inputs `c` and `cA` are the already recorded
  `ProEtaleObjectRestrictionComparison` in rings and abelian groups. They supply
  the stated restriction identification, with its distinguished coprojection
  and actual sheafification-unit equations. These are choices of identification
  already authorized in the node, not extra geometric hypotheses: the recorded
  restriction theorem supplies them, and the result holds for every such
  normalized comparison. No arbitrary unnormalized natural isomorphism is used.
- `bar β` is exactly `proEtaleLocalizedRingIso`: inverse of `c.sheafIso.app R`
  followed by β. Its sheaf and section maps are ring maps. Its restrictions
  are literal precomposition along `MorphismProperty.Over.map`.
- `e_u` is `(proEtaleSheafAdjunction V.hom CommRingCat).unit.app R`, not a unit
  chosen on an isomorphic left adjoint. `proEtaleLocalizedRingMate` is exactly
  that unit followed by the direct image of β.hom.
- The first conjunct quantifies over every site object T and every a ∈ R(T).
  It applies `c.sheafIso` to `e_u,T(a)` and equates this to R applied to the
  opposite of the counit of `Over.mapPullbackAdj`. That counit is the first
  product projection, hence this is exactly e_u,T(a) = R(pr_T)(a) under the
  stated restriction identification.
- The second conjunct gives η^β_T(a) = barβ_(T×_B V)(R(pr_T)(a)). The chosen
  base change has variable factor first and is viewed over V by its second
  projection, as in the node.
- The third conjunct quantifies over every U/V and every B-map b from its
  composite to T. `proEtaleLocalizationGraph` uses the actual site adjunction's
  Hom equivalence: it is the pair (b,U→V). The equality applies S to that graph
  and the mate to a, with right side barβ_U(R(b)(a)). No graph is supplied as
  an unconstrained parameter.
- The fourth conjunct specializes T=V, U=V/V and b to the identity of V.
  `proEtaleLocalizationIdentityIso` records the harmless identity-composition
  identification between the composite site object and V. Its graph is δ.
  The equality of ring morphisms identifies S(δ)η^β_V with barβ_(V/V), with the
  identity-object identification of the domain made explicit. The fifth conjunct
  asserts `IsIso` of that composite ring morphism. It does not assert that
  S(δ) alone is invertible. V/V is the terminal object by
  `MorphismProperty.Over.mkIdTerminal`, so its sections are Γ(V,S).
- The sixth conjunct fixes the integer unit by the equation that it followed
  by `proEtaleConstantInverseImageMap` is the identity. The helper is an
  isomorphism with real data: restriction/sheafification compatibility followed
  by the inverse normalized abelian comparison. Thus the equation specifies
  the inverse of the canonical constant-coefficient map. This is the canonical
  inverse-image monoidal unit, characterized on integer sections as in node
  proof Step 5 and Stacks 03EL; it is not an arbitrary monoidal-unit choice.
- The seventh conjunct quantifies over every r ∈ R(B/B). The map
  `proEtaleLocalizedSectionMap` is constructed by the constant-sheaf/evaluation
  adjunction from `uliftZMultiplesHom _ r`, hence is precisely the additive
  map from the integer sheaf sending 1 to r. This must be an additive map,
  since r need not equal the ring unit. `proEtaleLocalizedPulledSection`
  applies the actual abelian inverse image, compares its target with the
  additive sheaf of the ring inverse image through the normalized restriction
  comparisons, and composes with β. Its value at V/V on the sheafification of
  the constant integer 1 equals barβ_(V/V)(R(u)(r)). The terminal structure
  arrow in the displayed right side is precisely the composite U→V→B at U=V/V.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`, topology.
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` (canonical
  FiniteCoefficient re-export): `AlgebraicGeometry.ProEtale.upperStar`, the
  same sheafified Kan construction, and lowerStar/direct image.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`:
  `ProEtaleObjectRestrictionComparison`, including presheafIso, coprojection,
  sheafification_isIso, sheafIso, sheafIso_inv; the existence theorem
  `proEtaleObjectInverseImageRestriction` supplies normalized comparisons.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, over, Hom.over, overMap and overFunctorMap;
  `Mathlib.CategoryTheory.Sites.Over`: `Sheaf.over` and the localization topology.
  Their restriction is the same sectionwise restriction transported to the
  weakly etale object site by the dependency's recorded localization equivalence.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: proEtaleBaseChange,
  proEtaleSheafInverseImage, proEtaleSheafDirectImage, proEtaleSheafAdjunction,
  proEtaleConstantInverseImageMap. These retain the exact constructed adjunction.
- Proof dependencies: `Mathlib.CategoryTheory.Sites.ConstantSheaf.constantSheaf`
  and constantSheafAdj; `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`
  in `Mathlib.CategoryTheory.Sites.Pullback`; `CategoryTheory.siteInverseImage_tensor`
  in `Sheaf.CategoryTheory.SiteInverseImageTensor` for canonical unit normalization.
- Supporting existing constructions: `MorphismProperty.Over.mapPullbackAdj`,
  `Over.mkIdTerminal`, `Functor.pushforwardContinuousSheafificationCompatibility`,
  `uliftZMultiplesHom`. No second definition of these constructions was introduced.

Sources opened: Stacks sites.tex labels lemma-adjoints-u (00VE),
lemma-adjoint-sheaves (00WX), definition-localize (00Y0), and
lemma-localize-given-products (03CE); sites-modules.tex
lemma-tensor-product-pullback (03EL). The theorem docstring writes all five
node proof steps, including the cocone relation for the specified unit and the
constant integer normalization.

Edge cases: empty B, V or T; zero rings; arbitrary, nonconstant R and S; arbitrary
sections including r=0 and r≠1; the identity site morphism; and weakly etale u
which is not a monomorphism (e.g. a disjoint union over B). All are admitted.
The diagonal composite, rather than the diagonal restriction alone, is an
isomorphism. The ULift of integers permits every scheme universe without
restricting the site object or morphism universes.

Searches performed with the prescribed msearch.py wrapper:

- leanfinder: "localization inverse image unit restriction projection graph ring
  sheaf mate": eight hits, mainly StructureSheaf/LocallyRingedSpace localization
  formulas, none for the specified pro-etale Kan unit and arbitrary ring mate.
- loogle: `CategoryTheory.Sheaf.toPushforwardOverPullback`: two hits, the map
  and its component formula in Mathlib.CategoryTheory.Sites.Over. They construct
  the projection map but do not state its identification with this Kan unit,
  arbitrary ring-isomorphism mate, graph evaluation and integer normalization.
- grep: `toPushforwardOverPullback|overMapPushforwardAdj`, CategoryTheory/Sites:
  one hit, Sites/Over.lean. Read its map and component formula directly.
- leansearch: "sheaf inverse image localization adjunction unit projection
  restriction graph ring isomorphism": eight hits, including open-immersion
  Scheme.Modules.restrictAdjunction_unit_app_app and module pullback unit
  formulas, none the complete statement here.
- rg in the project Sheaf and upstream WeilConjectures sources, and the upstream
  name index, for the item id, localized mate names, graph evaluation, and
  pro-etale unit/constant-section names: no exact statement. Read nearby
  ProEtaleOpenUnitEvaluation, the inverse-image interface, and normalized object
  restriction source. The older CompactObject example is withdrawn; read its
  node's canonical upstream binding and followed current module/header style.

No STATEMENT-DISPUTED issue, source correction, new node, or dependency repair.

## Second reading by Q67

A separate self-review pass checked the node against the definitions and seven
conjuncts above. The maintainer supplies the independent review after delivery;
no other agent was started. In particular, the read-through checked the actual
Kan adjunction rather than an arbitrary unit, the direction of the normalized
restriction isomorphism, the graph and diagonal domains, all ring operations,
and the additive nature of the integer-to-R section map. It made the
identity-object isomorphism explicit and used the composite forgetful functor
CommRingCat → RingCat → AddCommGrpCat, rather than assuming a direct forget₂
instance. No mathematical clause or hypothesis was changed.

Validation: the prescribed scompile.py completed cleanly for the full delivered
module in both sandbox (19.0 s) and library (16.5 s) form, under the unchanged
60-second per-file limit. No warning remained. The only postponed proof is the
main theorem. The exact theorem signature is recorded verbatim in lean.statement;
all eight helpers are listed in lean.declarations. No global build or direct
repository mutation was performed.
