## Worker report

Module: `Sheaf.CategoryTheory.SubterminalDerivedImageCalculus`. Main declaration:
`CategoryTheory.SubterminalImageCalculus.subterminal_derived_image_calculus`.
The only postponed proof is this theorem. The two records and the composition
predicate package its conclusion; they introduce no extra input hypotheses.
All definitions have real data. Additive instances are componentwise constructors
with `map_add := rfl`; the sheafification instances apply Mathlib's existing
small-model transport. No new independent definition node is required.
The node statement and dependencies are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The site is `{C : Type u} [SmallCategory C]`, topology `J`, with exactly
  `[HasFiniteLimits C] [J.Subcanonical]`. There is no covering assumption.
  `R : Sheaf J CommRingCat.{max u r}` is the commutative ring sheaf.
  Coefficients and modules live in a universe containing the small site;
  the four localization morphism universes `w0,wU,wV,wW` are independent.
- `U V : C`, `hU : IsSubterminal U`, `hV : IsSubterminal V` are the two
  subterminals. W is literally `U ⨯ V`; its arrows are `prod.fst,prod.snd`.
  `ring R` only forgets commutativity. `modules R` and `sliceModules R Z`
  transparently use the recorded `ringedSiteModules` and ring restriction.
- The five existential `DerivedPair` witnesses `pU,pV,pW,pKU,pKV` use the
  actual Mathlib functors `overFunctor` and `overMap` for all restrictions.
  The right functors are `direct`, literally `pushforward (pushforwardOver Z)`,
  and `overPullback` for the two projection arrows. The first evaluates on
  `Z × C → Z` (Mathlib's product order); product symmetry identifies this
  canonically with the stated `C × Z → Z`. The scalar map is restriction
  `R.obj.map prod.snd.op : R(C) → R(Z × C)`. The second evaluates at the
  slice fibre product, with the same restricted scalar action. No unspecified
  ordinary direct-image functor or arbitrary scalar map replaces the source.
- `DerivedPair.resolutions_source` and `resolutions_target` assert, for every
  unbounded complex M, the existence of a quasi-isomorphism M → I with I
  K-injective. For these five pairs this covers all four module categories.
  `restrict_injective` and `direct_injective` assert preservation of
  `CochainComplex.IsKInjective` for every complex in every pair.
- `left,right` are derived functors and `adj` is their adjunction. `qF` is
  the natural factorization of exact restriction on ALL complexes and maps.
  `qG` is the natural comparison Q(GI) → RG(QI), and `qG_iso` asserts it is
  invertible for every K-injective I. This is the node's computation on
  K-injective representatives, for j and k alike.
- The `ordinary` arguments are precisely `overPushforwardOverAdj` and
  `overMapPushforwardAdj`. `DerivedPair.transpose` requires the derived
  Hom bijection at Q(M),Q(I), with I K-injective, to be Q of the ordinary
  chain-map transpose through qF and qG. This fixes counits and fixes units
  on K-injective M, since restriction also preserves K-injectives. A right
  adjoint to this specified exact derived restriction is the derived direct
  image, so the record does not substitute an unrelated derived functor.
- `cU,cV` compare j_W restriction with j_U then k_U and j_V then k_V.
  The two `CompositionNormalization` clauses are explicit predicates:
  for every complex, conjugation of c by the three qF comparisons is Q of
  `restrictionComp`. The latter is the termwise image of
  `overFunctorMap.symm`, with the explicit chain-functor composition iso.
  This fixes canonical iterated restriction on all complexes and cochain maps.
- The final `Nonempty (Comparisons ...)` asserts existence of all the
  comparison isomorphisms together with every normalization equation.
  `eU,eV` give the two self comparisons; `eW` gives the W self comparison
  needed in the final clause. `selfU,selfV,selfW` equate their hom
  transformations to exactly the three derived counits.
- `eUV : pV.right ⋙ pU.left ≅ pKV.left ⋙ pKU.right` is precisely
  j_U^* Rj_V* ≅ Rk_U* k_V^*. `eVU` is the symmetric clause.
  `crossUV,crossVU` fix their hom maps to the k-unit followed by the
  two iterated-restriction comparisons and the j-counit (the base-change mate).
- `eUW,eVW` give j_U^* Rj_W* ≅ Rk_U* and the V version.
  `toUW,toVW` fix these to the k-unit followed by the inverse iterated
  restriction comparison and the W-counit.
- `dU,dV` give Rj_U* Rk_U* ≅ Rj_W* and the V version; functor-composition
  order is `pKU.right ⋙ pU.right`. `compositeU,compositeV` fix their hom
  maps to the W-transpose of the two successive counits through cU or cV.
- These mate normalizations specify the sectionwise product comparisons:
  the underlying adjunctions are the actual product/graph adjunctions and
  `transpose` fixes their derived transposes on K-injective representatives.
  Hence no arbitrary isomorphism replaces the node's canonical comparison.
- `overlap adjU adjW cU A` defines r_A literally as the W-adjunction
  transpose of `cU.hom.app (Rj_U*A) ≫ k_U^*(epsilon_U,A)`. The V version
  is r_B, with no extra map supplied as data.
- `overlapUnitU` states r_A restricted to U, followed by eUW, equals the
  U counit followed by the k_U unit. `overlapUnitV` gives the k_V unit for r_B.
- `overlapCrossU` states r_B restricted to U, followed by eUW, equals eUV;
  `overlapCrossV` gives the symmetric identity for r_A on V. Thus after the
  two cross identifications each map is the identity on the common object.
- `overlapWU,overlapWV` compare r_A,r_B restricted to W with cU,cV followed
  by the restricted U,V counits, using the W self counit on their targets.
  These are exactly the two identities under self-restriction counits.
  A and B in these equations are arbitrary unbounded derived objects;
  all isomorphisms are natural, so arbitrary D on W is included as well.

Dependencies read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` (the abstract derived category node).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `overFunctor`, `overMap`, `overFunctorMap`, `overPullback`, `pushforwardOver`,
  `overPushforwardOverAdj`, `overMapPushforwardAdj`, all in `SheafOfModules`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; the resolution morphisms use `QuasiIso`.
- Proof imports retain the recorded
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
  (`SheafOfModules.localizedSystemExact`),
  `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation`
  (`CategoryTheory.slice_subtopos_site_presentation`),
  `Sheaf.CategoryTheory.KInjectiveTotalDerived`
  (`CategoryTheory.exists_rightDerived_of_enough_isKInjective`),
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
  (`SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`),
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
  (`CategoryTheory.Adjunction.preservesKInjectiveComplexes`), and
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
  (`CategoryTheory.Adjunction.mapHomotopyCategory` and `mapHomologicalComplex`).
  The two Mathlib proof matches are `Functor.mapDerivedCategoryFactors`
  from `DerivedCategory.ExactFunctor` and
  `CochainComplex.IsKInjective.Qh_map_bijective` from `DerivedCategory.KInjective`.

Sources inspected locally: Stacks sites.tex lemma-localize-given-products (03CE),
sites-cohomology.tex lemma-restrict-K-injective-to-open (08FI), derived.tex
lemma-derived-adjoint-functors (09T5), and cohomology.tex lemma-glue (08DG),
including its proof's direct-image restriction argument. The theorem docstring
contains the node's complete nine-step proof with its cited tools.

Edge cases checked: U=V=terminal reduces the maps to unit/counit identities;
U=V uses the canonical diagonal isomorphism. An object representing the empty
open, disjoint opens, a non-covering pair, and the zero ring are all allowed.
No nonzero, nonempty or boundedness hypothesis is imposed on complexes.
All coefficient sizes containing the small site and all four independent
chosen localization morphism universes are retained.

Searches for existing statements (prescribed msearch wrapper and read-only rg):

- LeanSearch: "Derived direct image for sheaves of modules on subterminal slice
  sites commutes with restriction to intersections" returned eight hits,
  including scheme restriction/restrictAdjunction and pushforwardSections;
  none states this full site/derived/map calculus.
- LeanFinder: "For localization of a ringed site at subterminal objects,
  derived direct image commutes with restriction to intersections" returned
  eight scheme restriction/global-section identities, no exact match.
- Loogle: "SheafOfModules.overFunctor, SheafOfModules.overMap" returned
  `SheafOfModules.overFunctorMap`, used for iterated restriction.
- Mathlib grep for "overPushforwardOverAdj|overMapPushforwardAdj|subterminal"
  in Algebra/Category/ModuleCat found both existing ordinary adjunctions and
  their isLeftAdjoint instances. These are used directly.
- rg for subterminal/Subterminal and localizedSystem in Sheaf and
  WeilConjectures found the binary-descent consumer and generic foundations.
  Binary descent assumes a cover and concludes gluing, so is not an exact match.
  Exact-name and blueprint-id searches in WeilConjectures, Sheaf, Mathlib,
  and dag/lean_names_upstream.json found no prior declaration of this statement.

Validation: the prescribed scompile wrapper confirmed the mathematical statement
cleanly against current server sources in 50.4 seconds, under the 60-second limit.
A local overlay attempt timed out, after which the wrapper's server confirmation
succeeded. The sandbox unexpectedly disappeared before packaging; its source,
node and report were recreated, and deliver2 is run again for fresh validation.
No launcher script or read-only library source was edited.

## Second reading by Q115

This is a separate self-reading; the dispatcher forbids starting another agent,
and the maintainer supplies the independent review. I reread the node together
with the complete Lean source. I checked that `pV.right ⋙ pU.left` starts on V
and ends on U, while its target is k_V^* then Rk_U*. The composite dU starts on
W and ends on the ambient derived category. All three self isomorphisms are
required to be the counits. Each of the six final fields matches its specified
unit or identity after the correct comparisons, including cU/cV on W.
The `DerivedPair` witnesses assert, rather than assume, K-injective resolutions
and both preservation clauses, and use the existing canonical ordinary functors.
No clause was removed and no mathematical statement change was needed.
