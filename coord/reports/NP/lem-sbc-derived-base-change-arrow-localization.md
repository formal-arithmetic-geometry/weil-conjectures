## Worker report

The delivery retains the saved packet's two-module layout and supplies the exact canonical
comparisons required by `lem-sbc-derived-base-change-arrow-localization`. The theorem
`AlgebraicGeometry.Etale.derivedBaseChangeArrow_localization` is stated with `sorry`.
There are no other postponed proofs and no data defined by `sorry`.

The first saved dry run compiled both modules and then reported four metadata errors:
missing `lean.existing` on the item, the helper's wrong `lean.module`, and the helper
structure incorrectly listed among the theorem module's declarations. These records are
repaired. Self-check also found a mathematical defect in the saved Lean: it quantified
arbitrary comparison isomorphisms. On an identity square, independently changing one
comparison by minus the identity changes the claimed equality. The final delivery
constructs the canonical maps and removes that hypothesis. This fixes the Lean rendering;
the original item's natural-language statement is unchanged.

Hypotheses and clauses, in order:

* The six schemes are `Scheme.{u}`. The global maps have exactly their specified domains
  and codomains. `sq : ChosenCartesianSquare h e f g` is the recorded chosen Cartesian
  square, including its projection equations.
* `a : U ⟶ X`, `b : B ⟶ S`, `[Etale a]`, `[Etale b]`, `fU : U ⟶ B`, and
  `fac : a ≫ f = fU ≫ b` render the two etale hypotheses and the factorization. No
  assumption is imposed on `f`, `g`, `fU`, or the schemes beyond the node's hypotheses.
* `pullback b g` is `T_B`, with `pullback.fst b g = g_B` and
  `pullback.snd b g = c`; `pullback a h` is `Y_U`, with `pullback.fst a h = h_U`
  and `pullback.snd a h = d`. The existing `BaseChangeLocalization.localArrow` and
  `localSquare` give exactly the canonical `e_U` and chosen local Cartesian square.
* Categories are `DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u+1})`.
  Thus K is arbitrary and unbounded, and coefficients are precisely abelian groups.
  The explicit universe follows the recorded small-site/size convention.
* `D((a)^*[AddCommGrpCat.{u+1}])` and the corresponding functor for `c` implement
  `r_U` and `r_{T_B}` under the recorded canonical inverse-image/restriction comparison.
  `R((g)_*[AddCommGrpCat.{u+1}])` and `R((h)_*[AddCommGrpCat.{u+1}])` are total
  unbounded right derived functors. The global and local arrows use the dependency's
  `abelianDerivedBaseChangeArrow` unchanged.
* `derivedInverseImageSquare` descends the existing canonical sheaf square isomorphism
  through the derived localization, using `mapDerivedCategoryCompIso` and
  `mapDerivedCategoryNatIso`. `derivedSliceComparison` is its inverse's mate under
  the canonical `mapDerivedUpperStarLowerStarAdjunction` for the two direct images.
  Thus its normalization is fixed by the unit and counit, rather than chosen.
* `derivedLeftComparison a b fU fac` is C_L^D: whisker the inverse-image comparison
  for fa = bf_U by Rg_*, then whisker the slice comparison for g by f_U^{-1}.
  `derivedRightComparison sq a b fU fac` is C_R^D: whisker the slice comparison for h
  by e^{-1}, then whisker the inverse-image comparison for ed = ce_U by Rh_{U*}.
  Functor associators provide only rebracketing. The first two `IsIso` clauses state
  exactly the invertibility specified by the two displayed canonical isomorphisms
  in the node. They are conclusions, not hypotheses or choices of comparison maps.
* The next conjunct, universally in K, is the stated equation
  `D(a^*).map beta_K ≫ C_R^D.app K = C_L^D.app K ≫ beta_local_(D(c^*)K)`.
* The following conjunct universally quantifies K, L, and `φ : K ⟶ L`, and states
  naturality of that common arrow: source.map φ followed by the arrow at L equals
  the arrow at K followed by target.map φ. Its source and target are the exact
  functor composites of the localization equation.
* Finally K is arbitrary and `q : ℤ`. The definition
  `restrictedDerivedCohomologyArrow a q beta_K` is
  `c_K⁻¹ ≫ a^*.map (H^q.map beta_K) ≫ c_L`, where c is the existing canonical
  `mapDerivedCategoryHomologyFunctorIso`. The final equality composes this actual
  transported restriction of H^q(beta_K) with H^q(C_R^D), and equates it to
  H^q(C_L^D) followed by H^q(beta_local). This renders the arrow-level
  exact-restriction/cohomology clause explicitly.

Dependency declarations read and used (directly or through the cited imports):

* `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `ChosenCartesianSquare.baseChangeInverseImageIso` and its underlying chosen square.
* `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`:
  `Etale.abelianDerivedBaseChangeArrow`; current source also read with
  `scompile.py --source`. Its unit-e/composition/counit-f construction is unchanged.
* `Sheaf.AlgebraicGeometry.BaseChangeArrowLocalization`:
  `BaseChangeLocalization.localArrow` and `localSquare` (actual pullback constructions).
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `lowerStarComp` and the adjunction-normalized `upperStarComp`, and the canonical
  `squareUpperStarIso` obtained from those comparisons.
* `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
  `mapDerivedUpperStarLowerStarAdjunction`, and the same exact pullbacks and total
  derived direct images used by the abelian exchange dependency.
* `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `upperStarIsoLocalizationRestriction` and `localizationRestrictionLowerStarAdjunction`.
* `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, and
  `mapDerivedCategoryHomologyFunctorIso`; the latter is the descended exact-functor
  comparison of Mathlib's `Functor.homologyFunctorIso`.
* `Sheaf.Paper.RingedDerivedSliceLocalization`:
  `ringedDerivedSliceLocalization`, with its normalized direct-image comparison and
  `RingedSliceAdjunctionSquare` unit/counit equations, is imported for the proof.
* `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`:
  `upperStar_abelian_exact`; `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`:
  `siteRestriction_exact`; both current sources read using `scompile.py --source`.
* `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`:
  `Scheme.Etale.overEquiv` and the site/sheaf transport, available through the
  underived localization module.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`:
  `lowerStarComp_assoc`; Mathlib's `Adjunction.leftAdjointCompIso_assoc`, `mateEquiv`,
  localization lift and natural-transformation uniqueness, `DerivedCategory`,
  `Scheme.smallEtaleTopology`, `Sheaf`, and `Etale` are the recorded dependency APIs.

Edge cases: identity etale maps and arbitrary factorizations are retained, and empty
schemes are permitted. The zero complex, unbounded complexes, degree zero and negative
cohomological degrees are included. There is no positivity, boundedness, torsion, qcqs,
separation, or new universe-equality hypothesis. Unlike the saved arbitrary-pair
interface, the comparisons cannot be independently negated in the identity case.

Searches retained from the previous packet include LeanFinder, Loogle, LeanSearch and
grep for derived base change and etale restriction. Additional searches during repair:

* `msearch.py leanfinder`: canonical derived direct image restricted to an etale object
  versus direct image on the localized site. Eight hits, including generic dense-subsite
  restriction and `Scheme.Etale.forget`; no comparison for these derived composites.
* `msearch.py leansearch`: canonical derived sheaf base change maps commute with
  restriction to an etale slice. Eight hits on ordinary sheaf restriction/global sections;
  none gives the required canonical unbounded comparisons or compatibility.
* `msearch.py loogle`: `CategoryTheory.mateEquiv, CategoryTheory.TwoSquare`.
  Twelve hits include `mateEquiv`, `mateEquiv_counit`, `unit_mateEquiv` and pasting;
  the generic mate construction is reused, with no new mate definition.
* `msearch.py grep`: `derivedLeftComparison|derivedSliceComparison|derivedBaseChangeArrow_localization`
  in Mathlib CategoryTheory: zero hits. The same `rg` in WeilConjectures and lean/Sheaf
  returned no existing declaration. Searches for the item id in upstream also find none.
* DAG title grep identified the underived arrow-localization node and the general ringed
  slice theorem as the relevant nearby notions; both are reused. `blueprint_refs.py
  search 'derived-localization-comparison'` returned zero blueprint nodes. The general
  ringed slice theorem does not define the two geometric abelian comparison composites.

There is no unresolved statement dispute or fault in the original node.

## New nodes

`def-sbc-derived-localization-comparison-data` now defines the actual canonical source
and target transformations, with helpers for the descended inverse-image square and its
derived adjunction mate. Its module is
`Sheaf.AlgebraicGeometry.DerivedLocalizationComparisonData`. The node cites each
notion it uses, including the existing geometric local-square construction. Its statement
contains no unconstrained comparison datum and no claimed proof. Its sources are Stacks
0EZR and 07A7 for the canonical comparison and transpose formulas, and 0D6G for the
slice interpretation. The searches above found no existing definition of these geometric
unbounded composite transformations; existing inverse-image, mate, and derived-functor
constructions are used, not duplicated. The consuming theorem states their invertibility,
so the new definition node has no dependency on that theorem and creates no cycle.

## Second reading by NP

This is the required author self-check; the dispatcher brief supplies the maintainer's
independent reading and forbids starting another agent. Reopened the original node, both
final modules, all statement-dependency records and their signatures, and Stacks 0EZR.
The saved arbitrary-comparison hypothesis was a real mismatch and was removed. All four
geometric projections and the canonical local-square map agree in direction. The left
comparison uses the square fa = bf_U and the g slice; the right comparison uses the h
slice and ed = ce_U. Their natural transformations are built with the canonical mate,
not by choosing a Nonempty witness. The theorem's IsIso clauses match the node's
isomorphism signs, followed by the exact arrow identity, naturality for arbitrary derived
arrows, and the restricted H^q arrow under the actual cohomology transport. Universes and
all-integer/unbounded quantifiers are unchanged. Neither extra geometric hypotheses nor
an arbitrary action, map or comparison are supplied. Metadata now assigns each module
only its own actual declarations, with verbatim primary signatures and existing=false.
