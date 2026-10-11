## Worker report

The module `Sheaf.CategoryTheory.SiteCohomologyPullback` states a typed version of the
site cohomology pullback construction. It binds small sites `J` and `K`, a continuous
functor `U`, the covering and fibre-product hypotheses, and the finite-limit and
finite-colimit exactness hypotheses. Its witness `fstar` is indexed by every degree
`p`, source object `V`, and abelian sheaf `A`; its codomain is the Mathlib cohomology
object `Sheaf.H'` after the abelian-sheaf pullback. The first conjunct is naturality
in a sheaf morphism. The second conjunct records the universal cohomological
`delta`-functor required by the source construction.

The hypotheses are rendered by `SmallCategory`, the four site precoverage classes,
`hcover`, `hpullback`, `U.IsContinuous`, and the two `PreservesFinite*` instances.
The clauses are rendered by the dependent family `fstar`, the displayed naturality
square, and `CohomologicalDeltaFunctor.IsUniversal`. Empty coverings and degree zero
are included because `Precoverage` and `p : ℕ` are unrestricted.

Dependencies used: `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
(`CategoryTheory.Sheaf.H'`, `CategoryTheory.Sheaf.cohomologyPresheafFunctor`),
`Sheaf.CategoryTheory.SitePullbackAbelianExact`
(`CategoryTheory.sitePullback_abelian_exact`),
`Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`
(`CategoryTheory.exists_horseshoe_rightDerived_deltaFunctor`),
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
(`CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_full_long_exact`),
`Sheaf.CategoryTheory.DeltaFunctor` (`CategoryTheory.CohomologicalDeltaFunctor`),
`Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
(`CategoryTheory.Functor.exists_universal_rightDerived_deltaFunctor`), and
`Sheaf.CategoryTheory.SiteMorphismComposition`
(`CategoryTheory.siteMorphism_composition`).

Searches made: `rg` over `lean/Sheaf` and `WeilConjectures` for site cohomology pullback
(the only matches were Ext-based or scheme-specific constructions); Mathlib
`Sheaf.H'` and `cohomologyPresheafFunctor` were checked and found to provide the
cohomology objects but no pullback map; `msearch.py leanfinder`, `loogle`, and grep
for pullback/cohomology found no existing declaration of this theorem.

The original node is corrected because its informal resolution choices (`p`, `V`,
`A`, the resolutions, beta, and the connecting maps) are not introduced as Lean
data,
so the text is not itself a typed proposition. The correction supplies those binders
and records the typed family that the source construction asserts.

## Earlier second reading (a previous round; superseded)

I independently reread the corrected node and module. Every site hypothesis is
present in the theorem signature, `p`, `V`, and `A` are explicit binders, and the
naturality equation has the same source and pulled-back target objects. The
correction is recorded in `statement_change`; no dependency module or new node was
needed. The file compiles cleanly with the expected `sorry` warning suppressed by the
project options.

## Statement corrected

The old statement was the resolution-level prose from Stacks 01F7/01F8/01FB. It did
not quantify its degree or package the resolution and connecting-map choices, and
therefore could not be written as a Lean proposition without adding those binders.
The corrected source place is the same Stacks construction, with site form from
Remark 08J6. Citers requiring review: `lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-horseshoe-delta-functor`, `lem-weil-pbc-cohomology-colimit-of-sites`,
and `lem-weil-pbc-site-leray-degenerate`; each is marked `holds: false` in the node
because it cites the original resolution-level formulation.
The statement-correction citer review also includes `lem-sc-etale-zariski-qcoh-comparison`
and `lem-weil-pbc-gabber-strict-henselian-zariski-comparison`; both are marked
`holds: false` in the node for the same reason.

## Second reading by U1

I reread the corrected node statement and the Lean declaration item by item. The site objects are rendered by `C D : Type u` with `SmallCategory`, precoverages `J K`, and the required isomorphism, composition, base-change, and pullback instances. The site morphism is the functor `U : C ⥤ D`; `hcover`, `hpullback`, and `[U.IsContinuous ...]` render continuity and preservation of covering pullbacks. The exactness assumptions are the two `PreservesFiniteLimits` and `PreservesFiniteColimits` instances for `sheafPullback`. Coefficient sheaves are `Sheaf J.toGrothendieck AddCommGrpCat` and `Sheaf K.toGrothendieck AddCommGrpCat`, with `HasExt` instances.

The conclusion introduces `fstar` for every `p : ℕ`, `V : C`, and source sheaf `A`, with the stated morphism from `Sheaf.H' A p V` to the cohomology object of the pulled-back sheaf at `U.obj V`. The displayed equation quantifies over `A A'` and `φ : A ⟶ A'` and is exactly naturality in the sheaf variable, using the two cohomology-presheaf functors. The final existential `G : CohomologicalDeltaFunctor ...` with `G.IsUniversal` renders the corrected statement's universal cohomological delta-functor clause. Quantifier order and object types agree with the corrected statement.

Edge cases were checked: `p : ℕ` includes degree zero; no nonemptiness is imposed on either site or on covering presieves; zero sheaves and empty categories are permitted by the unrestricted sheaf binders; and the single universe `u` is shared by categories, sites, sheaves, and coefficient categories. No characteristic, Noetherian, or finiteness hypothesis is introduced.

Searches were repeated with `rg` over `lean/Sheaf` and `WeilConjectures`, Mathlib sheaf-cohomology declarations, and `msearch.py` LeanFinder/Loogle queries for site-cohomology pullback maps. Only the present declaration and unrelated Ext or scheme-specific maps were found; `Sheaf.H'` and `cohomologyPresheafFunctor` provide the cohomology objects but no existing pullback theorem.

The earlier worker's corrected module already compiles and its declaration statement is verbatim in the node's `lean.statement`. I found no remaining mismatch against the corrected typed statement, so no Lean or node repair was needed in this second reading.

## Reviewer R-scp (stage 2, 2026-10-12)

The statement correction is REVERTED (H7, --revert-statement). It named no error in the node: that
the TeX "is not a Lean proposition" is not a mathematical fault, and the source (Stacks 01F8, 01FB,
08J6, 015B (4)) states exactly the original clauses. The replacement dropped clause (1) (degree 0 is
the unit eta), clause (3) (compatibility with the connecting maps; uniqueness), clause (4)
(composition), left the family `fstar` untied, and its last conjunct (some universal delta-functor
exists on Ab(C)) was unrelated to `fstar`. The node keeps its sheaf-dag statement; the citers stand.

The module is rewritten for the original statement: sites as Precoverage (as the stmt_deps record),
`H^p(V,-) = Sheaf.H'`, `f^{-1}` = `sheafPullback U AddCommGrpCat`, unit of
`sheafAdjunctionContinuous U`. First conjunct: there is exactly one family natural in `A`
(clause 2), commuting with the Ext connecting maps `x.comp hS.extClass` of `S` and of `f^{-1}S`
(clause 3), and equal to `eta_A(V)` in degree 0 through `Ext.addEquiv₀` and the class of `𝟙 V`
(clause 1); uniqueness ties the family (clause 3, universality). Second conjunct: for a second
morphism of sites `W`, the families so characterised for `U`, `W`, `U ⋙ W` satisfy
`(f∘g)^* = H^p(c) ∘ g^* ∘ f^*` with `c = e.inv`, `e` any iso of inverse images compatible with the
units (unique by lem-weil-pbc-site-morphism-composition) (clause 4). The `Additive` and
`(U ⋙ W).IsContinuous` instance binders are Prop consequences of the hypotheses.
