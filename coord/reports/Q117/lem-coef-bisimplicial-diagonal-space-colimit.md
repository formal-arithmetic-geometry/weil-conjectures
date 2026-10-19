## Worker report

The module defines the degreewise coend point type `CoendPoint`, the generating relation
`CoendRelation`, and its quotient `CoendDegree`.  It defines `DiagonalColimitFamily`,
which records for every simplicial diagram of simplicial sets the coherent cocone in the
localized diagram, its colimiting property, the identification of its apex with the
bisimplicial diagonal, the explicit coend equivalence and formula, and naturality by the
canonical coherent transformation.  The theorem `bisimplicial_diagonal_space_colimit`
states existence of a localization of simplicial sets and such a family, with proof `sorry`.

The theorem's existential `C` is `SSet.{u+1}` and `q` is the localization map from
`largeNerve.{u+1,u,u+1} SSet.{u}`.  The localization clause is
`IsLocalization (weakEquivalences SSet.{u}) q`; the final clause is
`Nonempty (DiagonalColimitFamily q)`.  In `DiagonalColimitFamily`, `cocone` and
`colimiting` render the coherent cocone and its universal property for every
`Z : SimplexCategoryᵒᵖ ⥤ SSet`; `apex` identifies its apex with
`SSet.BousfieldKan.diagonal Z`; `coend_equivalence` and `coend_formula` render the
specified degreewise coend bijection and formula; `naturality` retains the full coherent
transformation for every map `f : Z ⟶ Z'`.

Dependency declarations used: `SSet.Enhanced.coconeCategory`, `SSet.Enhanced.IsColimiting`,
`SSet.Enhanced.AreNaturallyEquivalent`, `SSet.Enhanced.diagramVertex` from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; `HomotopicalAlgebra.FiniteReedy.IsLocalization`,
`largeNerve`, `diagram`, `object`, and `transformation` from
`Sheaf.CategoryTheory.FiniteReedyLocalization`; `SSet.BousfieldKan.diagonal` from
`Sheaf.AlgebraicTopology.BousfieldKanComparisonCalculus`; and the localization/model
interfaces from the recorded modules `SimplicialModelNerveLocalization`,
`KanQuillenRightProper`, `BisimplicialDiagonalEquivalence`, `ModelInfinityDerivedAdjunction`,
`ReedyModelStructure`, `EnhancedFunctorConeCalculus`, and `SmallDiagramModelRectification`.
The project has no recorded module for `lem-coef-simplicial-presheaf-projective-model`,
so no import was added for that dependency.

Edge cases checked: the coend relation includes identity arrows and all degrees; the
formula accepts empty rows and the empty simplicial set; `r` ranges over every degree;
`Z` is unrestricted (no Kan or cofibrancy assumption); and degree zero is included by
`CoendDegree` and the all-degree formula.  Naturality is quantified over all maps of
bisimplicial sets, including maps between empty diagrams.

Searches: `msearch.py leanfinder` for “The diagonal of a bisimplicial set computes the
coherent colimit of its rows in spaces” returned only ordinary `SSet.hasColimits`,
`SimplicialObject.instHasColimits`, and subcomplex colimit declarations (no match).
`msearch.py loogle` with `"diagonal", "colimit"` returned no hits.  `msearch.py grep`
with `bisimplicial|homotopyColimit|diagonalFunctor` in `AlgebraicTopology` returned no
hits.  Repository `rg` found only the existing ordinary bisimplicial diagonal and
Bousfield–Kan declarations, which do not state the coherent spaces colimit.  The HTT
source was read online at Examples A.2.9.21, A.2.9.29--A.2.9.31 and Theorem the project server.

No `STATEMENT-DISPUTED` flag or node fault.

## Second reading by Q117

I read the node statement, its HTT source place (Examples A.2.9.21, A.2.9.29--A.2.9.31, Corollary A.2.9.30, and Theorem the project server), the dependency declarations, and the module from the beginning. The item-by-item correspondence is:

1. The node's simplicial sets, nerves, spaces, coherent colimits, Kan model structure, and localization are rendered by the imports and by `C : SSet.{u + 1}`, `q : largeNerve.{u + 1, u, u + 1} SSet.{u} ⟶ C`, `IsLocalization (weakEquivalences SSet.{u}) q`, and the existing `Enhanced`/`FiniteReedy` declarations. Verdict: same localization object and no additional model or size hypothesis.
2. The arbitrary diagram `Z : Δᵒᵖ ⥤ SSet.{u}` is the binder in every family field. `SSet.BousfieldKan.diagonal Z` is the simultaneous diagonal; its definition applies both simplicial operators. Verdict: same diagram and diagonal, with no Kan or cofibrancy assumption.
3. The coend summands are `CoendPoint Z r = Σ n, (Z.obj (op n)).obj r × (r.unop ⟶ n)`, and `CoendRelation` has exactly `((Z(α))_r z,t) ~ (z,α ∘ t)`; `CoendDegree` is the quotient by the generated relation. Verdict: same degreewise quotient and variance.
4. `cocone Z` is a vertex of `Enhanced.coconeCategory (diagram q Z)`, and `colimiting Z` says it is initial in that coherent cocone space. `apex` pins its apex to `object q (diagonal Z)`. Verdict: this renders the coherent colimit and the displayed equivalence of apexes.
5. `coend_equivalence` and `coend_formula` give, for every degree `r`, the required bijection and the representative formula `(Z.map t.op).app r z`; `Quot.mk` uses exactly the stated coend representative. Verdict: same formula, including all `n` and `r`.
6. For every `f : Z ⟶ Z'`, `naturality` uses `transformation q f`, with the endpoint equations for `diagram q Z` and `diagram q Z'`. I found that the previous version stopped there and did not constrain the selected cocones. I added `coconeEdge` and `CoconeNaturality`: an apex edge and two 2-simplices with a common diagonal edge now record the coherent square between `cocone Z`, `cocone Z'`, and `transformation q f`. Verdict after the repair: naturality includes the full cocone data and its higher homotopy.
7. The theorem concludes exactly `∃ C q, IsLocalization ... ∧ Nonempty (DiagonalColimitFamily q)`, so the existential localization and family are present in the same order as the node. Verdict: same conclusion and quantifier order.

The added `CoconeNaturality` is only a rendering of the node's phrase “naturality ... includes these cocones”; it does not add hypotheses to the theorem or alter `lean.statement`. All helper declarations (`CoendPoint`, `CoendRelation`, `CoendDegree`, `coconeEdge`, `CoconeNaturality`, and `DiagonalColimitFamily`) are listed in the node's `lean.declarations`.

Edge cases checked: `Z` may be empty in every degree; the coend quotient and diagonal are then empty and the family has no nonemptiness premise. The zero simplicial set and empty rows are allowed. Degree `r = 0` is included by the unrestricted `r : SimplexCategoryᵒᵖ`; the displayed formula also includes `n = 0`. Identity arrows and all degeneracy/face arrows occur in `CoendRelation`. The type uses a free universe `u`, while the localization target is the prescribed containing universe `u + 1`; no characteristic, finiteness, Noetherian, or universe-equality assumption was introduced. Naturality quantifies over every map, including maps between empty diagrams.

For one-definition checks I searched independently with `msearch.py` using the queries “simplicial realization diagonal coherent colimit spaces” (LeanFinder: only ordinary realization and diagonal hits), “coend diagonal simplicial set realization” (Loogle: no identifier/hit), and `coend|realization|diagonal.*colimit|colimit.*diagonal|bisimplicial` in Mathlib AlgebraicTopology (only ordinary `SSet.toTop`/unrelated realization declarations). I also searched the project and slopmaster2 sources with `rg` for coend, bisimplicial, diagonal-colimit, and homotopy-colimit variants; no existing declaration states this theorem or its coherent cocone. The existing ordinary diagonal and Bousfield--Kan declarations are different notions. No node statement was changed.

The only mismatch found was the missing cocone compatibility in the original naturality field; it was repaired by the explicit apex edge and coherent-square data described above. The repaired file compiles cleanly with `scompile.py`; the only remaining diagnostic is the theorem's permitted `sorry`.

## Maintainer review fix (2026-10-17)

The maintainer's reviewer found two H3 gaps in `DiagonalColimitFamily` and fixed them in the module.
The theorem's signature and `lean.statement` are unchanged.
(1) The node says the colimit cocone *is* the coherent coend cocone, and that the leg from `q(Z_0)` comes from
`Z_0 × Δ^0 → diag Z`. The delivered family allowed any colimiting cocone with apex `q(diag Z)`, and its
`coend_equivalence` was not connected to the cocone. The fix adds `coendInclusion Z n : Z_n ⊗ Δ[n] ⟶ diag Z`,
`(z, t) ↦ (Z(t))_r z`, which has real data and a proved naturality. It also adds the field `legs`: a
`Composes` 2-simplex saying that the leg at `[n]` composed with `q(fst)` is `q(coendInclusion Z n)`. This
specifies every leg up to homotopy, and at `n = 0` it gives the degree-zero clause.
(2) In `CoconeNaturality` the apex edge `d` could be any edge. That made the clause follow from `colimiting`
alone, so naturality said nothing. `d` is now an explicit argument, and `naturality` sets it to
`q(diag f)` (`whiskerLeft diag (uncurry.map f)`, the same form as `comparison_calculus`).
The statement docstring now gives the node's six proof steps. `coendInclusion` has been added to `lean.declarations`.
