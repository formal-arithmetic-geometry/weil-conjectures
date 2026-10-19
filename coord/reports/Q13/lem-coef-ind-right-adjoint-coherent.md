## Worker report

Existing match: `SSet.Presentability.ind_right_adjoint_coherent` in
`Sheaf.CategoryTheory.IndRightAdjointCoherent`, published on `newtargets-dag`.
The item adds no Lean declaration. The node copy records `existing: true`
and copies the existing theorem signature
verbatim, including its line break. Its proof remains `sorry`, as required at stage 2.

The recorded declaration and the actual dependency structure were read both from
the shared sources and through `scompile.py --source`. In particular the published
`CompactIndRight` already contains `right_preserves`; the result is not being
matched against an older interface omitting right-adjoint preservation.
There is no repair note for this item in `coord/repair-notes/`.

Source checked: [GHN, Definition 10.4](https://arxiv.org/html/1501.02161v3),
lines 896--898, and the actual dependency declarations listed below. Definition
10.4 uses the same category of small categories admitting the specified colimits,
and the same coherent contravariant Ind functor with right-adjoint edge values
preserving filtered colimits. The node expands its extension and adjunction data.

Hypotheses and clauses, read through the existing structure:

1. The smaller universe is `u`. The ambient universe is `max (u + 1) v`, with
   independent `v`; `Enhanced.CatInfinity` is formed one universe higher. The
   `uliftFunctor` occurrences only transport simplicial sets between these universes.
2. The fixed infinite regular lambda is `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`.
   Mathlib's `Cardinal.IsRegular` includes `aleph0 ≤ κ`, so infinitude is not omitted.
3. The source category is `compactRex κ`. Its `compactRexSubcomplex` retains precisely
   coherent simplices with `HasKappaSmallColimits` at each object and
   `PreservesKappaSmall` at each arrow. Its ambient `CatInfinity` retains
   quasicategories and cores of internal functor categories, including every
   higher mapping simplex, rather than an ordinary category of functors.
4. For each small source object `c`, `CompactIndRight.models c` is a
   `CompactIndModel (compactRexValue c) κ E`. Its `equivalence` and `isEquivalence`
   identify `E` with the actual `indKappa C κ` after universe lift. This is the
   full replete subcomplex of `Spaces.infinityPresheaves C` defined by
   `IsIndKappaObject C κ`: small κ-filtered colimits of representables in the
   presheaf category. Thus an arbitrary unrelated category is not substituted.
5. The Yoneda embedding `j_C` is `models c |>.yoneda`; its `yoneda_comparison`
   identifies its composite through the above equivalence and the actual Ind
   inclusion with `Enhanced.Yoneda.yoneda C`. Both source and target Yoneda
   maps in the node are rendered by this same normalization.
6. For an edge `e` encoding `u : C → D`, `extensions e` gives `L` from the
   model at `δ 1 e` to the model at `δ 0 e`. Its first conjunct is
   `PreservesKappaFiltered κ L`. Its second conjunct is the coherent equivalence
   `(models C).yoneda ≫ L ≃ uliftFunctor.map (compactCatArrow e.val) ≫
   (models D).yoneda`, precisely `L j_C ≃ j_D u`.
7. Essential uniqueness of the extension is the existing equivalence
   `indKappaRestriction` in `indKappa_extension`: the full coherent category
   of filtered-colimit-preserving extensions restricts equivalently to the
   functor category on C. Hence the existential `L` with the normalization
   in clause 6 is precisely the essentially unique extension named in the node;
   no extra choice or extension axiom is introduced.
8. The last conjunct of `extensions e` is
   `Nonempty (ModelInfinity.CoherentAdjunction L
   (compactContravariantArrow diagram (ULift.up e)))`. This is the right
   adjoint `u*` to that very extension. `CoherentAdjunction` has coherent
   unit/counit edges, triangle 2-simplices, and universal comma objects expressing
   the mapping-space adjunction; an ordinary homotopy-category adjunction is
   insufficient and is not used here.
9. `right_preserves e` is `PreservesKappaFiltered κ` for exactly
   `compactContravariantArrow diagram (ULift.up e)`, the same `u*` in clause 8.
   This is distinct from preservation by the left adjoint in `extensions e`.
10. `diagram` is an entire simplicial map
    `(uliftFunctor.obj (compactRex κ)).op ⟶ Enhanced.CatInfinity`.
    It includes all higher simplices and commutes with every simplicial operator.
    Opposite reversal and `compactContravariantArrow` give the required direction
    `Ind(D) → Ind(C)`. Thus identities, composition, and higher compatibility are
    included, not merely the assignment on vertices and edges.
11. `Nonempty (CompactIndRight.{u, v} κ)` concludes simultaneous existence of
    all these data. It does not choose the data in a definition from a mere
    unproved existence theorem.

Dependency declarations used, with their recorded modules:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.coneCategory`, `coconeCategory`, `IsColimiting`,
  `AreNaturallyEquivalent`, `IsFunctorEquivalence`, `fullSubcomplex`.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall`, `IsKappaSmall`, `IsKappaFiltered`,
  `PreservesColimitsIn`, `IsKappaCompact`, `IsPresentable`.
- `Sheaf.CategoryTheory.IndKappaPresentability`:
  `SSet.Presentability.indKappa`, `IsIndKappaObject`, `indKappaInclusion`,
  `indKappaYoneda`, `indKappa_presentability`.
- `Sheaf.CategoryTheory.PresentableInfinityAdjoints`:
  `SSet.Presentability.presentable_infinity_adjoint_localization`; its adjunction
  notion is the published `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction`.
- `Sheaf.CategoryTheory.IndKappaExtension`:
  `SSet.Presentability.indKappaRestriction`, `indKappa_extension`.
- `Sheaf.CategoryTheory.EnhancedCartesianFibration`:
  `SSet.Enhanced.sectionSSet`, `CatInfinity`, `catInfinitySubcomplex`.
- `Sheaf.CategoryTheory.SmallRightAdjointDiagramCompactModel`:
  `SSet.Presentability.CompactIndRight`, `CompactIndModel`, `compactRex`,
  `compactRexValue`, `compactContravariantArrow`, `PreservesKappaFiltered`,
  `PreservesKappaSmall`, `HasKappaSmallColimits`, and its recorded main theorem
  `small_right_adjoint_diagram_compact_model`.

The existing module also imports the available proof dependencies
`EnhancedFunctorConeCalculus`, `CatInfinityLimitsCartesianClosed`,
`CatInfinityOppositeInvolution`, `InfinityPresheafIndCriterion`, and
`InfinityYonedaEvaluation`. Its proof docstring follows the node's six steps:
coherent presheaf precomposition, restriction by the Ind criterion, the extension
and adjoint theorem, identification by Yoneda, filtered preservation by compact
representables, and restriction of all higher coherence data.

Edge cases checked against the definitions:

- `κ = aleph0` is allowed: `Cardinal.isRegular_aleph0` supplies exactly the regularity
  hypothesis; there is no uncountability or successor-cardinal hypothesis.
- The empty indexing simplicial set is included in `HasKappaSmallColimits` and
  `PreservesKappaSmall`. Thus initial objects and their preservation are required.
  An empty source category is not erroneously admitted as κ-cocomplete.
- Filteredness tests the empty diagram, enforcing nonemptiness of the indexing
  category. Preservation tests every small filtered coherent diagram and every
  colimiting cocone, not an arbitrary selected family of colimits.
- Identity edges and degenerate higher simplices remain in the domain of the
  entire simplicial map; nontrivial higher simplices are not discarded.
- The containing universe may be arbitrarily large via `v`; no equality between
  the smaller and containing universes is imposed.

Searches performed on 2026-10-17:

- `msearch.py leansearch`, query "Ind completion infinity categories coherent right
  adjoints filtered colimits": eight hits including ordinary
  `Limits.isIndObject_colimit`, `Ind.lim`, `IsFiltered.of_isRightAdjoint`, and
  filtered-colimit classes. Their displayed signatures concern ordinary categories;
  none states this coherent infinity-categorical assertion.
- `msearch.py leanfinder`, query "coherent contravariant Ind completion functor of
  infinity categories right adjoints preserving filtered colimits": eight hits,
  including ordinary `Ind.inclusion`, `Ind.lim`, `Ind.leftExactFunctorEquivalence`,
  `Ind` and presheaf adjoint facts. These use Type-valued ordinary presheaves.
- `msearch.py loogle`, query `"Ind", "rightAdjoint"`: three hits, for indiscrete
  topological modules, coinduced representations, and finite-index induction.
  None is about coherent Ind completion.
- `msearch.py grep` in Mathlib `CategoryTheory`, query
  `Ind.*(rightAdjoint|IsRightAdjoint)|Quasicategory.*Ind`: zero hits.
- `rg` of that pattern and `ind_right_adjoint_coherent|CompactIndRight` in the
  upstream `WeilConjectures` and project sources: no upstream match; the published
  project module and its dependency give the exact match analyzed above.
- `grep -rn lem-coef-ind-right-adjoint-coherent` in upstream `WeilConjectures`:
  no hit. The upstream name index also has no hit for the node or the declaration.
- `scompile.py --source Sheaf.CategoryTheory.IndRightAdjointCoherent` and the same
  request for `SmallRightAdjointDiagramCompactModel` confirmed the current published
  text, including `CompactIndRight.right_preserves`.

Validation: `scompile.py` is used for a scratch consumer importing the published
module and checking the theorem and the structure projections for the diagram,
models, extensions, right-adjoint preservation and Yoneda normalization. This
scratch file is not a delivered module. The delivery wrapper also checks the
existing declaration using its own `#check` consumer. No source library is edited,
no definition is added, and no node statement is corrected or disputed.
The dependency module below is delivered to repair an import-closure compiler failure.


## Dependency modules

`lem-coef-space-valued-straightening`: the exact published module fails in
`SSet.Enhanced.SpaceStraightening.Diagrams` with `lean.dependsOnNoncomputable`,
because its definition refers to `SSet.Enhanced.smallSpaces`, now noncomputable.
The scratch consumer and the first delivery dry run independently report this
same error. The module is needed through the import chain
`IndRightAdjointCoherent → PresentableInfinityAdjoints → CompleteAlgebroid →
KanRelativeNerveLeftFibration → SpaceValuedStraightening`.

The dependency module is fetched using `scompile.py --source` and changed only
from `abbrev Diagrams` to `noncomputable abbrev Diagrams`. Its entire mathematical
interface, real construction data, theorem signature, and ten-step proof docstring
are retained. In particular the module still states the global straightening
family, coherent base naturality, and the ordinary-base adjunction comparison.
No theorem is proved and no witness is chosen. The dependency node changes only
`lean`, with the required diagnostic note. The item cites this already landed
node under the authorization to add existing landed statement dependencies.
This is a computational annotation repair, not a mathematical statement change.
The maintainer should review the scope of this additional transitive-dependency
repair as well as the existing match. Every delivered Lean module is compiled
through `scompile.py` with the same 60-second per-file limit.

Compilation result: the repaired dependency and the scratch consumer both pass
`scompile.py` without warnings. The actual theorem and all six checked structure
projections are available after the repair. The entire source diff of the dependency
module is exactly the added `noncomputable` keyword.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
