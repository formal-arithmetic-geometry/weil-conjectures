## Worker report

The delivery states `SSet.Presentability.indKappa_extension` in
`Sheaf.CategoryTheory.IndKappaExtension`. Its only theorem has proof `sorry`.
The three supporting definitions have actual data: `indKappaYonedaInUniverse`
is the existing Yoneda map transported by `SSet.uliftFunctor.map`;
`indKappaFilteredFunctors` is the existing vertexwise full-subcomplex construction
on functors with the specified preservation property; `indKappaRestriction` is
its inclusion followed by `MonoidalClosed.pre` of that actual Yoneda map.
These are helpers specifying the very functor category and canonical restriction
map asserted in this node, not independent replacement notions.

Hypothesis and clause correspondence:

- A small infinity category C is `(C : SSet.{u}) [Quasicategory C]`.
  The small universe is u, including for the cardinal and every use of `IsSmall`.
- An infinite regular cardinal is `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`.
  Mathlib `Cardinal.IsRegular` includes `aleph0_le`; infinitude is not omitted.
- D is `(D : SSet.{max (u + 1) v}) [Quasicategory D]`. Its containing universe v
  is arbitrary; D need not be small, cocomplete or presentable in the first clauses.
  The nested ULifts of C and the ULift of Ind merely put the same categories and
  Yoneda map in this common universe. They impose no universe equality and do not
  enlarge the class of colimits called small.
- Local smallness is `hD : IsLocallySmall.{u, max (u + 1) v} D`.
- Existence of small kappa-filtered colimits is
  `hcolim : HasSmallKappaFilteredColimits D κ`.
- The full coherent functor category is `indKappaFilteredFunctors C κ D`.
  Its ambient category is the internal hom from the lifted Ind completion to D.
  Its vertex predicate is precisely the existence of the corresponding actual
  simplicial functor with `PreservesColimitsIn` for small quasicategorical
  kappa-filtered shapes. `fullSubcomplex` retains every higher simplex on these
  vertices. The vertex equation uses the existing `diagramVertex` correspondence;
  it does not weaken the preservation predicate.
- Restriction is the explicitly defined `indKappaRestriction C κ hκ D`.
  `IsFunctorEquivalence` of this map is the first conjunct. Its quasi-inverse and
  coherent natural inverse equivalences express the equivalence of the complete
  functor categories, including all transformation spaces. In particular this
  includes essential uniqueness with the identification on C: the fiber over f
  is contractible. Merely asserting an equivalence between two chosen extensions
  would not express this part; the full restriction equivalence does.
- Every `f` is universally quantified, with no preservation assumption. The next
  conjunct supplies an actual extension functor F, its filtered-colimit preservation,
  and `AreNaturallyEquivalent (indKappaYonedaInUniverse C κ hκ ≫ F) f`.
- The properties are then asserted for EVERY extension F with exactly these two
  properties, not just a particular existentially chosen extension.
- Full faithfulness of f is `IsFullyFaithful f`. Compactness is
  `∀ c, IsKappaCompact D κ (f.app _ c)`, for every vertex of the lifted C.
  Under these assumptions the conclusion includes `IsFullyFaithful F`.
- Equivalence onto the replete full essential image uses the published
  `fullEssentialImage F`, an actual restricted map F₀, its equation
  `F₀ ≫ (fullEssentialImage F).ι = F`, and `IsFunctorEquivalence F₀`.
- The further generation hypothesis quantifies over EVERY object d of D.
  It provides a small kappa-filtered I, a coherent p into D, equivalences from
  every p(i) to some f(c), a colimiting cocone t, and an equivalence d ≃ t.apex.
  Thus diagrams are coherent diagrams in the replete full image, not merely
  sets of objects and not arbitrary non-filtered diagrams. Fullness under the
  preceding full-faithfulness assumption gives precisely the node's meaning of
  a filtered colimit of objects f(c). The conclusion is `IsFunctorEquivalence F`.
- The final implication is a separate conjunct OUTSIDE the full-faithfulness and
  compactness implication. C having all kappa-small colimits is the universal
  existence of `IsColimiting` cocones for all `IsKappaSmall κ K` and all diagrams
  into the lifted C. D presentable is `IsPresentable.{u, v} D`. Preservation by f
  is `PreservesColimitsIn f (fun K _ _ ↦ IsKappaSmall κ K)`. Its conclusion is
  `PreservesColimitsIn F (fun K _ _ ↦ IsSmall.{u, max (u + 1) v} K)`, all small
  simplicial indexing shapes, without a quasicategory restriction on those shapes.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.IndKappaPresentability`:
  `SSet.Presentability.indKappa`, `indKappaYoneda` and their defining full-subcomplex
  and range constructions. This is the recorded Ind completion, not ordinary Ind.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall`, `IsKappaSmall`, `IsKappaFiltered`,
  `IsLocallySmall`, `HasSmallKappaFilteredColimits`, `IsKappaCompact`,
  `IsPresentable`, `PreservesColimitsIn`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.fullSubcomplex`, `diagramVertex`, `IsFullyFaithful`,
  `IsEquivalenceEdge`, `AreNaturallyEquivalent`, `IsFunctorEquivalence`,
  `coconeCategory`, `IsColimiting`.
- `Sheaf.CategoryTheory.InfinityFullEssentialImage`:
  `SSet.Enhanced.fullEssentialImage`, with `fullyFaithful_fullEssentialImage`
  as the proof interface for the essential-image clause. This node is already
  among the item's proof dependencies; its module is public because its
  construction occurs in the statement.

The already-stated proof dependencies also imported are
`Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`,
`Sheaf.CategoryTheory.IntermediatePresheafKan` and
`Sheaf.CategoryTheory.InfinityYonedaEvaluation`. The recorded proof dependencies
`lem-coef-infinity-presheaf-free-cocompletion`,
`lem-coef-infinity-pointwise-yoneda-evaluation`,
`lem-coef-infinity-presheaf-ind-criterion` and
`lem-coef-infinity-yoneda-presheaf-limits` have no recorded Lean module in the
read snapshot, so no guessed imports were added for them. Their complete roles
remain in the theorem's eight-step proof docstring. None supplies an object
needed to type this statement; its statement dependencies are all usable.

Edge cases checked before writing:

- Empty C gives empty Ind, because filtered indexing categories are nonempty.
  There is still the unique empty-source functor into every D; D is not forced
  empty for the restriction-equivalence assertion. The generation hypothesis
  forces D empty in this case, so its equivalence consequence is consistent.
  The all-colimit clause does not apply to empty C because C has no initial object.
- Empty D causes no problem: functors and extensions are quantified only when
  their types are inhabited. If C is empty, the empty-source case is retained.
- Empty indexing simplicial sets are tested by `IsKappaSmall` and `IsSmall` in
  the final clause, so preservation of initial objects is included.
- Empty filtered indexing categories are excluded by the existing definition
  `IsKappaFiltered`, whose test shapes include the empty shape.
- The case κ = aleph0 is retained, as are C terminal and arbitrary larger target
  universes. No compactness or full faithfulness is imposed for existence or the
  all-colimit conclusion.
- A D with filtered colimits but lacking arbitrary colimits still satisfies the
  first part's hypotheses. Presentability occurs only in the final implication.

Searches for an existing statement (all through the prescribed wrapper unless noted):

1. leanfinder: `A functor from a small infinity category extends uniquely along
   Yoneda to its kappa Ind completion preserving filtered colimits`. Eight hits:
   ordinary `CategoryTheory.Ind`, its Yoneda and limit functors, `IsIndObject`
   results, and `Presheaf.uniqueExtensionAlongULiftYoneda`. These concern ordinary
   categories and set-valued presheaves, not coherent space-valued functor categories.
2. loogle: `CategoryTheory.Ind, PreservesFilteredColimits`. Zero hits; the second
   identifier is unknown.
3. grep: `Ind.*extension|indKappa|Ind.*[Uu]niversal|Ind.*[Ee]quivalence` in
   Mathlib CategoryTheory. Returned ordinary category, localization and Ind-object
   results, no quasicategorical kappa-Ind extension statement.
4. Direct rg for `IndKappa|indKappa|Filtered.*[Ee]xtension|filtered.*extension`
   in upstream WeilConjectures and the side CategoryTheory modules. Upstream
   hits concern ordinary pro categories and unrelated filtered scalar extensions.
   Side hits identify the dependency `IndKappaPresentability` and a consumer's
   proof plan (`InfinityCompactGeneratedFilteredHull`), not this theorem.
5. Direct grep for `lem-coef-ind-kappa-extension` in upstream WeilConjectures:
   no matches. No existing declaration states this node's conclusion.

Source checked: the primary HTT PDF, Propositions the project server and the project server,
printed pp. 406--407 (PDF pp. 423--424), directly gives the restriction equivalence
and the compact-generation consequences. The last clause uses the node's stated
Corollary the project server argument, retained step by step in the docstring.
There is no statement correction, dependency repair, or disputed statement.
The node copy changes only its `lean` record.

Validation: the prescribed `scompile.py` compiled this file alone against the
published library with no errors or warnings. The initial run found only an
implicitly-used-variable warning, repaired by writing the explicit
`@IsKappaFiltered` proof argument. The node signature was checked verbatim against
the file, all lines are at most 100 characters, and the only changed node field
is `lean`. The prescribed `deliver2.py --no-push` runs the final server preflight;
the READY handoff is issued only after that command prints OK.

## Second reading by Q101

I read the item node, its three statement dependencies, the complete Lean module, and
HTT Proposition the project server (p. 406/printed p. 406 in the PDF) and Proposition the project server
(printed pp. 407--408), together with Corollary the project server for the final clause. The
node's Step 1 list and the corresponding Lean are:

1. The small infinity category is `C : SSet.{u}` with `[Quasicategory C]`; the
   Lean binders in `indKappa_extension` use exactly these objects and the same `u`.
   Verdict: present and no extra smallness hypothesis.
2. The infinite regular cardinal is `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`.
   `Cardinal.IsRegular` supplies infinitude in the recorded Mathlib convention.
   Verdict: present, with no stronger cardinal assumption.
3. The target is `D : SSet.{max (u + 1) v}` with `[Quasicategory D]`, and
   `hD : IsLocallySmall.{u, max (u + 1) v} D` and
   `hcolim : HasSmallKappaFilteredColimits D κ` are the only target hypotheses.
   The arbitrary `v` is retained. Verdict: present with the source universes and
   no cocompleteness or presentability added to the first part.
4. The recorded Ind completion and Yoneda map are `indKappa C κ` and
   `indKappaYonedaInUniverse C κ hκ`, with actual universe lifts. The helper
   `indKappaYonedaInUniverse` is the existing `indKappaYoneda` transported by
   `SSet.uliftFunctor.map`; it does not change the cardinal or small universe.
   Verdict: same canonical construction as the dependency node.
5. The full coherent subcategory of functors `Indκ(C) ⟶ D` preserving small
   κ-filtered colimits is `indKappaFilteredFunctors C κ D`, built from the actual
   internal hom and `fullSubcomplex`; its vertex predicate explicitly contains
   an actual functor, `IsSmall`, a quasicategory witness, and
   `@IsKappaFiltered`. Verdict: all vertices and higher simplices have the
   required full coherent meaning.
6. Restriction is the actual map `indKappaRestriction C κ hκ D`, namely the
   subcomplex inclusion followed by `MonoidalClosed.pre` of the lifted Yoneda
   map. `IsFunctorEquivalence` is the first conclusion. Verdict: canonical
   restriction, including coherent quasi-inverse and both natural equivalences.
7. Every `f` has the existential extension clause with `F`, preservation of
   exactly the same small κ-filtered class, and
   `AreNaturallyEquivalent (indKappaYonedaInUniverse C κ hκ ≫ F) f`. Verdict:
   universal quantification and the comparison direction match the node.
8. For every `F` satisfying those two properties, the implication has the
   full-faithfulness and compactness hypotheses, then `IsFullyFaithful F`, a
   factorization through `fullEssentialImage F` with the equation and
   `IsFunctorEquivalence F₀`, and finally the separate filtered-generation
   implication. Verdict: every extension is covered, and the replete full image
   and coherent generation clauses are not weakened.
9. The generation clause quantifies over every `d : D _⦋0⦌`, a small filtered
   `I`, a coherent `p : I ⟶ D`, an equivalence edge from each `p(i)` to some
   `f(c)`, a colimiting cocone, and an equivalence from `d` to its apex. The
   endpoint equations use the same `IsEquivalenceEdge` orientation as
   `fullEssentialImage`. Verdict: coherent filtered generation, not merely
   objectwise generation.
10. The final implication is outside the full-faithfulness block. Its hypotheses
    are all κ-small colimits in `C`, `IsPresentable D`, and preservation by `f`
    of `IsKappaSmall`; its conclusion is preservation by `F` of every
    `IsSmall.{u, max (u + 1) v}` shape. Verdict: clause order and hypotheses match
    the node and include empty shapes.

The edge cases are covered. Empty `C` gives the empty Ind completion and retains
its unique empty-source functor; the generation implication then forces the target
to be empty when invoked. Empty indexing shapes are included by `IsKappaSmall`, so
the final preservation clause includes initial objects. `IsKappaFiltered` itself
uses the empty test shape, so empty filtered indices are excluded. The zero/empty
simplicial target and terminal `C` introduce no extra assumptions. The case
`κ = aleph0`, arbitrary containing target universe `v`, and `n = 0` vertex
quantifiers are all retained.

I reran the prescribed searches. `leanfinder` returned only ordinary-category
`CategoryTheory.Ind` and unrelated filtered-colimit declarations; `loogle` had no
match for `CategoryTheory.Ind, PreservesFilteredColimits`; and the Mathlib grep
returned no infinity-categorical extension theorem. Grep over upstream
`WeilConjectures/` found no matching statement. Grep over the side Lean tree found
`AccessibleIndColimitExtension`, but that is the distinct presentable compact-hull
lemma and does not state this restriction equivalence or its universal extension
property. The existing `IndKappaPresentability`, `PresentableInfinityCategory`,
`EnhancedDiagramsCones`, and `InfinityFullEssentialImage` declarations were opened
and their signatures are exactly the interfaces used here.

No mismatch was found. I changed no statement, dependency, helper, or declaration.
The module compiles cleanly through `scompile.py`; there are no warnings, all
variables and universes are bound, and every line is at most 100 characters.
