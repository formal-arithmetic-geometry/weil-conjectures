## Worker report

The item is stated in `lean/Sheaf/CategoryTheory/FilteredPresentationCommonRefinement.lean` as
`SSet.Presentability.exists_common_refinement`, with proof `sorry`.
The module uses the existing project module
`Sheaf.CategoryTheory.PresentableInfinityCategory` and its declarations
`IsSmall`, `IsKappaFiltered`, `IsLocallySmall`, `IsKappaCompact`, and the coherent
cocone predicates from `Sheaf.CategoryTheory.EnhancedDiagramsCones`.

The Lean statement renders the node clause by clause as follows.

* `E : SSet.{v}` with `[Quasicategory E]` is the locally small infinity category;
  `hE : IsLocallySmall.{u,v} E` gives local smallness.
* `hEcolim` quantifies over every small quasicategory, every cardinal `κ'`, every
  `IsKappaFiltered` indexing quasicategory, and every coherent diagram, and supplies a
  colimiting cocone. Thus all small filtered colimits are available.
* `κ : Cardinal.{u}` is uncountable via `Cardinal.aleph0 < κ`, and regular via
  `hκreg : κ.IsRegular`.
* `A₀,A₁ : Type v` carry `PartialOrder`; `posetNerve` is the ordinary nerve with
  the ambient object and morphism universe fixed. `hA₀small` and `hA₁small` are
  `IsSmall` nerves, and `hA₀,hA₁` are `IsKappaFiltered` nerves.
* `p₀,p₁` are the two coherent nerve diagrams. `hc₀` and `hc₁` quantify over
  every poset vertex and require `IsKappaCompact E κ` for its image.
* `hcolim` supplies colimiting cocones for both full diagrams and an equivalence edge
  in `E` between their apices. This records “equivalent colimits” without choosing
  an unproved colimit object.
* `T₀,T₁` are subsets, with `HasCardinalLT` hypotheses. The conclusion supplies
  subsets `B₀,B₁`, inclusions `Tᵢ ⊆ Bᵢ`, `HasCardinalLT Bᵢ κ`, and
  `IsFiniteFilteredSubset Bᵢ`; the latter quantifies over finite subsets and includes
  the empty subset. `RestrictedColimitsEquivalent` supplies colimiting cocones for
  both restricted diagrams and an equivalence edge between their apices.

The item module reuses the existing `SSet.Presentability.posetNerve` declaration and
adds its public quasicategory instance, then defines `subsetInclusion`,
`restrictDiagram`, `IsFiniteFilteredSubset`, and `RestrictedColimitsEquivalent`. These
use the dependency module's `SSet.Enhanced.coconeCategory`, `IsColimiting`, `hocolim`,
and `IsEquivalenceEdge`; no private copy of those notions is introduced.

## Dependency declarations used

* `Sheaf.CategoryTheory.PresentableInfinityCategory`, declarations
  `SSet.Presentability.IsSmall`, `IsKappaSmall`, `IsKappaFiltered`,
  `IsEssentiallySmall`, `IsLocallySmall`, `HasSmallKappaFilteredColimits`,
  `IsKappaCompact`, `IsKappaAccessible`, `IsAccessible`, `HasSmallColimits`,
  `IsPresentable`, and `PreservesColimitsIn`.
* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations
  `SSet.Enhanced.coconeCategory`, `IsColimiting`, `hocolim`, and
  `IsEquivalenceEdge` (through the recorded dependency module above).
* `Sheaf.CategoryTheory.AccessibleIndColimitExtension`, the existing
  `SSet.Presentability.posetNerve` declaration reused by this delivery.

## Edge cases checked

The finite-filtered predicate explicitly quantifies over all finite subsets, so the
empty subset forces a witness. The original `IsKappaFiltered` predicate likewise
includes the empty simplicial set. The conclusion allows empty `Tᵢ` and repeated
indices because it only requires subset inclusions and filtered-subset predicates.
The statement does not identify either restricted colimit with the original total
colimit; it only supplies the equivalence between the two restricted colimits.
The ambient and small universes are kept separate (`u` for the cardinal and `v` for
simplicial sets and posets), and cardinality uses `HasCardinalLT` so cross-universe
subsets are represented without an equality assumption.

## Searches

* `msearch.py ... leanfinder "common refinement of two filtered presentations by compact objects in an infinity category"` returned only ordinary-category `ColimitPresentation` and `IsCardinalPresentable` declarations; no coherent infinity-category refinement theorem.
* `msearch.py ... loogle "CategoryTheory.IsCardinalPresentable, CategoryTheory.Limits.ColimitPresentation"` returned one ordinary-category `ColimitPresentation.isCardinalPresentable` result, not this statement.
* `msearch.py ... grep "refin|compact|filtered" AlgebraicTopology/Quasicategory` returned no hits.
* `rg` over `WeilConjectures/` and project `lean/Sheaf` found no declaration of this lemma. It did find the existing project module `Sheaf.CategoryTheory.PresentableInfinityCategory`, which exactly supplies the dependency notions and is recorded as `existing: true` on the dependency node.
* `grep -rn "lem-coef-filtered-presentation-common-refinement" WeilConjectures` found no upstream declaration.

The item statement is not marked `STATEMENT-DISPUTED`.

## Second reading by Q57

I read the node statement, its HTT source place (Lemma the project server, printed pp. 478--480),
the dependency declarations, and the complete Lean file item by item.

* The ambient object is `E : SSet.{v}` with `[Quasicategory E]`; `hE` is exactly
  `IsLocallySmall.{u,v} E`.
* `hEcolim` quantifies over every `I : SSet.{v}`, quasicategory instance, `IsSmall`,
  cardinal `κ'`, `@IsKappaFiltered`, and diagram, and returns an
  `Enhanced.IsColimiting` cocone. This is the node's all-small-filtered-colimits
  hypothesis, with no extra regularity or nonemptiness assumption.
* `κ : Cardinal.{u}` has `Cardinal.aleph0 < κ` and `κ.IsRegular`, exactly the
  uncountable regular cardinal hypothesis.
* `A₀` and `A₁` are `Type v` with `PartialOrder`; their nerves are the existing
  `SSet.Presentability.posetNerve A inferInstance` declaration from
  `Sheaf.CategoryTheory.AccessibleIndColimitExtension`. `hA₀small` and `hA₁small`
  are `IsSmall`, and `hA₀` and `hA₁` are `IsKappaFiltered`, as required.
* `p₀` and `p₁` have the two nerve-to-`E` diagram types. `hc₀` and `hc₁` quantify
  over every vertex and state `IsKappaCompact` of the corresponding image.
* `hcolim` supplies colimiting cocones for both diagrams and an edge whose endpoints
  are their `Enhanced.hocolim` apices, with `Enhanced.IsEquivalenceEdge`; it does
  not identify either apex by definitional equality or assert a chosen common
  colimit object.
* `T₀,T₁` are sets with `HasCardinalLT`; the conclusion gives `B₀,B₁`, both
  inclusions, both cardinal bounds, both `IsFiniteFilteredSubset` predicates, and
  `RestrictedColimitsEquivalent`. The latter supplies colimiting restricted
  cocones and an equivalence edge between the two restricted apices. Its finite
  subset quantifier includes the empty subset.

The source and node do not impose a nonempty index set, a zero object, a terminal
poset, or a characteristic condition. Empty `Tᵢ` are allowed; the empty finite
subset is covered by `IsFiniteFilteredSubset`; repeated indices are allowed; and
`κ = ℵ₀` is correctly excluded by `Cardinal.aleph0 < κ`. The object/cardinal
universes remain separate (`v` and `u`) throughout.

The first reading exposed one H4 mismatch: this file had redeclared
`SSet.Presentability.posetNerve`, while the landed node
`lem-coef-accessible-ind-colimit-extension` already declares that notion. I removed
the duplicate abbreviation and its duplicate instance, imported the existing module,
used `posetNerve A inferInstance` everywhere, added the existing node to `stmt_deps`,
and supplied the needed public quasicategory instance
`filteredPosetNerveQuasicategory`. The helper definitions depending on the existing
noncomputable nerve are now explicitly `noncomputable`. No mathematical hypothesis or
conclusion changed. The node's `lean.statement` was updated verbatim to the repaired
signature.

The remaining helpers (`subsetInclusion`, `restrictDiagram`,
`IsFiniteFilteredSubset`, and `RestrictedColimitsEquivalent`) are distinct notions
needed to render the node and use the recorded `Enhanced` cocone declarations; no
private duplicate of a dependency notion remains. The theorem proof is still only
`sorry`, with its source and blueprint docstring. Searches included LeanFinder for
filtered poset nerve/common-refinement statements, Loogle for
`SSet.Presentability.posetNerve`, `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`,
and direct reading of `AccessibleIndColimitExtension.lean`; Mathlib supplied only the
ordinary `CategoryTheory.nerve` and `CategoryTheory.Nerve.quasicategory`, while the
existing project declaration supplied the exact reusable helper. No upstream theorem
for this statement exists.

`scompile.py` was rerun after the repair and compiled the file cleanly; no diagnostics
remain beyond the permitted postponed proof.

## Earlier second reading (a previous round; superseded)

I reread the current item statement, the two recorded dependency declarations, and the complete Lean signature. The alternating filtered-subset conclusion preserves both cardinal bounds, contains both input subsets, includes the empty finite-subset case, and compares only the two restricted colimits. The separate object and morphism universes are retained throughout, and no statement correction or dispute was found.

## Maintainer review fix (cc reviewer, 2026-10-17)

`hEcolim` quantified over every `κ' : Cardinal.{u}` without regularity. Since
`IsKappaSmall 0 K` is false for every `K`, `IsKappaFiltered 0 I` holds for every `I`, so the
hypothesis demanded colimits of all small quasicategory-indexed diagrams, which is stronger
than the node's "admitting all small filtered colimits" (H3). It is replaced by the
dependency's own predicate `HasSmallKappaFilteredColimits.{u, v} E Cardinal.aleph0`
(filtered = `ℵ₀`-filtered; every `κ'`-filtered small quasicategory with `κ'` infinite
regular is `ℵ₀`-filtered). The theorem docstring now carries the node's six proof steps.
Nothing else changed; the file compiles cleanly per file.
