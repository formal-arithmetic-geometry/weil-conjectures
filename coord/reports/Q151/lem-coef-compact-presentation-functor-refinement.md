## Worker report

Item: lem-coef-compact-presentation-functor-refinement. The module
`Sheaf.CategoryTheory.CompactPresentationFunctorRefinement` states
`SSet.Presentability.compact_presentation_functor_refinement`, with `sorry` as its only
postponed proof. Four helper declarations construct the subnerve of an inherited subset,
the filtered κ-small subsets, their good subposet, and the corresponding cover. They are
real subcomplexes, subtypes and functions; there is no choice from an existence theorem.
No statement correction, new definition node or dependency repair is needed.

Read the entire item (including all seven proof steps), both original statement dependency
nodes and their recorded source modules, and all three proof-dependency signatures and
proof docstrings. Read HTT online at the recorded Harvard URL, Lemma the project server and the proof
of Lemma the project server, especially printed p. 481 (PDF page 498). That paragraph constructs the
poset of good filtered subsets and applies the project server and the project server. The generic H form here is
exactly the elaboration already recorded in the node. The source remains online rather
than locally archived, as the inherited proof_origin records.

Hypothesis-by-hypothesis translation:

- The smaller universe is `u`; the containing universe is `max (u + 1) v`, so its size
  is not forced to equal the smaller one. `κ : Cardinal.{u}`, `hκ : aleph0 < κ`, and
  `hκreg : κ.IsRegular` express uncountable regular cardinality.
- `E F : SSet.{max (u + 1) v}` with their `Quasicategory` instances are the two infinity
  categories. `hE` and `hF` use the dependency's `IsLocallySmall`; `hEcolim` and
  `hFcolim` use its `HasSmallColimits` for all small simplicial indexing shapes.
- `H : E ⟶ F` is the coherent functor. `hH : PreservesColimitsIn H ...` tests every
  small shape and its actual mapped coherent cocone, using the recorded dependency.
- `P : F _⦋0⦌ → Prop` specifies the full subcategory by `fullSubcomplex F P`.
  `hPreplete` is closure under equivalence edges, in both directions. `hPcompact`
  makes every vertex satisfying P κ-compact. `hPcolim` says every κ-small coherent
  diagram with its vertices in P has every ambient colimiting apex in P. It also
  includes the empty shape; no nonempty-shape restriction is imposed.
- `A` has its inherited ordinary partial order and `[Small.{u} A]`. `hA` is exactly
  `IsKappaFiltered κ (nerve A)`, using the quasicategorical convention from the
  recorded definition, including the empty test diagram. `q : nerve A ⟶ E` is the
  supplied diagram; `hq` and `hHq` respectively assert κ-compactness of q(a) and Hq(a)
  for every vertex `ComposableArrows.mk₀ a`.
- `x` is the supplied coherent cocone on q and `hx : IsColimiting q x`; its actual
  apex is `x.1.1`. This bundles the named object and the original colimit cocone.
- `J` has its smallness and partial order, and `hJ` is its κ-filtered nerve.
  `r : nerve J ⟶ (fullSubcomplex F P).toSSet` literally takes values in P. The
  cocone `y` and `hy` are on its inclusion into F. `heq` is an equivalence edge from
  its colimit apex to `H.app _ x.1.1`. No equality of independently chosen colimits
  or arbitrary unrelated equivalence is assumed.
- `compactPartialSubsets κ A` consists of exactly the subsets of cardinality <κ
  satisfying the existing `IsFiniteFilteredSubset`; its empty finite-subset test
  forces nonemptiness. The full subcomplex `partialSubsetNerve b` consists exactly
  of chains in b and is canonically N(b), with the inherited order and inclusion.
- `t` is an arbitrary supplied choice of cocone for each such subset, and `ht`
  says each of these very cocones is colimiting. Its apex is `(t b).1.1 = x_b`.
  No colimiting cocones are chosen by the module.

Conclusion-by-conclusion translation:

- `goodCompactPartialSubsets H P q t` is the subtype of all these partial subsets
  with `P (H.app _ (t b).1.1)`, precisely the B in the node. Both subtype orders
  inherit inclusion from `Set A`; there is no different order on B.
- The first conjunct is `Small.{u} B`, the second is `IsKappaFiltered κ (nerve B)`.
  The third quantifies over every `T : Set A` with `HasCardinalLT T κ` and supplies
  `b : B` with `T ⊆ b.1.1`, including T empty.
- The existential `q' : nerve B ⟶ E` is a coherent diagram. Its first conjunct is
  the literal vertex equation `q'(b) = (t b.1).1.1`, retaining each prescribed x_b.
- `a` is a coherent transformation on the existing directed-cover incidence set.
  The two endpoint equations identify q pulled back along the shape projection
  and q' pulled back along the stage projection. The equation on every
  `directedCoverFiber` identifies its whole local coherent cocone with the
  prescribed `coconeHomotopy ... (t b.1)`. Thus it expresses assembly of the
  specified partial cocones, including their higher transition compatibilities.
- `ν` is a coherent cocone on q', `IsColimiting q' ν` is its colimit condition,
  and `ν.1.1 = x.1.1` keeps the supplied original apex x.
- The family `z` of 2-simplices on that incidence set has faces a, the pullback of
  the ν cocone, and the pullback of the original x cocone. This is compatibility
  with the original cocone in every degree and expresses the induced components,
  rather than an arbitrary map to the same apex.
- The remaining universal conjunct says every q'(b) is `IsKappaCompact E κ` and
  `P (H.app _ q'(b))`. These are precisely the two final assertions of the node.

Dependency declarations used:

- `Sheaf.CategoryTheory.PresentableInfinityCategory`: `IsLocallySmall`,
  `HasSmallColimits`, `IsKappaSmall`, `IsKappaFiltered`, `IsKappaCompact`, `IsSmall`,
  and `PreservesColimitsIn`, all in `SSet.Presentability`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`, `IsEquivalenceEdge`,
  `coconeCategory`, `IsColimiting`, all in `SSet.Enhanced`.
- `Sheaf.CategoryTheory.FilteredPresentationCommonRefinement`:
  `SSet.Presentability.IsFiniteFilteredSubset` (reused, not duplicated) and the
  non-public proof-plan theorem `exists_common_refinement` available through the
  same necessary public import.
- `Sheaf.CategoryTheory.DirectedCoverColimitAssembly`:
  `SSet.Enhanced.directedCoverIncidence`, `directedCoverToShape`,
  `directedCoverToIndex`, `directedCoverFiber`; its assembly theorem is the named
  input in proof step 6. These constructions supply statement-level coherence.
- `Sheaf.CategoryTheory.FinalIndexColimit`: `SSet.Enhanced.coconeHomotopy`, the
  existing extractor of a coherent cocone transformation. No finality hypothesis
  or theorem is introduced by using this extractor.
- `Sheaf.CategoryTheory.CompactSmallColimits` is imported without `public` for
  the proof-plan input `SSet.Presentability.isKappaCompact_of_isColimiting`.
- Mathlib supplies `nerve`, `ComposableArrows.mk₀`, inherited subset orders,
  `Small`, `HasCardinalLT`, simplicial products and simplex face maps.

The three already-landed nodes providing statement interfaces were added to stmt_deps:
lem-coef-filtered-presentation-common-refinement,
lem-coef-directed-cover-colimit-assembly, and lem-coef-infinity-final-index-colimit.
Their full stmt/proof closures have respectively 710, 208 and 139 nodes and do not reach
this item. No proof-dependency field or natural-language statement was changed.

Edge cases checked before drafting and again against the final signature:

- T empty still has a containing good subset. B nonempty follows from filteredness
  with the empty test shape; neither condition is replaced by pairwise directedness.
- The empty subset b of A is excluded by the required inherited filteredness,
  exactly as in the node. Empty finite subsets of each b are tested.
- A or J empty cannot satisfy κ-filteredness; no unrelated extra Nonempty hypothesis
  is needed. For a singleton A all indices and repeated/degenerate chains are retained.
- Empty κ-small colimits are included in hPcolim. If P is empty the r-presentation
  hypotheses are inconsistent, as expected; no bogus inhabitant is constructed.
- κ = aleph0 is correctly excluded. Uncountability bounds countably many dimensions
  of finite chains; regularity handles unions of fewer than κ partial subsets.
- Arbitrary chosen partial-colimit cocones remain universally quantified. The
  compatibility triangle refers to the supplied x, not a newly chosen total cocone.
- Universes are bound explicitly. Small A and J can be represented in the ambient
  universe without identifying it with u; Small B is a substantive conclusion.

Searches (2026-10-17, through the prescribed msearch.py wrapper):

- LeanFinder: “Regroup a compact filtered presentation along a colimit preserving
  functor of infinity categories so small partial colimits land in a closed full
  subcategory”. Eight hits, including ordinary `ColimitPresentation.bind_diag_obj`
  and ordinary filtered-category presentation lemmas. No quasicategorical theorem.
- Loogle: `"IsCardinalPresentable", "colimit"`. Twelve hits, including
  `CategoryTheory.isClosedUnderColimitsOfShape_isCardinalPresentable`; read its full
  source signature in Mathlib/CategoryTheory/Presentable/Limits.lean:199 and the
  neighboring colimit compactness statement at line 185. They use ordinary Category
  instances and set-valued Hom compactness, not the mapping-space predicate here.
- LeanSearch: “A compact filtered presentation can be regrouped along a colimit
  preserving functor so partial colimits belong to a full subcategory closed under
  small colimits”. Eight ordinary-category hits: ColimitPresentation.map,
  isColimitOfPreserves, and full-subcategory colimit closure. No exact match.
- Mathlib grep through msearch: `compact|filtered|colimit` in
  AlgebraicTopology/Quasicategory: zero hits. Read Quasicategory/Basic.lean:39:
  the primitive horn-filling predicate is not this refinement assertion.
- rg/grep in the upstream WeilConjectures tree for the item id and
  `partialColimit|goodSubset|CompactPresentation|compactPresentation`: no match.
  `dag/lean_names_upstream.json` has no declaration attached to this item.
- rg over side lean/Sheaf for partial-colimit/good-subset/refinement and assembly
  names found the three proof modules above and the reusable cocone extractor.
  Read their full signatures and docstrings; none states this generic H theorem.
- Exact-name grep for `compactPartialSubsets|goodCompactPartialSubsets|partialSubsetNerve|
  goodPartialSubsetCover` in Mathlib, upstream and lean/Sheaf found no prior declaration.

Validation: prescribed scompile.py compiled both its sandbox form and the real library
module path cleanly (2.8 s and 3.0 s), with no warnings. All Lean lines are at most 100
characters. The lean.statement field is extracted verbatim from the theorem header.

## Second reading by Q151

A second pass by the same worker reopened the original node and the completed file and
checked the translation above. The dispatcher explicitly forbids starting other agents;
the maintainer's independent delivery review remains separate. This is not represented
as an independent-worker review.

The main risk checked was loss of coherence: vertex equalities alone would not state
that the chosen partial cocones assemble or that the new cocone is induced by the original
one. The final signature has the full incidence transformation, its exact fiber equations,
and a 2-simplex family with its long face the pullback of `coconeHomotopy q x`. The global
cocone is supplied as a hypothesis and retained. Checked all three simplex face directions
against DirectedCoverColimitAssembly, and checked the local subcomplex is exactly the
full inherited subnerve. Confirmed no hypothesis asserting presentability, accessibility,
essential smallness of P, or closure under arbitrary large colimits has slipped in.
The report above matches every binder and conclusion conjunct; no mismatch remained.
