## Worker report

Reuse the existing declaration `SSet.Presentability.pointwise_compact_diagrams`
in `Sheaf.CategoryTheory.PointwiseCompactDiagrams`, at
`lean/Sheaf/CategoryTheory/PointwiseCompactDiagrams.lean:84` on `newtargets-dag`.
Group NW already supplied this exact theorem. No new theorem or notion is duplicated, and no proof is attempted. The
item's `lean` field is updated to an `existing: true` record, without a `file` field.

I read the item's full statement, five proof steps, source, dependency records,
the existing theorem's full signature and proof docstring, and the definitions
expanded below. The repair note for this item is resolved stage 1: it asks to
re-split the long proof step while keeping this statement and its Lean record.
There is no released stage-2 defect or archived interface to repair.

Source: [HTT Proposition the project server](https://people.math.harvard.edu/~lurie/papers/HTT.pdf#page=417),
printed pp.399--401 (PDF indices 416--418), opened online on 2026-10-17.
The proposition asserts compactness in the entire functor category from
vertexwise compactness on a small simplicial shape. The current node makes
its universe and local-smallness conventions explicit; the existing Lean
statement retains them all. No statement correction is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Universes U in U': the explicitly declared `universe u v` and
  `SSet.{max (u + 1) v}` for both `C` and `K` permit an arbitrary containing
  universe above `u`. They do not equate the two universes or require `C`
  itself to be small.
- Infinite regular small cardinal: `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`.
  Mathlib `Cardinal.IsRegular` includes `aleph0_le`, so infinitude is present.
- Locally small quasicategory: `(C : SSet.{max (u + 1) v}) [Quasicategory C]`
  and `(hClocal : IsLocallySmall.{u, max (u + 1) v} C)`.
  This means mapping spaces equivalent to small spaces, rather than smallness
  of the given simplicial models.
- All small κ-filtered colimits: `(hCcolim : HasSmallKappaFilteredColimits C κ)`.
  The definition quantifies over every small κ-filtered quasicategory and
  every coherent diagram, and asks for an actual colimiting cocone.
- κ-small simplicial shape: `(K : SSet.{max (u + 1) v})
  (hK : IsKappaSmall κ K)`. The predicate counts the sum of nondegenerate
  simplices over all degrees and bounds its cardinality strictly by κ.
  There is no requirement that K be a quasicategory.
- Coherent diagram: `(a : K ⟶ C)` is an actual simplicial map.
- Every vertex value compact: `(ha : ∀ k : K _⦋0⦌,
  IsKappaCompact C κ (a.app (op ⦋0⦌) k))`.
- Conclusion: `IsKappaCompact ((ihom K).obj C) κ
  (SSet.Enhanced.diagramVertex a)` uses the entire coherent functor category
  and the actual vertex associated to a. The standard Mathlib internal-hom
  quasicategory instance is supplied by the existing imports.
- Explicit preservation clause: unfolding the recorded `IsKappaCompact`
  tests every small κ-filtered quasicategory I, every F into the canonical
  universe lift of this entire functor category, and every colimiting cocone t.
  Its conclusion is `CategoryTheory.Spaces.PreservesColimit ... F t`, namely
  `Enhanced.IsColimiting (F ≫ Spaces.corepresented ...)
  (Spaces.mappedCocone (Spaces.corepresented ...) F t)`.
  `mappedCoconeData` retains the image apex and postcomposes the whole coherent
  edge via the internal-hom maps. Thus the map is the actual image cocone,
  not an arbitrary comparison or mere existence of some colimit. The further
  universe accommodates the infinity category of containing-universe spaces.
- Arbitrary target diagrams: F ranges over all diagrams valued in the entire
  functor category. No constant-diagram condition restricts F or its apex b.
- Empty K: there is no `Nonempty` hypothesis on K; ha is a universal vertex
  condition and is vacuous for the empty simplicial set. The conclusion still
  asserts compactness in its terminal functor category. The docstring's proof
  explicitly covers the empty shape, including existence of filtered colimits.

Dependency declarations read and reused through the existing module:

- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsKappaSmall`, `IsKappaFiltered`, `IsLocallySmall`,
  `HasSmallKappaFilteredColimits`, and `IsKappaCompact` (full definitions read).
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.diagramVertex`, `evaluation`, `mappingSpace`, `coconeCategory`,
  and `IsColimiting` (signatures, docstrings and construction formulas read).
  The recorded main declaration `coneCategory` and its docstring were also read.
- `Sheaf.CategoryTheory.InfinityYonedaPresheafLimits`:
  `SSet.Enhanced.YonedaLimits.infinity_yoneda_presheaf_limits`, especially its
  fourth conjunct and `PointwiseColimit`; these supply the source's objectwise
  colimit convention. Its full theorem signature and proof docstring were read.
- The compactness predicate uses `CategoryTheory.Spaces.corepresented`,
  `mappedCoconeData`, `mappedCocone`, and `PreservesColimit` from
  `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`; their signatures and
  definitions were inspected to verify the specified coherent cocone maps.

The existing module also imports all recorded proof dependencies: spine/tower
mapping descent, the arrow-morphism square, mapping excision, boundary cells
(Mathlib `SSet.relativeCellComplexOfMono`), and the spaces interchange theorem.
Its theorem remains postponed by `sorry` with the five-step proof docstring.

Edge cases checked before recording reuse: empty K (terminal functor category,
vacuous ha), a one-vertex K (the original compact object), an edge K (compact
source and target with arbitrary intervening arrow), κ = aleph0 (finite
nondegenerate simplices), and uncountable regular κ (possibly infinite-dimensional
κ-small K). Empty C is allowed when K is empty; a nonempty K has no diagram
into empty C. Filtered I is nonempty because its definition tests the empty
shape, so no invalid empty-index filtered colimit is introduced. No bound on
dimension, nonemptiness condition, accessibility assumption, or constancy
condition has been added.

Searches for reuse, performed with the prescribed Q19/item wrappers:

- `leanfinder`: “A coherent diagram on a kappa small simplicial set with kappa
  compact vertex values is kappa compact in the infinity functor category”:
  eight hits, chiefly `SSet.Finite.instIsFinitelyPresentable` and finite-simplicial
  set results. I read Mathlib `SimplicialSet/Presentable.lean`: these concern
  ordinary Hom-set finite presentability of simplicial sets, not this theorem.
- `loogle`: `IsKappaCompact, pointwise_compact_diagrams`: zero hits,
  unknown identifier `IsKappaCompact` in the Mathlib search environment.
- Mathlib `grep`, CategoryTheory: `([Pp]ointwise|[Oo]bjectwise).*[Cc]ompact|IsKappaCompact`:
  zero hits.
- `rg` in upstream `WeilConjectures` for
  `pointwise_compact_diagrams|IsKappaCompact|pointwise.*compact`, and the
  exact blueprint id: no upstream matches.
- The same conceptual/name search in the shared `lean/Sheaf` finds the exact
  `PointwiseCompactDiagrams.lean:84` statement. The other hits concern its
  consumers or broader presentability results; the existing exact statement
  is reused. No extra definition is needed. A transitive prerequisite compile repair is
  described below.

No STATEMENT-DISPUTED flag or node fault was found. Validation is performed by
`deliver2.py` through its prescribed `scompile.py` existing-declaration probe,
followed by the server preflight. The dependency repair is also compiled separately.


## Dependency modules

`lem-coef-space-valued-straightening`: the existing import closure failed at
`SpaceValuedStraightening.lean:64:7` with `lean.dependsOnNoncomputable`:
`Diagrams` uses `smallSpaces`, which is noncomputable. The exact current server
source was obtained using `scompile.py --source`. This delivery copies that
module into the sandbox and changes only `abbrev Diagrams` to
`noncomputable abbrev Diagrams`. It retains the same internal-hom construction,
all universe parameters, all statement signatures and docstrings, the entire
canonical comma-pullback interface, and the existing postponed theorem.
There is no natural-language statement change or extra hypothesis. Its copied
node changes only `lean`, with the required explanation in `lean.note`.
The dependency is in the item's transitive statement/proof prerequisite
closure, reached by the existing pointwise-colimit and descent imports.
The owning node's full statement and recorded interface were read. Its
clauses remain exactly as before: small left-fibration straightening natural
under pullback, and the same explicit ordinary-base adjunction, Kan counit
weak equivalence, and natural comparison for every indicated replacement.
All endpoint, empty-base, and non-Kan ordinary-diagram cases are preserved
because this is only a code-generation annotation on an unchanged definition.
No extra theorem or sorry is introduced. This is the authorized §1(B)
repair of an unusable recorded dependency; a live library file was never edited.

Dependency path verified from the DAG:
`lem-coef-pointwise-compact-diagrams` →
`lem-coef-infinity-yoneda-presheaf-limits` → `def-coef-complete-algebroid` →
`lem-coef-kan-relative-nerve-left-fibration` → `lem-coef-space-valued-straightening`.
The prescribed `scompile.py Q19 lem-coef-pointwise-compact-diagrams` invocation
for the repaired module passed both sandbox and library checks without errors
or warnings (2.2 s and 2.5 s respectively).

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
