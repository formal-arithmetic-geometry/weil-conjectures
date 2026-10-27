## Worker report

The module `Sheaf.CategoryTheory.AlmostFilteredComponents` states
`CategoryTheory.exists_filtered_partition_of_span_coequalization`, with proof `sorry`.
The source is Stacks Project, Categories, Tag 002X, label
`lemma-split-into-directed`; I read its statement and proof in `categories.tex`,
lines 2451–2475. No definitions, new nodes, dependency repairs, or statement
corrections are needed. The item's original fields are preserved except `lean`.

Clause-by-clause correspondence:

- Size convention and small category: explicit `universe u`, `(I : Type u)` and
  `[SmallCategory I]`. The index `J : Type u` and its subsets stay in the same
  chosen small universe. No nonempty ambient-category hypothesis is imposed.
- Hypothesis (a): `hspan` quantifies over all objects `w x y`, all arrows
  `a : w ⟶ x` and `b : w ⟶ y`, and supplies `z`, `c : x ⟶ z`, `d : y ⟶ z`
  with `a ≫ c = b ≫ d`. Lean's composition order is the source's
  `c ∘ a = d ∘ b`.
- Hypothesis (b): `hparallel` quantifies over all parallel arrows `a b : x ⟶ y`
  and supplies `z`, `c : y ⟶ z` with `a ≫ c = b ≫ c`, exactly `c ∘ a = c ∘ b`.
- A small set of indices and subsets of the object set:
  `∃ (J : Type u) (S : J → Set I)`.
- A partition of all objects: `∀ x : I, ∃! j : J, x ∈ S j` expresses exhaustive
  coverage and disjointness, with literal object membership, not just equivalence
  of categories.
- Each full subcategory is filtered:
  `∀ j : J, IsFiltered (ObjectProperty.FullSubcategory (fun x : I ↦ x ∈ S j))`.
  `FullSubcategory` uses all ambient morphisms between the selected objects with
  inherited identities/composition. `IsFiltered.nonempty` asserts nonemptiness
  of every part, `IsFilteredOrEmpty.cocone_objs` asserts a common target within
  that full subcategory for every two of its objects, and
  `IsFilteredOrEmpty.cocone_maps` coequalizes every parallel pair there. No
  `IsFilteredOrEmpty` substitute loses the required nonemptiness.
- No morphism joins different parts: the last clause says that for every
  `j k`, objects `x ∈ S j`, `y ∈ S k`, and arrow `x ⟶ y`, one has `j = k`.
  All ordered pairs are quantified, so both possible arrow directions are covered.
- Empty category allowed, with empty index set: there is no `Nonempty I` or
  `Nonempty J` assumption. If `I` is empty, each indexed filtered full subcategory
  would provide an object of `I`, so the conclusion forces `J` empty. Conversely
  the empty type `J` and its empty family satisfy the conclusion for empty `I`.

Dependency declarations read and used:

- `def-weil-size-convention` is explicitly recorded as a metatheoretic convention,
  with no declaration or module. Its prescribed universe binders are used directly.
- `def-weil-pbc-category-colimit` records Mathlib's
  `CategoryTheory.IsFiltered`; its full signature, docstring, and fields were read
  in `Mathlib.CategoryTheory.Filtered.Basic`. The module is publicly imported.
  The dependency's recorded module `Mathlib.CategoryTheory.Limits.HasLimits`
  is also publicly imported, as required for recorded dependencies; its
  `colimit` and `colimit.desc` are not needed in this particular conclusion.
  The related `Cocone`/`IsColimit` signatures and the generated colimit interface
  were inspected as well. There are no additional proof-only dependency modules:
  both proof dependencies are these same statement dependencies.
- The standard full subcategory is
  `CategoryTheory.ObjectProperty.FullSubcategory` from
  `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`; it is reused unchanged.

Edge cases checked mathematically before writing:

- Empty category: vacuous hypotheses, empty partition; no accidental filteredness
  hypothesis on all of `I`.
- Discrete category with two objects: hypotheses hold and the two singleton
  parts work; the statement does not incorrectly require a common target across
  different components.
- One-object category of a nontrivial group: hypothesis (b) fails by cancellation,
  so no false filteredness claim is made.
- One-object category of the monoid `{1,e}`, with `e²=e`: both conditions hold
  and the single full subcategory is filtered.
- A span with no common target fails hypothesis (a). A category with terminal
  object satisfies both hypotheses and has the expected single filtered part.
- An arbitrarily large small universe is admitted by polymorphism in `u`;
  no fixed finite/countable or base-universe restriction is imposed.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`, query "A small category with commuting cocones for
  spans and coequalization of parallel arrows is a disjoint union of filtered
  full subcategories": eight hits, including `IsFiltered.span`, `IsFiltered`,
  `IsFilteredOrEmpty`, `cocone_objs`, `cocone_maps`, and the special presentation
  instance `instIsFilteredI`. None states the partition theorem.
- `msearch.py ... leansearch`, query "A category with commuting cocones on spans
  and coequalizing morphisms for parallel pairs has filtered connected components":
  eight hits, including `ConnectedComponents`, `IsFiltered.isConnected`,
  `IsFiltered.of_cocone_nonempty`, and `IsFiltered.span`. None is the statement.
- `msearch.py ... loogle`, query `"IsFilteredOrEmpty"`: twelve hits for the class,
  its opposite/equivalence/product forms and related instances, no decomposition.
- `msearch.py ... grep`, query
  `IsFiltered.*Connected|Connected.*IsFiltered|component.*filtered|filtered.*component`,
  subdirectory `CategoryTheory`: twelve hits, all reverse filtered-to-connected
  results or their uses, none giving filtered components from the two hypotheses.
- Read `Mathlib.CategoryTheory.ConnectedComponents` and
  `Mathlib.CategoryTheory.Filtered.Connected`: `Decomposed` and `decomposedEquiv`
  give connected full subcategories for arbitrary categories but do not establish
  their filteredness under the present hypotheses. `IsFiltered.isConnected` is
  the reverse direction. `IsFilteredOrEmpty` would incorrectly require a common
  target even across distinct components.
- `rg -n` over Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the proposed declaration and module names:
  no existing declaration or module.
- `rg -n` over `lean/WeilConjectures`, `lean/Sheaf`, and the upstream names for
  `almost.?[Ff]iltered|[Ff]iltered.*[Cc]omponent|[Cc]omponent.*[Ff]iltered|split.into.directed|002X`:
  no exact theorem; unrelated filtered constructions and downstream docstring
  references only. `grep -rn 'lem-sfb-almost-filtered-components'
  lean/WeilConjectures` found no attachment.

Validation: `scompile.py Q157 lem-sfb-almost-filtered-components` compiled both
sandbox and library forms cleanly (1.2 s and 1.4 s respectively), with no warnings.
Only the theorem's proof is postponed, and its docstring carries all six DAG proof
steps, including closure of chosen targets in their equivalence classes.

No `STATEMENT-DISPUTED` issue was found. Independent review is left to the
maintainer, as the dispatch brief requires; no second worker was started.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
