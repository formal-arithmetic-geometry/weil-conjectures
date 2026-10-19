## Worker report

Item: `lem-coef-algebroid-ff-simplicial-realization`, group Q52, 2026-10-17.
The module `Sheaf.CategoryTheory.AlgebroidFullyFaithfulRealization` states
`SSet.Enhanced.Algebroid.fullyFaithful_simplicial_realization`. Its only postponed
proof is this theorem, with the node's seven-step natural-language proof in its
docstring. The two helpers have explicit data: `objectSpaceProjection` remembers
the space parameter of every total-algebroid simplex, and `realizationLeg`
evaluates the actual coherent cocone cylinder at a specified indexing vertex.

The source read online was Gepner--Haugseng,
[arXiv:1312.3178v4](https://arxiv.org/html/1312.3178v4), Theorem 5.6.2,
specifically the paragraphs after the pointwise presheaf colimit and the two
Cartesian squares, using Theorem 4.5.3. The node generalizes those paragraphs to
any fully faithful simplicial diagram. No completeness or essential-surjectivity
hypothesis was borrowed from the special completion diagram in that proof.

Hypotheses and clauses are represented as follows:

- The presentably monoidal coefficient infinity category is a quasicategory
  `E` with its operadic projection `p` and
  `hp : IsPresentablyMonoidal.{u, v} p`. This is exactly the predicate from the
  complete-algebroid dependency, including presentability of the underlying
  category and preservation of small colimits by both tensor variables.
- Algebroids are the dependency's `total.{u, v} p`, not the full subcategory of
  complete algebroids. Each object space is small in universe `u`; the ambient
  simplicial sets live in `max (u + 1) v`, with no equality imposed on universes.
- The small coherent simplicial diagram is
  `D : uliftFunctor.obj (nerve SimplexCategoryᵒᵖ) ⟶ total p`. A simplicial map
  from this nerve retains all chains, faces and degeneracies, including the
  higher simplices of the given diagram. The indexing category itself is small.
- Every structure map is fully faithful through `hD`, which quantifies over
  every pair of degrees `m n` and every `f : m ⟶ n`, and applies the inherited
  `Algebroid.IsFullyFaithful` to `D`'s actual edge on `ComposableArrows.mk₁ f`.
- Existence of `C = |C_bullet|` is the first conjunct
  `∃ c : (coconeCategory D) _⦋0⦌, IsColimiting D c`. The apex of `c` is `c.1.1`.
  This is the recorded coherent universal property, not an ordinary colimit.
- `X_n = U(C_n)` is the composite `D ≫ objectSpaceProjection p`. The helper's
  value is literally `a.val.space`, the object's universal-family parameter.
- `U(C) ≃ |X_bullet|`, compatibly with all cocone maps, is
  `IsColimiting (D ≫ objectSpaceProjection p)
  (CategoryTheory.Spaces.mappedCocone (objectSpaceProjection p) D c)` for every
  colimiting `c`. The mapped cocone has apex `U(c.1.1)` and postcomposes the whole
  transformation of `c`, in every simplicial degree. Thus it asserts that this
  very apex and these very coherent legs realize `X_bullet`. The colimit
  universal property gives the equivalence with any chosen realization of
  `X_bullet`, including its cocone compatibility; no arbitrary comparison map
  or unconnected equivalence has been substituted.
- For every `n` and `x,y ∈ X_n`, the induced mapping-object edge is an equivalence
  in `V`: this is exactly `IsFullyFaithful (realizationLeg D c n)`. Unfolding the
  dependency's predicate quantifies over every ordered pair and every lift along
  the object-space edge, and tests the equivalence of the value of that edge at
  the relative-nerve label `[1]`. This is the canonical mapping-object arrow
  `C_n(x,y) → C(xbar,ybar)`, not an equivalence of ordinary Hom sets. The same
  clause states the final conclusion that all cocone maps are fully faithful.
- No assumption or conclusion of essential surjectivity is present. In
  particular the theorem does not require nonempty object spaces, discreteness,
  completeness, a fixed object set, or strict enriched functors.

The universal quantification over all colimiting cocones makes the statement
independent of a chosen representative of geometric realization. The cylinder
evaluation defining `realizationLeg` is the pair consisting of the degenerate
index edge at degree `n` and the identity edge of `Δ[1]`; hence its source is
`D(n)` and its target is the supplied cocone's apex.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: `total`, `TotalSimplex.space`,
  `universalFamily`, `IsPresentablyMonoidal`, `pairParameter`, `homObject`,
  `IsFullyFaithful`, together with its actual relative-nerve construction.
  The recorded primary declaration `completeCategory` and its docstring were
  also read; this item concerns `total`, not `completeCategory`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `coconeCategory`, `IsColimiting`,
  the comma-category and mapping-space definitions determining those predicates.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`:
  `CategoryTheory.Spaces.mappedCocone`, `mappedCoconeData`, `mappedCoconeData_mem`.
  Its full signature and endpoint characterization were read. The construction
  retains precisely the original apex and postcomposed coherent transformation.
- `Sheaf.CategoryTheory.FinalIndexColimit`: `coconeHomotopy`, with its full
  signature and cylinder convention. Only this helper is used, not the theorem
  about final indices.
- The already stated proof dependency `Sheaf.CategoryTheory.SpaceGeometricDescent`
  is imported without `public`, as required for the later proof. The other two
  proof dependencies `def-coef-segal-presheaf-localization` and
  `lem-coef-algebroid-segal-localization-model` have no recorded Lean modules in
  the current DAG, so no import is available for them. They are used in the
  natural-language proof plan and are not needed to type the statement.

The item's `stmt_deps` gains the three already recorded nodes for coherent
colimits, mapped cocones, and the cocone cylinder. There are no new nodes and no
dependency modules, and the natural-language statement and proof are unchanged.
The two new helpers belong to the item itself and are listed in
`lean.declarations`; neither duplicates an independently defined notion.

Edge cases checked before writing:

- If `X_0` is empty, maps of the simplicial diagram to degree zero force each
  `X_n` empty. The resulting realization is empty on objects, and the pairwise
  full-faithfulness tests have no object pairs. The statement assumes no point.
- Constant diagrams, including the empty algebroid, give the original object
  up to equivalence; the theorem requires every colimiting representative to
  have the specified projection and full-faithfulness property.
- Degree zero is included by `n : SimplexCategoryᵒᵖ`, and identities and
  degeneracies are included among the maps quantified by `hD`.
- Non-discrete object spaces and arbitrary coherent higher simplices are
  retained in `total`, `D`, `coconeCategory` and `mappedCocone`.
- The independent ambient universe `v` remains arbitrary. The indexing nerve
  is lifted to `max (u + 1) v`, not restricted by an equality with `u`.

Searches for existing declarations:

- `msearch.py ... leanfinder "Geometric realization of a coherent simplicial
  diagram of fully faithful enriched infinity algebroids preserves object spaces
  and mapping objects"`: eight hits including `CategoryTheory.SimplicialNerve`,
  simplicial thickening, simplicial enrichment and ordinary nerves. None states
  enriched algebroid realization or this mapping-object preservation assertion.
- `msearch.py ... loogle "SSet.SimplicialNerve, FullyFaithful, colimit"`: no hits;
  the service reported unknown identifier `SSet.SimplicialNerve`.
- `msearch.py ... grep
  "algebroid|SegalPresheaf|fullyFaithful.*realization|realization.*fullyFaithful"`:
  only the unrelated Lie-Rinehart algebra comment in Mathlib.
- `rg` for `Algebroid|algebroid|PresentablyMonoidal` in `lean/Sheaf` and the
  upstream `WeilConjectures` source found the existing complete-algebroid module,
  which is used. A search for the item's id in upstream sources and the upstream
  declaration-name index found no declaration.
- `rg` for object-space projections and fully faithful realization names in
  Mathlib's CategoryTheory tree, the upstream source and `lean/Sheaf` found no
  duplicate projection or theorem. Existing total-projection names concerned
  bicomplexes. Generic cocone-map searches found the reusable `mappedCocone`;
  specialized weighted-cocone legs and coherent Cat-infinity legs do not have
  this total-algebroid interface. The cylinder is reused from the recorded
  `coconeHomotopy` instead of redefining it.

There is no statement dispute or source-based correction.

Validation: `scompile.py Q52 lem-coef-algebroid-ff-simplicial-realization` compiled
the delivered module both as a sandbox and at its library module name, cleanly
with no errors or warnings (16.5 s and 18.1 s respectively). The prescribed
`deliver2.py` dry run is the final preflight; no library build is run.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
