## Worker report

Module `Sheaf.AlgebraicTopology.MarkedHomotopyPrecomposition` states
`SSet.Marked.Over.marked_homotopy_precomposition`, with its sole proof `sorry`.
The helper `mapFlatVertex` gives an ordinary relative marked map as a flat mapping vertex,
by the actual projection from its product with the point. Its data are fully constructed.
All universes and variables are explicit (`autoImplicit false`).

Hypothesis and clause correspondence:

- The small simplicial base is `{S : SSet.{u}}`; `U V W : SSet.Marked.Over S` are
  marked simplicial sets equipped with arbitrary underlying maps to S. The slice is over
  `sharp S`, so its marking-preservation condition imposes no condition on these base maps.
  All data and mapping objects use the same containing universe u.
- Marked maps over S are `h₀ h₁ : U ⟶ V`; the flat-parameter marked relative homotopy
  is `H : (productLeft U).obj (flat Δ[1]) ⟶ V`. The base ignores the parameter by the
  definition of `productLeft`.
- The `endpoints` hypothesis ranges over both `i : Fin 2`, every simplicial degree and
  every source simplex. Its equality identifies H at the constant simplex i with h_i.
  This is precisely the two given endpoint maps, without extra hypotheses.
- `mapFlat` and `mapSharp` are the existing relative mapping simplicial sets. Their
  n-simplices are the slice morphisms from U times the flat or sharp standard n-simplex;
  their operators are precomposition on the parameter. No alternative definition is made.
- `∃ Φ : mapFlat V W ⊗ Δ[1] ⟶ mapFlat U W` asserts the required simplicial map.
  The first conjunct quantifies independently over parameter degree n, source degree m,
  every relative marked a, every interval simplex τ, every x and every v. Its equation is
  exactly `a(H(x,τ(v)),v)`, using `yonedaEquiv.symm τ` to realize τ as a simplex map.
  This formula determines Φ on every simplex; the existential is not an arbitrary map.
- The second conjunct identifies each endpoint in every degree with `productMapLeft h_i
  (flat (stdSimplex.obj n.unop)) ≫ a`. These are the simplicial precomposition maps,
  with their given restriction operators, expressed by their degreewise action.
- The third conjunct evaluates Φ on `(σ 0 (mapFlatVertex a), yonedaEquiv (𝟙 Δ[1]))`.
  This is its edge at vertex a. Equality of the underlying maps with `H.left.val ≫ a.left.val`
  says that it is represented by a after H.
- The last implication assumes exactly the additional sharp-parameter marking condition:
  for every marked e of U and every interval edge d, `H(e,d)` is marked in V.
  For every vertex map a it provides `b : (mapSharp U W) _⦋1⦌` with the same underlying
  simplicial map as the component. Thus the component belongs to the sharp mapping subset;
  b already includes the required relative base equation.
- No `Quasicategory`, `KanComplex`, fibrancy, invertibility or inhabitedness hypothesis
  occurs. All flat simplices a are retained, including noninvertible parameter edges.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: Mathlib's `SSet`, `stdSimplex`,
  degreewise tensor products and simplicial operators, as used by the dependency module.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked`, `Hom`,
  `markedCategory`, `flat`, `sharp`, `product`, `productMap`, and `flatSimplex`/`sharpSimplex`.
  Their signatures and docstrings were read in full.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`: `SSet.Marked.Over`,
  `Over.productLeft`, `Over.mapFlat`, `Over.mapSharp`, and `Over.productMapLeft`.
  Its existing node `lem-coef-marked-relative-cartesian-model` is added to stmt_deps
  to cite the already landed owning declaration. This introduces no new notion or theorem
  dependency assumption: only its explicit relative mapping constructions are used.

Source: read the official IAS HTT PDF in memory using urllib and pdftotext, printed
pp. 154–155, Section 3.1.3 immediately before Remark the project server. The flat/sharp mapping
properties and relative restriction to maps over S agree with the node. The six-step
coordinate verification is agent-formulated, as the node explicitly records, and the
entire plan is in the theorem docstring. No statement correction or disputed statement.

Edge cases checked before writing:

- U empty: formulas are vacuous in x, and all component maps have the unique empty source.
- V or W empty: no existence of a vertex or map is assumed; universal quantifiers can be empty.
- n=0, m=0, and degenerate τ: the formula still applies, with the endpoint equations
  specializing to ordinary precomposition.
- Constant H: the resulting homotopy is constant at the corresponding precomposition.
- Non-sharp H, e.g. the identity on the flat interval with a point source: no sharp component
  is claimed unless the additional marking implication is supplied.
- Different flat versus sharp parameter markings are retained; no invertibility condition
  is imposed on an arbitrary simplex a. No constraint on characteristics is relevant.

Searches (authentic service output is also in sandbox searches.jsonl):

- msearch.py leanfinder, query “A marked homotopy over a simplicial base induces parameterized
  precomposition on flat relative mapping simplicial sets”: 8 hits, including
  `SSet.RelativeMorphism.Homotopy.precomp` and `precomp_h`. Read their source signatures
  and docstrings in `Mathlib/AlgebraicTopology/SimplicialSet/RelativeMorphism.lean`:
  these concern unmarked relative pairs, not whole relative marked mapping objects.
- msearch.py leansearch, query “Marked simplicial homotopy induces precomposition on relative
  internal hom with sharp components”: 8 hits, on relative pairs, right homotopy classes,
  and Dold–Kan morphism components. No match for this statement.
- msearch.py loogle, query `SSet.RelativeMorphism.Homotopy.precomp`: 2 hits, the above
  `precomp` and `precomp_h`, with the same mismatch.
- msearch.py grep, query `MarkedSSet|MarkedSimplicial|mapFlat|homotopyPrecomposition`:
  0 Mathlib hits.
- rg in upstream WeilConjectures for `markedHomotopyPre|homotopyPrecomposition|MapFlat|
  mapFlat|MarkedSSet`: no hits. The exact node-id grep also returned no hits.
- rg in lean/Sheaf for `mapFlatPre|mapFlat.*[Hh]omotopy|precomp.*[Ff]lat|
  homotopy.*[Pp]recomp` found the ordinary unmarked `Enhanced.homotopyPrecomposition` in
  `HomotopyPrecompositionEquivalence.lean`. Read that construction and its theorem:
  it assumes unmarked objects and has an equivalence conclusion under quasicategory
  and fixed-vertex assumptions, so it is neither the relative marked statement nor
  the sharp-component assertion. Existing marked mapFlat/mapSharp were found and reused.
- Exact declaration-name rg for `mapFlatVertex|marked_homotopy_precomposition` in Mathlib,
  upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no collisions.

Validation: scompile.py compiled the delivered file separately in sandbox and library form
without errors or warnings (2.5 seconds each). No global build or direct git command was run.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
