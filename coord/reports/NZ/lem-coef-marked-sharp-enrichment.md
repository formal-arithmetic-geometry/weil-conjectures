## Worker report

The module `Sheaf.AlgebraicTopology.MarkedSharpEnrichment` states
`SSet.Marked.marked_sharp_enrichment`, with its sole theorem proof postponed by
`sorry`. No definition is duplicated and no new data is chosen from an existence
statement. The existential witnesses are part of the theorem conclusion and are
specified by coordinate normalizations. The node is unchanged apart from `lean`.

Hypothesis and clause correspondence:

- Arbitrary marked simplicial sets are `X Y Z : SSet.Marked.{u}`, without
  fibrancy or nonemptiness hypotheses. The markings, marked morphisms, products,
  `flat`, `sharp` and `internalHom` are the existing dependency constructions.
- The sharp mapping set and its restrictions are exactly `mapSharp X Y`, defined
  in the imported source as `(sharpSimplex ⋙ productLeft X).op ⋙ yoneda.obj Y`.
  Thus its degree n is the required marked-map set, and its operators are
  precomposition with the sharp simplex restriction maps.
- The existential `E : SimplicialCategory Marked.{u}` provides associativity,
  units, simplicial composition and the ordinary-category compatibility. The
  isomorphisms `i X Y : E.Hom X Y ≅ mapSharp X Y` identify its hom objects with
  the actual sharp mapping objects, rather than an unrelated enrichment.
- The first conjunct normalizes `E.homEquiv f` after `i` on every degree and
  every simplex: its value at `(x,a)` is `f(x)`. In degree zero this identifies
  vertices with the actual marked morphisms; for `f = 𝟙 X` it is the constant
  identity family. `E.homEquiv` is bijective, and the maps from the simplicial
  unit identify with vertices by Mathlib `SSet.unitHomEquiv`.
- The second conjunct normalizes enriched composition after `i`: at `(x,a)` it
  is exactly `g(f(x,a),a)`. Together with the enriched laws this states the
  specified associative, unital diagonal-parameter composition.
- `T X Y K` is the first requested simplicial isomorphism, from
  `mapSharp (product X (sharp K)) Y` to `(ihom K).obj (mapSharp X Y)`.
  The latter is Mathlib's existing unmarked simplicial function object. Its
  `HomObj` presentation is the usual natural-family encoding of maps from
  `K × Δ[n]`, not a new notion of Fun.
- `C X Y K` is the second requested simplicial isomorphism, from that same
  function object to `mapSharp X (internalHom (sharp K) Y)`. The objects are
  therefore exactly the specified tensor and cotensor.
- The third conjunct specifies the tensor transpose on all coordinates: if
  `a : [m] → [n]`, `s : [r] → [m]`, its value at `k`, then `(x,s)`, is
  `f_r((x,s* k),s ≫ a)`. This determines the entire map, including its inverse
  since `T` is an isomorphism; it is the node's currying bijection.
- The fourth conjunct specifies the composite of the two comparisons on all
  coordinates. Its value first at `(x,a)` and then `(k,b)` is
  `f_r((b* x,k),b ≫ a)`. This is precisely the same three-factor marked map
  with the K and simplex factors interchanged, followed by the dependency's
  marked internal-Hom transpose. Hence `C` is the prescribed cotensor
  comparison rather than an arbitrary isomorphism.
- The final two conjuncts state simultaneous naturality for arbitrary
  `a : X' → X`, `b : Y → Y'`, `k : K' → K`. They use the existing
  `productMap`, `sharpMap`, `mapSharpPre`, `mapSharpPost`, `internalHomMap`, and
  Mathlib `MonoidalClosed.pre` / `ihom.map`.
- Compatibility with restriction is built into all the simplicial morphisms
  and isomorphisms. Compatibility with composition and identities is also
  specified by the full coordinate normalizations: transposing the second
  conjunct evaluates to `g(f(x,k,t),t)`, and transposing the first with an
  identity evaluates to the unchanged value. The comparisons are uniquely
  determined pointwise; this rules out unrelated natural automorphisms of
  any of the mapping objects.
- All sets, function objects and marked objects have the same arbitrary
  universe `u`. Only the type containing all such objects is in `u+1`; none
  of the constructions changes the input universe. `autoImplicit false`
  forbids unbound variables; `u` is declared explicitly.

Dependency declarations used:

- `Sheaf.AlgebraicTopology.MarkedInternalHom`:
  `SSet.Marked.marked_internal_hom`, `SSet.Marked.internalHomMap`.
  I read the entire declaration, docstring, evaluation formula, inverse
  transpose formula, functoriality and marking test.
- Its public import `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `markedCategory`, `Hom`, `flat`, `sharp`, `product`,
  `productMap`, `sharpMap`, `sharpSimplex`, `productLeft`, `mapSharp`,
  `internalHom`, `mapSharpPre`, `mapSharpPost`. I read their full definitions.
  The downstream model-structure theorem is not invoked.
- Mathlib `AlgebraicTopology.SimplicialCategory.Basic`:
  `CategoryTheory.SimplicialCategory`; its underlying
  `EnrichedOrdinaryCategory` includes associative/unital composition and
  `homEquiv` compatible with ordinary composition.
- Mathlib `CategoryTheory.Monoidal.Closed.FunctorToTypes` and
  `CategoryTheory.Functor.FunctorHom`: the existing closed structure on
  simplicial sets, with `Functor.HomObj`, `functorHom`, and the evaluation
  coordinate presentation. Mathlib `CategoryTheory.Monoidal.Closed.Basic`:
  `CategoryTheory.ihom`, `CategoryTheory.MonoidalClosed.pre`.

Edge cases were checked before writing. For empty K the tensor is empty, the
cotensor is the terminal marked point, and all three mapping objects in the
comparison are terminal. For K the point the two objects reduce up to their
canonical isomorphisms to X and Y. For empty X all sharp mapping objects are
terminal, including when Y is empty; no vertex was selected. For empty Y and
nonempty X there are no sharp mapping vertices. The coordinate equations still
quantify over exactly the existing families. Arbitrary markings, including flat
or sharp, are preserved because only X's marking restricts an edge of a product
with a sharp parameter. The formulas include degree zero, identities, all
simplicial operators and degeneracies without excluding any parameter.

Searches (2026-10-17 UTC):

- `msearch.py ... leanfinder`: "Sharp mapping simplicial sets of marked
  simplicial sets form an enrichment with tensor and cotensor adjunctions".
  Eight hits: unmarked `SSet.instMonoidalClosed`, generic simplicial-object
  enrichment, quasicategory Cat-enrichment and related declarations. None
  states the marked enrichment and its specified tensor/cotensor isomorphisms.
- `msearch.py ... loogle`: `"SimplicialCategory", "tensor"`: zero hits.
- `msearch.py ... grep`: `marked.*[Ee]nrich|marked.*[Cc]otensor|sharp.*[Tt]ensor`:
  zero Mathlib hits. A direct Mathlib AlgebraicTopology search for
  `marked.*[Ee]nrich|sharp.*[Cc]otensor` also returned none.
- `rg` of the upstream `WeilConjectures` tree for
  `MarkedSSet|marked.?simplicial|mapSharp`, and the required recursive grep for
  the item id: no hits. The direct declaration-name search in upstream and
  `dag/lean_names_upstream.json` found no `marked_sharp_enrichment`.
- `rg` of `lean/Sheaf/AlgebraicTopology` for sharp/enrichment identified the
  reusable marked objects in `MarkedPointCartesianModel` and the dependency
  `MarkedInternalHom`. The model package contains fields for ordinary
  tensor/cotensor bijections and an enrichment, but no standalone theorem
  with exactly this statement and its two enriched simplicial isomorphisms.
  Requiring that whole model package would add hypotheses unrelated to this
  elementary result and create a downstream dependence. No duplicate was made.

Source checked directly: author-hosted HTT PDF
<https://www.math.ias.edu/~lurie/papers/HTT.pdf>, Section 3.1.3 opening paragraph
(printed page 154) gives the sharp mapping universal property; Corollary the project server
(printed page 162) uses exactly this enrichment and the sharp tensor parameter.
The eight-step proof docstring follows the node's coordinate expansion.
No statement correction, new node, dependency repair or disputed statement.

Validation: `scompile.py NZ lem-coef-marked-sharp-enrichment` compiled the
file cleanly, both its sandbox check (28.5 seconds) and library check
(8.7 seconds), without warnings or errors. The required delivery dry run follows.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
