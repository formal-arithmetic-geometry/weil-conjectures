## Worker report

The module `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus` states
`SSet.Marked.marked_anodyne_lifting_calculus`. Its only postponed proof is this theorem,
whose docstring includes all ten proof steps of the node, including their dependency ids.
All definitions contain actual data; there are no additional postponed helper theorems.
The node's statement, statement dependencies, proof and proof dependencies are unchanged.
No repair note for this item was present.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- Universe convention: the explicit `universe u` and `SSet.{u}`, `Marked.{u}` bind the
  input simplex universe throughout. `def-weil-size-convention` is a metatheoretic
  convention with no declaration or module. `R` is an endofunctor of `Marked.{u}`;
  the ordinal shapes in `markedSaturation` have universe `u` as well.
- Simplicial conventions: the imported `EnhancedDiagramsCones` gives the existing
  `SSet`, Mathlib `stdSimplex`, `horn`, `Quasicategory`, `KanComplex`,
  `SSet.Enhanced.IsEquivalenceEdge` (two inverse triangles) and `SSet.Enhanced.core`.
  Their full definitions and docstrings were read.
- Marked objects, maps, product markings, flat, sharp and natural markings, and both
  mapping objects are the already landed `SSet.Marked`, `Marked.Hom`, `product`,
  `flat`, `sharp`, `natural`, `mapFlat` and `mapSharp` in
  `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`. Their signatures, data and
  docstrings were read. In particular `mapFlat` and `mapSharp` have exactly the
  specified marked-map n-simplices and parameter-precomposition operators.
  `natural` explicitly retains degeneracies; in a quasicategory these are
  equivalences, so this is exactly the required natural marking.
- Generators (i): the first summand of `anodyneGenerators` quantifies over `n`,
  `i : Fin (n + 1)`, `0 < i.val` and `i.val < n`, using
  `flatMap (horn n i).ι`.
- Generators (ii): `finalMarkedSimplex n` is dimension `n+1`, with precisely
  the degenerate edges and `stdSimplex.edge (n+1) n (n+1)` marked.
  `finalMarkedHorn n` is the final horn inclusion with the inverse-image marking
  supplied by `inducedMarking` and `inducedMarkingMap`. The indexing includes
  dimension one and excludes dimension zero, exactly as the node requires.
- Generator (iii): `triangleMarkingSource` has underlying `Δ[2]` and marking the
  union of the degeneracies and the image of all edges of `horn 2 1`. This is the
  displayed pushout, in its canonical marking-only presentation: its underlying
  pushout is `Δ[2]`, and the colimit marking is exactly that union. The induced
  `triangleMarkingMap` is the identity underlying map into the full marking.
  It therefore adds the diagonal to the marked consecutive edges.
- Generators (iv): the final summand quantifies over every `K : SSet.{u}` with
  `KanComplex K`, and uses `flatToMarked (sharp K)`. With `countableOnly=false`
  the implication in the index is vacuous. With `true` it requires countability
  of `Σ n : ℕ, K _⦋n⦌`, i.e. of all simplices, not just vertices.
- Closure definition: `markedSaturation G` is the intersection of all morphism
  properties containing `G` and satisfying `W.pushouts ≤ W`,
  `transfiniteCompositions.{u} W ≤ W`, `W.retracts ≤ W`.
  These are Mathlib's actual cobase-change, continuous well-ordered composition,
  and arrow-category-retract constructions. Identities occur as one-stage
  transfinite composites, and pushout closure transports along isomorphisms.
  `markedAnodyne` uses the unrestricted four families.
- Right lifting means existence of a diagonal: the theorem uses Mathlib's `.rlp`,
  defined using `HasLiftingProperty` in every commuting square; no uniqueness or
  specified choice of fillers is imposed.
- Countable small generation: the first conjunct says saturation is unchanged
  by the countable restriction. The next gives an actual small generating set
  `J.IsSmall.{u}`, contained in those generators, with exactly the same saturation.
  This is existential rather than incorrectly declaring the family of all
  isomorphic copies of countable Kan complexes small.
- Functorial marked-anodyne replacement: `∃ (R : Marked ⥤ Marked)
  (η : 𝟭 Marked ⟶ R), ∀ X, markedAnodyne (η.app X) ∧
  IsNaturallyFibrant (R.obj X)`. Naturality is part of `η`. The target's
  underlying simplicial set is a quasicategory and its marking is exactly the
  equivalence edges, by the existing definition `IsNaturallyFibrant`.
  No arbitrary construction is chosen from this existence theorem.
- Fibrant-object characterization: for every `X`,
  `markedAnodyne.rlp (toPoint X) ↔ IsNaturallyFibrant X`, with the existing map
  to the fully marked standard zero-simplex.
- Pushout products: `i,j` are arbitrary marked maps, `markedAnodyne i` and
  `cof j` are precisely the hypotheses. The existing `IsPushoutProduct i j p`
  specifies the pushout square on `X×Y → X'×Y` and `X×Y → X×Y'` and both
  restrictions of its canonical map into `X'×Y'`. The theorem explicitly
  asserts existence of that pushout product, and `markedAnodyne p` for every
  such representative. It does not assume an unavailable global pushout instance
  or make the conclusion conditional on a pushout object never existing.
- Mapping objects: for arbitrary marked `X` and arbitrary `C : SSet.{u}` with
  `Quasicategory C`, the flat mapping object is a quasicategory and the sharp
  one is Kan. `mapSharpToFlat` is the actual parameter-marking inclusion,
  not an arbitrary isomorphism. In every degree the theorem asserts this map
  injective with image exactly `(Enhanced.core (mapFlat X (natural C))).obj n`.
  This states that the sharp mapping object IS the core, compatibly with the
  canonical inclusion on all simplices.
- Restriction: `mapSharpPre j (natural C)` is the existing precomposition map.
  For `cof j` it satisfies `SSet.modelCategoryQuillen.J.rlp`, the horn-lifting
  definition of Kan fibration. For `markedAnodyne j` it satisfies
  `SSet.modelCategoryQuillen.I.rlp`, the boundary-lifting definition of trivial
  Kan fibration, including boundary dimension zero. There are no fibrancy or
  inhabitance assumptions on the source or target of `j`.
- Finite detector: `detectorFaceRelations` and `detectorDegeneracyRelations`
  are parallel maps `Δ[2] ⨿ Δ[2] → Δ[3] ⨿ Δ[1]`, using respectively
  `δ 1, δ 2` into the first summand and `σ 0, σ 1` into the second.
  Their actual coequalizer `equivalenceDetector` therefore corepresents exactly
  `(σ,e)` with the two specified equations. The named `e` summand is redundant
  because those equations identify it with an edge of the tetrahedron, so this
  is the stated quotient of `Δ[3]`, not a freely chosen detector.
  `equivalenceDetectorEdge` is specifically the image of `[0,1]` from `Δ[3]`.
  `markedEquivalenceDetector` adds precisely that edge to the degeneracies.
  The final conjunct gives both boundary lifting and `IsIso` for the restriction
  along `flatToMarked markedEquivalenceDetector` into every naturally marked
  quasicategory, as requested.

Dependency imports and proof planning:

- Public statement import: `Sheaf.CategoryTheory.EnhancedDiagramsCones`, with
  `SSet.Enhanced.IsEquivalenceEdge` and `SSet.Enhanced.core`.
- Reused constructions import: `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`,
  with the marked primitives listed above and `cof`, `toPoint`, `mapSharpPre`,
  `IsNaturallyFibrant`, `IsPushoutProduct`. No conclusion of its model theorem is
  used; the present theorem has its own single `sorry`. Its proof already cites
  this item: adding a reverse proof import in that module would close an import
  cycle and must be omitted under stages/2-statements.md §3(7). This delivery
  leaves the existing ownership of the shared marked primitives intact.
- Proof imports: `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, declaration
  `SSet.Enhanced.enhanced_functor_cone_calculus`;
  `Sheaf.CategoryTheory.EquivalenceOuterHornFilling`, declaration
  `SSet.Enhanced.equivalence_iff_outer_horn_filling`;
  `Sheaf.CategoryTheory.SimplicialCompositionSpine`, declaration
  `SSet.Enhanced.simplicial_composition_spine`;
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`, declaration
  `SSet.KanQuillen.right_proper_kan_quillen`. Their statements and proof docstrings
  were read. The other six proof dependencies have no Lean record in the current
  DAG and consequently no recorded module to import. They are retained in the
  theorem's proof docstring and in the unchanged proof dependency list.
- Mathlib imports `MorphismProperty.TransfiniteComposition` and
  `MorphismProperty.IsSmall` provide the exact closure and small-family APIs.

Edge cases checked before finalization: inner horns in dimensions zero and one
have no valid index; the final family starts at dimension one, whose horn has no
nondegenerate marked edge in its source; the triangle horn contains both consecutive
edges but not the long edge. The empty Kan complex is included in (iv), without
`Nonempty` assumptions. Empty marked inputs and quasicategories are allowed in
mapping assertions. Boundary lifting in degree zero is retained for both trivial
restriction assertions. Marking extensions with identity underlying map are covered
by `cof`; the pushout-product assertion therefore includes them. Countability is on
all degrees. Every replacement object remains in the same `SSet.{u}` universe.

Searches (2026-10-16 UTC):

- `msearch.py ... leanfinder "marked anodyne maps of marked simplicial sets pushout
  product mapping space Kan fibration"`: eight hits, headed by
  `SSet.modelCategoryQuillen.J`, `I`, their fibration instances, and horn membership
  lemmas. These are unmarked simplicial facts, not the present theorem.
- `msearch.py ... loogle "SSet.Marked, MorphismProperty.transfiniteCompositions,
  MorphismProperty.retracts"`: zero hits, unknown identifier `SSet.Marked`.
- `msearch.py ... grep "marked|Marked" AlgebraicTopology`: zero Mathlib hits.
- `rg` for marked-anodyne names, marked simplicial sets, and the item id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no implementation or theorem.
  The required `grep -rn` of the exact item id also returned no hits there.
- `rg` under `lean/Sheaf`: the marked primitives and references to this calculus
  occur in `MarkedPointCartesianModel`; it has no marked-anodyne generators or
  saturation definition and no theorem stating this node. Its model theorem has
  different conclusions and is not an exact existing match.
- Additional name searches for all new declaration stems in Mathlib's
  `AlgebraicTopology`, the project and `WeilConjectures` found no duplicate.
  Mathlib's morphism-property files were read for pushouts, retracts,
  transfinite compositions, `.rlp` and `IsSmall`; its simplicial-set
  `CategoryWithFibrations` was read for the exact horn and boundary families.
  The existing `SSet.Enhanced.WeaklySaturated` is specialized to unmarked `SSet`,
  so it does not define saturation in the marked category.
- `tools/blueprint_refs.py search 'marked simplicial'` returned no matching
  blueprint node. DAG text searches found the model node and the dependent
  coanodyne and relative-calculus nodes; none already states this item.
- Opened HTT online and read Definition the project server, Remark the project server, the point-case
  lifting and mapping statements, and Proposition the project server(1)'s explicit detector
  equations and its assertion that the restriction is an isomorphism.

Validation: the required `scompile.py Q39 lem-coef-marked-anodyne-lifting-calculus`
compiled the complete module cleanly in both its sandbox and library placement
(1.4 and 1.6 seconds respectively). No warnings. All variables and universe levels
are explicit (`autoImplicit false`). The module contains one named `sorry` and
no proven theorem. No statement fault or dispute was found.

## Second reading by Q39

I read the node and module independently against HTT, not just the worker report.
The source is https://www.math.ias.edu/~lurie/papers/HTT.pdf, PDF pages 163--175:
Definition the project server, Definition the project server and Remark the project server, Proposition the project server
and Remark the project server specialized to the terminal point, Proposition the project server,
Remark the project server, Remark the project server, Lemma the project server, and the explicit detector in
Proposition the project server(1). The relative source assumes a Cartesian fibration over
S; at the point this means exactly a quasicategory with its equivalences marked.
There is no scheme, coefficient ring, finiteness, characteristic, or nonemptiness
hypothesis to carry over. No repair-note file for this item is present.

My object/hypothesis/conclusion checklist and correspondence:

1. Fix an input universe and small simplicial sets, with standard simplices,
   horns, quasicategories, equivalence edges, Kan complexes and cores.
   Lean: `universe u`, `SSet.{u}`, Mathlib's `stdSimplex`, `horn`,
   `Quasicategory`, `KanComplex`, and `Enhanced.IsEquivalenceEdge`/`Enhanced.core`
   from the recorded `EnhancedDiagramsCones` module. I opened its definitions:
   inverse edges have both inverse triangles, and the core tests every edge of
   every simplex. `def-weil-size-convention` is explicitly a declaration-free
   metatheoretic convention. Verdict: exact.
2. Objects are simplicial sets with a subset of edges containing degeneracies;
   maps preserve those subsets and products mark coordinatewise. Lean reuses
   `SSet.Marked`, `Marked.Hom`, `markedCategory`, `product`, `productMap` from
   `MarkedPointCartesianModel`. I read their actual data, not just their names.
   Verdict: exact, with no new marking convention or private copy.
3. Minimal/full/natural markings and both parameter mapping objects. Lean:
   `flat`, `sharp`, `natural`, `mapFlat`, `mapSharp` from that same module.
   `mapFlat` and `mapSharp` use the hom functor on product with the respective
   cosimplicial simplex; thus their n-simplices are precisely the required
   marked maps and all operators are precomposition. `natural` includes
   degeneracies explicitly, which are equivalences in every quasicategory.
   `IsNaturallyFibrant X` requires both the quasicategory condition and equality
   of its markings with equivalence edges, not just one implication.
   Verdict: exact under the theorem's explicit `Quasicategory C` hypothesis.
4. Generators (i): flat inner horns, with precisely `0 < i < n`. Lean:
   the first supremum of `anodyneGenerators`, using `flatMap (horn n i).ι`
   with both inequalities. Verdict: exact, with no outer or zero-dimensional horn.
5. Generators (ii): positive-dimensional final horn with induced marking of
   just the final edge and degeneracies. Lean: `finalMarkedSimplex n` is
   dimension n+1 and marks `stdSimplex.edge (n+1) n (n+1)`; `finalMarkedHorn n`
   uses the final horn and `inducedMarking` is inverse image under its actual
   inclusion. Verdict: exact after the explicit positive-dimension reindexing.
6. Generator (iii): the displayed sharp-horn/flat-simplex pushout. Lean:
   `triangleMarkingSource` has underlying two-simplex with marking equal to
   degeneracies union the image of all edges of `horn 2 1`; the underlying
   map of `triangleMarkingMap` is the identity. This is the pushout marking,
   so precisely the missing long edge becomes marked. Verdict: exact.
7. Generators (iv): all Kan K, minimal to full marking. Lean:
   the last supremum of `anodyneGenerators false` and `flatToMarked (sharp K)`.
   The optional countability condition is vacuous when false. Verdict: exact.
8. Least pushout/transfinite/retract closure and existence-only right lifting.
   Lean: `markedSaturation` takes the intersection over all containing classes
   closed under Mathlib's `pushouts`, `transfiniteCompositions.{u}`, `retracts`;
   `markedAnodyne` uses all four unrestricted families. I opened those APIs:
   pushouts are actual pushout squares, composites are well-order-continuous,
   retracts are `RetractArrow`, and `.rlp` uses `HasLiftingProperty` in every
   square. A one-object chain supplies identities, and pushouts supply their
   isomorphic arrows; no extra isomorphism hypothesis is missing. Verdict: exact.
9. A small generating set, with countable Kan complexes sufficient in (iv).
   Lean: the first conjunct identifies the countably generated saturation;
   the second gives `J.IsSmall.{u}`, `J ≤ anodyneGenerators true` and equality
   of saturations. I read `IsSmall`: it means a small set of arrows, rather
   than merely small domains. Countability is `Countable (Σ n : ℕ, K _⦋n⦌)`.
   Taking representatives gives such a J, without claiming all isomorphic
   copies form a small family. Verdict: exact small-generation assertion.
10. Functorial marked-anodyne replacement by some naturally marked quasicategory.
    Lean: `∃ (R : Marked.{u} ⥤ Marked.{u}) (η : 𝟭 Marked.{u} ⟶ R), ∀ X,
    markedAnodyne (η.app X) ∧ IsNaturallyFibrant (R.obj X)`.
    Naturality is actual natural-transformation data; no choices are hidden in
    a definition using this unproved existence theorem. Verdict: exact.
11. Terminal lifting objects are exactly those natural markings. Lean:
    `∀ X, markedAnodyne.rlp (toPoint X) ↔ IsNaturallyFibrant X`.
    I checked `toPoint`: its target is the fully marked standard zero-simplex,
    and its underlying arrow is the canonical terminal arrow. Verdict: exact.
12. Pushout product with every degreewise injection is marked anodyne. Lean:
    the fifth conjunct quantifies arbitrary marked i,j, assumes exactly
    `markedAnodyne i` and `cof j`, and gives both existence of a pushout-product
    representative and the assertion for every such representative.
    `cof` is degreewise underlying injectivity; `IsPushoutProduct` uses the
    correct square on X×Y, X'×Y, X×Y' and both restrictions to X'×Y'.
    Verdict: exact; neither existence nor marking-only injections are lost.
13. For every marked X and quasicategory C, flat mapping is a quasicategory,
    sharp mapping is Kan and is the flat mapping core. Lean: the sixth
    conjunct, with `Quasicategory C` as the only hypothesis. The map used is
    the constructed `mapSharpToFlat`, induced by minimal-to-full parameter
    marking. Injectivity plus the degreewise image/core equivalence for every
    n expresses the core identification through this canonical inclusion.
    Verdict: exact and compatible with simplicial operators.
14. Restriction along any degreewise injection is a Kan fibration; restriction
    along marked-anodyne maps is a trivial Kan fibration. Lean:
    `cof j → modelCategoryQuillen.J.rlp (mapSharpPre j (natural C))` and
    `markedAnodyne j → modelCategoryQuillen.I.rlp (...)`. I opened the
    Mathlib definitions: J contains all positive-dimensional horns and I all
    boundary inclusions including degree zero. `mapSharpPre` really is
    precomposition by `productMap j (𝟙 _)`. Verdict: exact.
15. The finite detector and its distinguished marked edge. Lean:
    `equivalenceDetector` is the actual coequalizer of two maps from
    Δ[2] ⨿ Δ[2] to Δ[3] ⨿ Δ[1], defined by faces δ1,δ2 and degeneracies
    σ0,σ1. Maps from it are exactly pairs (σ,e) satisfying the two specified
    equations. The auxiliary edge summand is identified with an edge of the
    tetrahedron, so this is the required quotient of Δ[3].
    `equivalenceDetectorEdge` is specifically the image of edge [0,1] in Δ[3],
    and `markedEquivalenceDetector` adds only it and the degenerate edges.
    Verdict: exact, with real coequalizer data rather than an arbitrary witness.
16. Restriction from the marked detector to its flat version is both trivial
    Kan and an isomorphism for every naturally marked quasicategory. Lean:
    the final conjunct applies `I.rlp` and `IsIso` to the same `mapSharpPre`
    along `flatToMarked markedEquivalenceDetector`. Direction is from maps
    on the marked object to maps on its flat version. Verdict: exact.
17. All assertions are universe-relative and replacement remains small in the
    input universe. Lean explicitly uses `Marked.{u}`, `SSet.{u}`,
    `transfiniteCompositions.{u}`, `J.IsSmall.{u}` and a same-universe
    endofunctor R. There is no independent test universe or hidden equality
    restricting inputs. Verdict: exact.

Edge cases: inner horns have no allowed index at n=0,1; family (ii) starts
at dimension one and includes its endpoint horn. Family (iii) marks both
consecutive edges and then the diagonal. Empty Kan complexes are allowed in
(iv), and empty marked X or empty quasicategory C remain allowed in all
mapping assertions. Nothing assumes an inhabited mapping space. The I-lifting
conditions retain the empty boundary in degree zero. Degreewise injections
include maps changing only markings. Countability refers to every degree.
There are no coefficient or characteristic cases; those objects do not occur.

Independent searches, 2026-10-17 (three kinds, with different phrasing):

- `msearch.py ... leanfinder "weak saturation marked simplicial sets natural
  marking fibrant replacement countable Kan complexes"`: eight hits, including
  Mathlib's unmarked J, I, KanComplex, sk and cosk. None states this calculus.
- `msearch.py ... leansearch "Mapping simplicial set into quasicategory marked
  equivalence edges largest Kan subcomplex restriction isomorphism"`: eight
  hits including `instQuasicategoryOfKanComplex`, `Subcomplex.topIso` and
  `Subcomplex.instIsIsoToRangeOfMono`. Their unmarked statements are not matches.
- `msearch.py ... grep "marking|anodyne|saturation" AlgebraicTopology`: 25
  hits in unmarked anodyne-extension files, including the inner pushout-product
  module. These do not define the marked class or its mapping objects.
- Direct `rg` searches for `marked.?anodyne`, `marked.?simplicial`,
  `markedSaturation`, `equivalenceDetector`, `flatToMarked`, and marking
  declarations across Mathlib, upstream WeilConjectures and `lean/Sheaf` found
  only the reused marked primitives and references in `MarkedPointCartesianModel`.
  No existing exact theorem or duplicate helper was found.
  I also opened `Enhanced.WeaklySaturated`: it is specific to unmarked SSet,
  so cannot serve as saturation in the category Marked. The generic closure
  operators are reused rather than reimplemented.

Changes and dependency audit: no mathematical mismatch, missing notion, new
node, dependency repair, or source-based statement correction was needed.
I added three ordinary proof imports required by stages/2-statements.md §3(7):
`Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` for the recorded boundary-cell
leaf, `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`
for the recorded inner pushout-product leaf, and
`Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument` for the
recorded small-object-factorization leaf. I opened their actual declarations
`relativeCellComplexOfMono`, `innerAnodyneExtensions_pushoutObjObjι'` and
`SmallObject.functorialFactorizationData`. The worker's description of six
dependencies as having no Lean record overlooked these three Mathlib matches.
The remaining three unstated proof dependencies have no module to import:
right-fibration-space-fiber, marked-endpoint-prism-generation and
marked-triangle-cancellation. I opened the four recorded Sheaf proof modules
and their relevant signatures as well. Reusing definitions from the model
module does not invoke its downstream model theorem; the reverse import there
would form a cycle and is correctly deferred.

All helper data are constructed, including proofs of degeneracy preservation;
the only postponed theorem is the item's theorem with its matching DAG node.
The module and declaration docstrings carry source and blueprint id. Its proof
docstring actually retains all eleven node steps (the worker's opening sentence
said ten); no proof step is missing. No notation, private definition, local
instance, or auto-implicit binder obscures the signature. The theorem signature
in `lean.statement` is verbatim equal to the file and has not changed.

Validation: after the three import additions, the required scompile wrapper
compiled the entire delivered file cleanly in sandbox placement (1.6 s) and
library placement (1.8 s), with no warnings or errors. All universes and
variables are bound. The node and all mathematical declarations remain intact.
