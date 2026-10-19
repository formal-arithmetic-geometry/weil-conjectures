## Worker report

The module `Sheaf.AlgebraicTopology.HomotopyCategoryTriangleCalculus` states
`SSet.homotopyCategory_triangle_calculus`, with its sole proof `sorry`. It introduces
no definitions, auxiliary theorems, or new nodes. The item's node changes only in `lean`.
No repair note exists for this item. There is no statement correction or disputed statement.

Clause-by-clause reading:

- A quasicategory in a fixed, arbitrary input universe is `(D : SSet.{u}) [Quasicategory D]`,
  with `universe u` explicitly declared and `autoImplicit false`.
- The requested `hD` is exactly Mathlib's
  `SSet.Truncated.HomotopyCategory ((SSet.truncation 2).obj D)`. Its objects are the
  vertices, wrapped by `Truncated.HomotopyCategory.mk`. The wrapper is surjective
  (`HomotopyCategory.mk_surjective`), so quantifying over vertices covers all objects.
- Finite composable words are the paths in the free category. `Cat.FreeRefl` quotients
  paths by the relation identifying the reflexive edge with the empty path. The
  reflexive edge of `SSet.OneTruncation₂` is `Truncated.Edge.id`, the degeneracy of the
  vertex. `OneTruncation₂.HoRel₂.of_compStruct` then imposes exactly the relation of
  a consecutive two-edge path with a third edge whenever the specified triangle exists.
  `Truncated.HomotopyCategory` is this quotient. Its composition is inherited path
  concatenation. These existing definitions are used directly, without making a copy
  or substituting the different `HomotopyCategory₂` construction.
- The edge class `[f]` is `Truncated.HomotopyCategory.homMk f.toTruncated`.
  `SSet.Edge.toTruncated` is the existing identity conversion to the two-truncation.
- The first conjunct quantifies over `x y` and every morphism `a : mk x ⟶ mk y` and
  concludes `∃ f : Edge x y, Truncated.HomotopyCategory.homMk f.toTruncated = a`.
  This is precisely the single-edge representative assertion, including identity arrows.
- The second conjunct quantifies over all `x y z` and all three edges `f`, `g`, `h`
  with the requested endpoints. The equation `[g] ∘ [f] = [h]` is written
  `homMk f.toTruncated ≫ homMk g.toTruncated = homMk h.toTruncated`.
- The other side of the iff is `Nonempty (Edge.CompStruct f g h)`. Its data consist
  of a two-simplex with faces `δ₂ = f.edge`, `δ₀ = g.edge`, `δ₁ = h.edge`, so all
  three edges are fixed exactly; this is existence of the triangle, not existence
  of a triangle with only the same edge classes.

Dependency inspection and declarations used:

- `def-cbc-enhanced-diagrams-cones` records
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` and its principal declaration
  `SSet.Enhanced.coneCategory`, with the full helper declaration list. I read its
  node statement and record and the module. For this item the relevant part of that
  definition node is its use of Mathlib's existing `SSet`, `stdSimplex`, degeneracy
  operators, and `Quasicategory`; the coherent cone and mapping-space helpers are
  not needed. The dependency module is publicly imported, and the same Mathlib
  `Quasicategory` horn-filling condition is used, without a private replacement.
- `Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat` supplies
  `SSet.OneTruncation₂`, `SSet.OneTruncation₂.HoRel₂`,
  `SSet.Truncated.HomotopyCategory`, its `mk` and `homMk`, and `SSet.truncation`.
  I read their signatures and source definitions/docstrings, including the
  presentation in the module header and `homMk_id`/`homMk_comp_homMk`.
- `SSet.Edge`, `SSet.Edge.toTruncated`, and `SSet.Edge.CompStruct` come from
  `Mathlib.AlgebraicTopology.SimplicialSet.CompStruct`, already imported publicly
  by `HomotopyCat`. I read the definitions and all three prescribed-face equations.
- No proof dependency is recorded, so none requires a separate proof-only import.

Source and future proof: I opened the cited
[Cisinski PDF](https://cisinski.app.uni-regensburg.de/CatLR.pdf), Section 1.6,
Lemmas 1.6.2 and 1.6.4 and Theorem 1.6.6 (PDF pages 36--40, printed 21--25).
The theorem docstring gives a complete natural-language proof plan: reduce words
by inner two-horn fillers; use coherence and edge homotopy to identify the
presentation with edge homotopy classes; replace a chosen composite diagonal
by the specified homotopic diagonal using an inner three-horn filler. This is
why the reverse implication holds for the actual three specified edges.

Edge cases checked before writing:

- Empty quasicategory: there is no `Nonempty D`, no chosen vertex, and both
  conclusions quantify over vertices, so the assertion is vacuous as required.
- Empty word at a vertex: `Edge.id` is allowed and its image is the identity by
  the existing `Truncated.HomotopyCategory.homMk_id`.
- Degenerate edges, repeated vertices, and identity compositions: there is no
  nondegeneracy or distinctness restriction. `CompStruct.idComp`, `compId`, and
  `idCompId` in Mathlib provide the corresponding degenerate triangles.
- Disconnected objects and pairs with no edges: every quantifier has the stated
  endpoints; no edge or arrow is assumed to exist before it is quantified over.
- No restriction on the input universe: paths, edge types, and the quotient
  category all stay in the same arbitrary `u`.

Searches made using `/home/ubuntu/weil-launcher-nt/msearch.py Q20
lem-coef-homotopy-category-triangle-calculus`:

- `leanfinder`: “For a quasicategory, every arrow of the category presented by
  edges and triangle relations is represented by an edge, and an equality of a
  composite of two edges with a third edge is realized by a triangle”. Eight hits
  include `Quasicategory₂.fill21/fill31/fill32`, `Quasicategory.hornFilling`, and
  `Truncated.Edge.comp`; none states both assertions for the path presentation.
- `loogle`: `SSet.Truncated.HomotopyCategory.homMk, SSet.Truncated.Edge.CompStruct`.
  Three hits: `homMk_comp_homMk`, its reassociation lemma, and `lift_map_homMk`.
  The first gives only the triangle-to-equation implication, not the converse
  or surjectivity for the presented category.
- `grep` in Mathlib `AlgebraicTopology`: `homMk_surjective|nonempty_iff|HomotopyCategory₂.*HomotopyCategory`.
  Fourteen hits include `HomotopyCategory₂.homMk_surjective` and
  `Edge.CompStruct.nonempty_iff`. I read `TwoTruncated.lean`, including the explicit
  TODO that its category has not yet been compared with `HomotopyCategory`.
  These are useful proof ingredients, not an exact existing declaration.
- `leansearch`: “Every morphism in the homotopy category presented by edge words
  and triangle relations of a quasicategory is represented by an edge; equality
  of a composite of edges with another edge is witnessed by a 2 simplex”. Eight
  hits include `HomotopyCategory.homMk`, `homMk_comp_homMk`, and the analogous
  surjectivity theorem for `HomotopyCategory₂`; again no exact match.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`:
  `homotopyCategory_triangle|homotopy_category_triangle|homMk_surjective|CompStruct.nonempty_iff|HomotopyCategory₂|Truncated.HomotopyCategory`.
  Only unrelated hom-surjectivity uses and the existing diagram-object/edge-class
  helpers in `ModelInfinityDerivedAdjunction.lean`; no statement of this item.
- `rg` for the exact item id in upstream `WeilConjectures` returned no match.
  Searching `dag/lean_names_upstream.json` for `HomotopyCategory|homMk_surjective|triangle_calculus`
  likewise returned no declaration. The proposed theorem name was also searched
  in Mathlib, upstream and `lean/Sheaf`, without a collision.

Validation: the prescribed `scompile.py Q20 lem-coef-homotopy-category-triangle-calculus`
compiled the delivered module cleanly in both sandbox and library positions (1.2 s
per position), with no errors or warnings. All binders and universes are explicit.
The delivery dry run is recorded below after completion. Independent second reading
is reserved for the next worker; this report does not claim one has happened.

Dry run result: `deliver2.py Q20 lem-coef-homotopy-category-triangle-calculus --no-push`
exited 0 and printed `OK (dry run): commit 86f8330c07 compiles and passes the preflight
except for the second reading, which the second reader writes; nothing pushed.`
As instructed by the tool, no second-reading section was written by this worker.


## Second reading by Q20

I independently opened the item node, the sandbox module, the recorded dependency
node and module, and the Mathlib definitions used by the signature. I read Cisinski,
Higher Categories and Homotopical Algebra, July 30, 2026, Section 1.6, printed
pp. 21--25 (PDF pp. 36--40), at https://cisinski.app.uni-regensburg.de/CatLR.pdf.
Section 1.6.1 assumes only an infinity-category, defined by inner horn filling in
Definition 1.5.1. Lemmas 1.6.2 and 1.6.4 supply coherence and edge homotopy;
Theorem 1.6.6 compares the presented category with edge homotopy classes.
The statement needs no field, ring, finiteness or nonemptiness hypothesis.

My object/hypothesis/conclusion inventory and Lean correspondence:

1. An arbitrary input universe and a quasicategory D: `universe u`,
   `(D : SSet.{u}) [Quasicategory D]`. The imported
   `Mathlib.AlgebraicTopology.Quasicategory.Basic` class requires exactly inner
   horn filling. Verdict: exact, with no extra instance.
2. Vertices as objects of hD: `x y : D _⦋0⦌`, represented by
   `Truncated.HomotopyCategory.mk (V := (truncation 2).obj D) x` and the same for y.
   I read `mk` and `mk_surjective` in `HomotopyCat.lean`: the wrappers contain
   exactly the vertices. Verdict: exact, no objects excluded.
3. Finite composable edge words, degenerate-edge identities, triangle relations,
   and concatenation: `Truncated.HomotopyCategory` is the categorical quotient
   by `OneTruncation₂.HoRel₂` of `Cat.FreeRefl (OneTruncation₂ V)`.
   I read `FreeReflRel` and `FreeRefl` in `CategoryTheory/Category/ReflQuiv.lean`,
   and `HoRel₂` in `SimplicialSet/HomotopyCat.lean`: the first relation identifies
   the reflexive edge with the nil path and the second identifies the two-edge
   path with the specified diagonal for each `Truncated.Edge.CompStruct`.
   The reflexive edge is `Truncated.Edge.id`, hence the degeneracy of the vertex.
   These are categorical congruence quotients with inherited composition.
   Verdict: exactly the node's hD, using existing definitions.
4. The class [f] of an actual edge f: `Truncated.HomotopyCategory.homMk
   f.toTruncated`. I read `Edge`, `Edge.toTruncated`, and `homMk`: truncation
   leaves dimensions zero through two intact, and `homMk` is the quotient image
   of the one-edge path. Verdict: exact, no replacement by a different class.
5. Every arrow x to y has a single-edge representative: the first conjunct
   universally quantifies over `x y` and `a : mk x ⟶ mk y`, then says
   `∃ f : Edge x y, ...homMk f.toTruncated = a`. Verdict: exact endpoints,
   quantifier order and equality.
6. Three specified vertices and edges f:x to y, g:y to z, h:x to z: the second
   conjunct binds `x y z`, then `(f : Edge x y) (g : Edge y z) (h : Edge x z)`.
   Verdict: exact, with repeated vertices and degenerate edges permitted.
7. The equation [g] composed with [f] holds iff a triangle has exactly these
   edges: `homMk f.toTruncated ≫ homMk g.toTruncated = homMk h.toTruncated`
   iff `Nonempty (Edge.CompStruct f g h)`. I read the definition and the
   `simplex`, `d₂`, `d₀`, `d₁` signatures in `CompStruct.lean`: the simplex
   has faces f, g, h in exactly those positions. Verdict: exact iff, including
   the equation-to-triangle direction for the actual chosen boundary.
8. Empty quasicategories, degenerate edges, and each input universe: there is
   no `Nonempty` assumption on D, no chosen vertex, no nondegeneracy or distinctness
   condition, and only the arbitrary universe u. Verdict: all requested cases.

Dependency inspection: `def-cbc-enhanced-diagrams-cones` lives in
`dag/nodes/sec-smooth-purity/`, records
`Sheaf.CategoryTheory.EnhancedDiagramsCones` and `SSet.Enhanced.coneCategory`
with its helper list. The module explicitly uses the Mathlib simplicial primitives
and publicly imports `Quasicategory.Basic`; this item uses those primitives, not
its cone helpers. Nothing in that definition module changes the meaning of
quasicategory, vertex, edge or degeneracy. The other proof dependency,
`lem-coef-edge-homotopy-quotient-calculus`, is a Mathlib leaf, with no delivered
module. I read its `mathlib_match` and `TwoTruncated.lean`, particularly
`HomotopicL`, `instSetoidEdge`, the category construction, `homMk_surjective`,
and `Edge.CompStruct.nonempty_iff`. Its category is different from the presented
category; the docstring now records the node's explicit comparison between them.
There are no new nodes or dependency repairs in this delivery, so H12/H13 add
no separate module to review. No repair note exists for this item.

Independent edge-case checks: an empty D has no vertices, so both universally
vertex-indexed conclusions are vacuous. At an existing vertex, the empty word
is represented by `Edge.id` (`HomotopyCategory.homMk_id`). Degenerate triangles
`CompStruct.idComp`, `compId`, and `idCompId` cover identities, including the
one-vertex case. Disconnected components and pairs with no arrows add no
existence assumption: the first assertion starts from an actual arrow.
Truncation and the two quotients remain in u. There is no coefficient
characteristic, scheme, numeric n, or independent index set in this statement.

Independent searches (through the prescribed `msearch.py Q20
lem-coef-homotopy-category-triangle-calculus` wrapper):

- LeanFinder query `HomotopyCategory triangle calculus edge CompStruct` returned
  eight unrelated triangulated-category hits; none concerns this simplicial hD.
- Loogle query `SSet.Truncated.HomotopyCategory.homMk` returned twelve hits,
  including `homMk_id`, `homMk_comp_homMk`, `hom_rec`, and `functor_ext`.
  The triangle relation proves only one direction; no surjectivity or converse
  criterion for this presentation is already stated.
- LeanSearch query `In a quasicategory, morphisms in the path category modulo
  two-simplex relations have single edge representatives, and prescribed
  triangles realize composite equations.` returned eight hits, including
  `instSetoidEdge`, `Quasicategory₂.mk`, `FreeReflRel`, and homotopy congruences;
  none gives the item for the path presentation.
- Direct rg in Mathlib's SimplicialSet and Quasicategory directories for
  `homMk_surjective|HomotopyCategory₂.*HomotopyCategory|HomotopyCategory.*HomotopyCategory₂|nonempty_iff`
  found only the single-edge-quotient surjectivity and triangle iff in
  `TwoTruncated.lean`. I read its explicit TODO comparing the two constructions.
- Direct rg in upstream `WeilConjectures` and repository `lean/Sheaf` for
  `Truncated.HomotopyCategory|HomotopyCategory₂|Edge.CompStruct` found only
  diagram-object/edge-class helpers in `ModelInfinityDerivedAdjunction.lean`.
  I opened those signatures: they do not assert either clause of this item.
  The exact theorem name had no existing declaration, and the upstream name
  map search for `HomotopyCategory|triangle_calculus|homMk_surjective` had no hit.

Mismatches found and repaired:

- H8: the old proof docstring gave a valid informal horn-compression argument
  but did not carry the node's six explicit proof steps or name its supporting
  edge-quotient node. I replaced only that proof-plan paragraph with the six
  steps, including the construction of F and G, quotient descent, the two
  inverse calculations, the exact-boundary triangle criterion, and sizes.
- Proof dependency imports: added non-public
  `import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated` for the recorded
  Mathlib proof dependency. The worker report's claim that no proof dependency
  was recorded was inaccurate: the node has that Mathlib leaf and the enhanced
  diagram definition. The latter was already publicly imported.
- No H3 mathematical mismatch was found. I preserved the theorem signature,
  node statement, and node dependency fields. The verbatim `lean.statement`
  equality was checked programmatically. There is one named theorem, its only
  proof is `sorry`, no new definition, no hollow data, no local notation or
  private declaration, and every universe and binder is explicit.

Validation: after the changes, the prescribed scompile.py wrapper is run for
this sole module; its result and the final delivery dry run are recorded below.

Second-reader compile result: scompile.py exited 0; sandbox and library
positions compiled in 1.4 s and 1.2 s, respectively, with no diagnostics.

Second-reader dry run: deliver2.py --no-push printed
`OK (dry run): commit 882417c77d passes the preflight and compiles; nothing pushed`.
