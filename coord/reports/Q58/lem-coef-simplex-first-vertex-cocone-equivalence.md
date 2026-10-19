## Worker report

Item: `lem-coef-simplex-first-vertex-cocone-equivalence`; group Q58.

This is the stage-2 statement of the authoritative Q53 split. The sandbox was empty
apart from dispatcher brief markers at the start of this retry. I copied the current
shared node and changed only `lean`; Q53's statement, proof, source, ancestry and
review records are preserved. The previous unchanged-node rejection is repaired by
attaching the new compiling module and its five declarations.

The module supplies real first-vertex arrow data, its named functor-law theorem,
the functor itself, the induced nerve map, and the claimed restriction theorem.
It uses Mathlib's category of elements rather than defining a second simplex category.
Every theorem has proof `sorry`; definitions have explicit data. The only construction
proof dependency is the named `simplexFirstVertexArrow_functorial` theorem, which
states exactly the functoriality clause already in this node (proof step 1); it determines
no arbitrary data. Both postponed theorems are listed in `lean.declarations` and their
docstrings give complete natural-language proofs, including all six main proof steps.

Hypothesis/clause correspondence:

- The small ordinary category is `(C : Type u) [Category.{v} C]`, with independent
  object and hom universes; there is no nonemptiness, skeletal or thinness assumption.
- For any simplicial set X, `X.Elements` is the opposite of the stated simplex category:
  its objects are pairs of an ordinal and a simplex, and an arrow s to t has underlying
  ordinal map alpha from the dimension of t to that of s, with `X.map alpha.op s = t`.
  This is Mathlib `CategoryTheory.Elements`, lines 45--71, read in full. It retains
  degeneracies and all monotone maps. Thus `(nerve C).Elements` is exactly S(N(C))^op.
- `simplexFirstVertex.obj` sends s to `s.2.obj 0`. `simplexFirstVertexArrow f` is the
  chain's image of `0 ≤ alpha(0)`, followed by equality transport supplied by
  `f.property`. It is the specified arrow tau(0) to sigma(0), in the specified direction.
  The named law theorem asserts both identities and composition for this exact rule.
- `simplexFirstVertexMap` sends each chain to its postcomposition with that functor:
  it is N(v_C). Its explicit formula avoids Mathlib `nerveMap`'s restriction that
  source and target categories share object and hom universes. It is not a freely
  supplied map or replacement functor.
- The arbitrary quasicategory is `(E : SSet.{max u v w}) [Quasicategory E]`.
  `SSet.uliftFunctor.{w}` enlarges the two indexing nerves into this same universe;
  w is arbitrary. This implements “universes enlarged as necessary” without imposing
  an equality between object and hom universes or a size restriction on the target.
- The arbitrary diagram and apex are `p : uliftFunctor.obj (nerve C) ⟶ E` and
  `T : E _⦋0⦌`. The constant diagram is `diagramVertex (SSet.const T)`.
- Both mapping spaces are the published `SSet.Enhanced.mappingSpace`, with ambient
  internal hom `(ihom K).obj E`, and the theorem explicitly asserts `KanComplex` of
  each. The target endpoints are the images of p and its constant diagram under the
  restriction map. By the internal-hom precomposition formula these are precisely
  p composed with N(v_C) and the constant diagram on the new indexing nerve.
- The final conjunct is `IsWeakHomotopyEquivalence (mappingSpaceMap restriction
  (diagramVertex p) (diagramVertex (SSet.const T)))`. The actual restriction is
  `(MonoidalClosed.pre (uliftFunctor.map (simplexFirstVertexMap C))).app E`.
  This asserts equivalence of that map, rather than existence of an unrelated inverse.
- There is no colimit-existence hypothesis. Empty C is permitted; then the simplex
  category is empty as well and both cocone mapping spaces are the point.

Dependency declarations read and used: `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
recorded main declaration `SSet.Enhanced.coneCategory`, together with its
`mappingSpace`, `mappingSpaceMap`, `diagramVertex`, and `IsWeakHomotopyEquivalence`.
I read their complete signatures and docstrings, including `coneCategory`'s explicit
comma definition. Mathlib's existing `nerve`, `Functor.Elements`, `homOfLE`,
`Functor.mapComposableArrows`, `SSet.uliftFunctor` and `MonoidalClosed.pre` supply the
other constructions. There is no dependency repair or new independent notion.

All six already recorded proof-dependency modules are imported without `public`:
`EnhancedFunctorConeCalculus`, `SimplicialGroupoidLocalization`,
`InfinityCofinalCommaCriterion`, `IsofibrationExponentiation`,
`IsofibrationPullbackLimit`, and `NerveNaturalHomotopyEquivalence`.
Their recorded declarations respectively supply Kan closure, edge-inversion
localization, cofinal restriction, the isofibration interface, categorical pullbacks,
and nerve homotopies from natural transformations. No import cycle was needed.

Source read: the primary HTT PDF at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf, Variant the project server(2), PDF page
272 (zero-based), printed p.255. It explicitly uses the opposite simplex category and
initial-vertex functor, and contracts each comma category through simplices of the
undercategory. The expanded argument works for arbitrary small C, not only the
particular category I1 of that variant. The node's existing six-step proof is retained.
WANTED: archival copy of these HTT pages; no Stacks tag is claimed.

Edge cases checked: empty C; a discrete category; the terminal category; C = [1] with
its noninvertible arrow; zero-simplices; all degenerate chains; ordinal maps repeating
vertices or omitting zero; and a one-object category with automorphisms. None needs
invertible arrows in C, injective ordinal maps, or nonempty C. For an ordinal map
omitting zero the arrow is the genuine composite from zero to its positive image,
which confirms the first-vertex orientation. The explicit max-universe lift handles
larger E and independent object/morphism universes.

Actual searches in this retry, logged in `searches.jsonl`:

- msearch LeanFinder: “First vertex functor on the opposite category of simplices of
  the nerve preserves coherent cocone mapping spaces”: eight hits about ordinary
  nerve formulas, the nerve adjunction and standard simplices; no matching theorem.
- msearch Loogle: `CategoryTheory.Functor.Final, CategoryTheory.nerve`: zero hits.
- msearch grep in AlgebraicTopology:
  `first.?[Vv]ertex|simplex.*[Cc]ofinal|[Cc]ofinal.*simplex`: zero hits.
- msearch LeanSearch: “opposite simplex category first vertex functor preserves spaces
  of cocones”: eight hits about ordinary cones and passage to opposites, none giving
  the coherent mapping-space assertion.
- Read-only rg of `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`
  for the exact node id, `simplexFirstVertex`, and first-vertex/cocone combinations:
  no existing implementation of the assigned statement. Broader simplex/category
  searches located Mathlib's `Functor.Elements` and ordinary nerve, which are reused.

Validation: `scompile.py Q58 lem-coef-simplex-first-vertex-cocone-equivalence` compiled
this final module twice (sandbox and library paths), cleanly with only the permitted
sorry usage. No direct compiler or global build was run. The two earlier definition
issues were repaired before this final compile: the functor law is a named theorem,
and independent universe enlargement and both Kan clauses are explicit.
No statement correction or STATEMENT-DISPUTED flag is needed.

## Second reading by Q58

I independently read the item node, its source passage, the dependency node, and the
Lean module. The node's objects and clauses match the following Lean terms.

1. The arbitrary small ordinary category is `(C : Type u) [Category.{v} C]`; the
   object and morphism universes are independent and no nonemptiness, skeletal, or
   thinness hypothesis is added. Verdict: matches the node.
2. The node's simplex category `S(X)` is rendered for the needed nerve by Mathlib's
   `CategoryTheory.Functor.Elements`: `(CategoryTheory.nerve C).Elements` is the
   opposite category of all simplices, including degeneracies. Its arrows have an
   underlying `alpha : [n] -> [m]` and the restriction equation in `f.property`.
   Verdict: the recorded Mathlib notion is the same category and no private copy is
   introduced.
3. `simplexFirstVertexArrow` maps such an arrow to the chain map from vertex zero to
   `alpha(0)`, followed by the endpoint equality; `simplexFirstVertex` packages it
   as the functor to `C`. `simplexFirstVertexArrow_functorial` states identity and
   composition. Verdict: direction, endpoints, and functoriality are exactly the
   node's first-vertex rule.
4. `simplexFirstVertexMap C` is the induced nerve map, defined degreewise by
   `mapComposableArrows`; it is therefore the node's `N(v_C)`, with no arbitrary map
   supplied. Verdict: matches.
5. The arbitrary quasicategory is `(E : SSet.{max u v w}) [Quasicategory E]`; the
   `SSet.uliftFunctor.{w}` terms enlarge both indexing nerves into E's universe.
   Verdict: all universes are explicit, and no equality or finiteness restriction is
   imposed.
6. The arbitrary diagram and apex are exactly
   `p : SSet.uliftFunctor.obj (nerve C) ⟶ E` and `T : E _⦋0⦌`. The two displayed
   `mappingSpace` terms use the dependency's right-pinched definition; their target
   endpoints are the images of `diagramVertex p` and the constant diagram under the
   actual precomposition map. Verdict: both KanComplex clauses are present and the
   endpoints have the required restriction interpretation.
7. The final conjunct is
   `IsWeakHomotopyEquivalence (mappingSpaceMap restriction (diagramVertex p)
   (diagramVertex (SSet.const T)))`, where `restriction` is the actual
   `MonoidalClosed.pre (uliftFunctor.map (simplexFirstVertexMap C))`. Verdict: the
   conclusion asserts equivalence of restriction itself, with no chosen inverse or
   replacement map.
8. The node's absence of a colimit-existence assumption and allowance for empty `C`
   are reflected by the binders: there is no colimit hypothesis and no `Nonempty C`.
   Verdict: matches.

I read the dependency declaration `SSet.Enhanced.coneCategory` and its companion
`mappingSpace`, `mappingSpaceMap`, `diagramVertex`, and `IsWeakHomotopyEquivalence`
in `Sheaf.CategoryTheory.EnhancedDiagramsCones`; their conventions are exactly the
node's enhanced-diagram and right-pinched conventions. I also checked Mathlib's
`Functor.Elements`, `CategoryTheory.nerve`, and `mapComposableArrows` definitions.
The source PDF was opened at HTT Variant the project server(2), printed page 255 (PDF page 272),
where the opposite simplex category and first-vertex functor are specified; the
cofinal mapping-space interpretation is the cited Theorem the project server and Proposition
the project server. The source agrees with the node.

Edge cases checked independently were empty `C`, a discrete category, the terminal
category, `C = [1]` with its noninvertible arrow, a one-object category with
automorphisms, zero-simplices, degenerate chains, ordinal maps repeating vertices,
and ordinal maps omitting zero. The first-vertex composite remains defined in each
case, and the empty case has the unique empty indexing map. Independent and enlarged
universes were also checked. No edge case exposes a missing hypothesis or a vacuous
one.

For the existing-definition search I reran LeanFinder, LeanSearch, Loogle, and grep
searches for first-vertex simplex functors, simplex-category cofinality, and coherent
cocone mapping spaces in Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and
`dag/lean_names_upstream.json`. The hits were ordinary nerve/Elements APIs or
unrelated graph and simplex formulas; none states this notion or theorem. Thus the
module is required, while its simplex-category construction correctly reuses
Mathlib's `Functor.Elements`.

No mismatch was found, so no Lean declaration or node field was changed during this
second reading. The only delivery change is this independent audit section; the
module was recompiled with `scompile.py` and produced no errors or warnings beyond
the permitted `sorry` declarations.
