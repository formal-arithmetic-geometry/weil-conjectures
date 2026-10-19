## Worker report

The module `Sheaf.CategoryTheory.LeftFibrationEquivalenceLift` states
`SSet.Enhanced.left_fibration_equivalence_lift`, with one postponed proof and no definitions.
The node is unchanged outside `lean`.

Hypotheses and conclusions, clause by clause:

- Small quasicategories `𝓛, 𝓜`: `{L M : SSet.{u}} [Quasicategory L] [Quasicategory M]`,
  with explicitly declared arbitrary universe `u`.
- The simplicial map `r` is `(r : L ⟶ M)` and its left-fibration hypothesis is
  `(hr : leftFibration r)`.
- Reflection: the first conjunct quantifies over every edge `a : L _⦋1⦌` and asserts
  `IsEquivalenceEdge M (r.app _ a) → IsEquivalenceEdge L a`.
- The inner-horn part of the isofibration conclusion is `InnerFibration r`.
- Its equivalence lifting at a prescribed source is the third conjunct: for every `x` and
  equivalence `e` with `M.δ 1 e = r.app _ x`, there is an equivalence `a` with
  `L.δ 1 a = x` and the strict equality `r.app _ a = e`. Its target is unrestricted.
- The prescribed-target clause is the fourth conjunct: for every `y` and equivalence `e`
  with `M.δ 0 e = r.app _ y`, there are `x` and `a` with `L.δ 1 a = x`,
  `L.δ 0 a = y`, `IsEquivalenceEdge L a`, and `r.app _ a = e`. The unnamed `m₀`
  in the node is `M.δ 1 e`; naturality of `r` gives `r(x) = m₀` from these equalities.
  No extra choice of target or homotopy instead of strict equality is substituted.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`
  (an actual inverse edge and its two inverse-triangle witnesses). Its imported Mathlib
  `SSet`, `SSet.Quasicategory`, and the face operators give the simplicial objects,
  quasicategory hypotheses, edges, and endpoints.
- `Sheaf.CategoryTheory.InfinityFibrations`: `SSet.Enhanced.leftFibration`, right lifting
  against every positive-dimensional horn `0 ≤ i < n`, and its imported Mathlib
  `SSet.InnerFibration`, right lifting against all inner horns.

The isofibration conclusion is expanded into its two defining lifting conditions instead
of adding a new definition. I read `SSet.Enhanced.IsIsofibration` in
`Sheaf.CategoryTheory.IsofibrationExponentiation`: its non-quasicategory conditions are
exactly these two clauses. Citing its owning node would introduce the dependency cycle
`lem-coef-infinity-isofibration-exponentiation` →
`lem-coef-infinity-equivalence-prism-extension` →
`lem-cbc-inner-fibration-equivalence-outer-horn-lift` →
`lem-cbc-left-fibration-equivalence-lift`. No declaration is duplicated.

Source checked online: Kerodon https://kerodon.net/tag/019K, Proposition the project server,
proves conservativity; https://kerodon.net/tag/01EW, Example the project server, states the
isofibration result. The docstring gives the inverse-triangle argument for reflection,
the one-horn argument for source lifting, and the one-horn followed by a left two-horn
for target lifting. The node has four stored proof steps and lists the same two dependencies as proof dependencies; both modules are imported publicly.
No statement correction or disputed statement was needed.

Edge cases checked before writing: empty source is allowed (all edge and vertex clauses
are vacuous, and no nonemptiness is assumed); empty base then forces an empty source.
Identity/degenerate equivalences are included without any distinct-endpoint hypothesis.
Non-surjective left fibrations remain allowed. Left lifting includes dimension one,
while `InnerFibration` includes precisely the inner horns and no zero-dimensional
surjectivity condition. The target lift uses only a left two-horn, not an assumed
right-fibration structure. An arbitrary common `u` allows all small simplicial sets
in the chosen universe, with no finite/countable bound.

Searches performed using `msearch.py Q22 lem-cbc-left-fibration-equivalence-lift`:

- LeanFinder: `A left fibration of quasicategories reflects equivalences and lifts
  equivalence edges with prescribed source or target` returned 8 hits on Quillen
  fibrations, quasicategory horn filling, truncated Segal lifting and homotopies;
  none states the requested one-sided-fibration theorem.
- Loogle: `SSet.Enhanced.leftFibration, SSet.Enhanced.IsEquivalenceEdge` returned zero
  hits (unknown side-project identifier, as expected for the Mathlib service).
- Mathlib grep: `LeftFibration|leftFibration|isofibration|IsEquivalenceEdge` under
  `AlgebraicTopology` returned zero hits.
- LeanSearch: `Left fibrations of quasicategories reflect equivalences and lift
  equivalence edges` returned 8 hits on ordinary equivalences and Quillen/model-category
  fibrations; none has the hypotheses or conclusion of this node. Read the relevant
  Quillen horn-lifting declarations in `CategoryWithFibrations.lean`: they require
  all horns, not left horns.
- Direct `rg` with the same regex in `WeilConjectures/` and `lean/Sheaf` found no
  upstream declaration and found the two dependency definitions and downstream uses.
  Inspected the existing isofibration definition and outer-horn theorem module.
- `grep -rn 'lem-cbc-left-fibration-equivalence-lift' WeilConjectures/` found no matches.
  The proposed declaration name was also searched in `dag/lean_names_upstream.json`,
  `lean/Sheaf`, and `WeilConjectures/`, with no collision.

Validation: `scompile.py Q22 lem-cbc-left-fibration-equivalence-lift` on the delivered
module completed successfully for both sandbox and library-path checks, with no warnings.

## Earlier second reading (a previous round; superseded)

I independently read the node and its four proof steps, both statement-dependency nodes,
their recorded declarations, and the delivered module. I read Kerodon Proposition
the project server (https://kerodon.net/tag/019K) and Example the project server
(https://kerodon.net/tag/01EW) online. The source is Kerodon, not a Stacks .tex passage.
Both source statements assume functors between infinity categories; they impose no
additional finiteness, nonemptiness, or surjectivity assumption. There is no repair note,
statement_change, new definition node, or dependency module in this delivery.

The node's objects, hypotheses, and conclusions, matched independently with the Lean:

1. Two small quasicategories L and M: `{L M : SSet.{u}} [Quasicategory L]
   [Quasicategory M]`. Verdict: exact. Mathlib's Quasicategory is inner-horn filling,
   as specified in def-cbc-enhanced-diagrams-cones; neither category is required to
   be Kan, inhabited, ordinary, finite, or essentially small in a lower universe.
2. A simplicial map r that is a left fibration: `(r : L ⟶ M)
   (hr : leftFibration r)`. Verdict: exact. I opened
   Sheaf.CategoryTheory.InfinityFibrations: leftFibration quantifies over n >= 1
   and i < Fin.last n, using HasLiftingProperty for the actual horn inclusion.
   This is precisely def-coef-infinity-fibrations, including the initial horns.
3. Reflection of every equivalence: the first conjunct is
   `∀ a : L _⦋1⦌, IsEquivalenceEdge M (r.app _ a) → IsEquivalenceEdge L a`.
   Verdict: exact. I opened IsEquivalenceEdge in EnhancedDiagramsCones: it uses
   an inverse edge and both inverse 2-simplices, with their long edges the correct
   source/target degeneracies. It is the dependency node's notion of equivalence.
4. Every inner horn lifts: `InnerFibration r`. Verdict: exact. I read Mathlib's
   innerHornInclusions, innerFibrations and InnerFibration: this is right lifting
   for all and only 0 < i < n, n >= 2, without a dimension-zero condition.
5. Every equivalence with prescribed source lifts to an equivalence with that source:
   the third conjunct quantifies over x and e, assumes
   `M.δ 1 e = r.app _ x` and `IsEquivalenceEdge M e`, and produces a with
   `L.δ 1 a = x`, `IsEquivalenceEdge L a`, and `r.app _ a = e`.
   Verdict: exact; δ 1 is the source. The target is unrestricted, as required.
6. Every incoming equivalence e at a prescribed y has a strict target-fixed lift:
   the fourth conjunct quantifies over y and e, assumes
   `M.δ 0 e = r.app _ y` and `IsEquivalenceEdge M e`, and produces x and a
   with `L.δ 1 a = x`, `L.δ 0 a = y`, `IsEquivalenceEdge L a`, and
   `r.app _ a = e`. Verdict: exact; δ 0 is the target. The node's m₀ is the
   source `M.δ 1 e`. Simplicial naturality and the strict image equality imply
   `r.app _ x = M.δ 1 e`, so no separate source-over-base condition is missing.
   The outer quantifiers and witnesses have the same dependence as the node;
   no lift or inverse is fixed before the incoming edge and its endpoint.

I also opened IsIsofibration in IsofibrationExponentiation. Its data are the two
quasicategory conditions plus exactly clauses 4 and 5 above. Expanding those
conditions here introduces no second definition. Importing that downstream module
would create the dependency cycle documented by the worker; the node itself spells
out the meaning of isofibration, so this expansion is the correct interface.

Edge cases: empty L gives vacuous edge/vertex clauses and satisfies inner lifting;
empty M permits a simplicial map only from empty L. No vertex-surjectivity is asserted
when the base has components outside the image. Identity and degenerate equivalences
are included. Dimension zero adds no lifting hypothesis; dimension one is explicitly
present in leftFibration and supplies the source lift. Inner lifting starts at n = 2.
The arbitrary universe u covers all small simplicial sets in the chosen universe,
with no object/morphism universe equality for an independent category being imposed.
There is no index set, ring characteristic, module zero, scheme, or algebraic degree
parameter in this node. These checks reveal no excluded case or false statement.

Independent searches, using different wording from the worker:

- LeanFinder through msearch.py: "The initial horn lifting property implies reflection
  of invertible arrows and lifting with fixed codomain in a quasi category". Eight
  results were primitive Quasicategory horn filling, StrictSegal and nerve helpers;
  none has the reflection or strict equivalence-lifting conclusion.
- Loogle through msearch.py: `SSet.InnerFibration, _ → _`. Twelve results include
  InnerFibration, its membership equivalence, its constructor, and quasicategory
  closure lemmas. I read InnerFibration.lean:58-101 and Basic.lean:30-57; these give
  the inner-fibration vocabulary, not this left-fibration theorem.
- Mathlib grep through msearch.py, subdirectory AlgebraicTopology:
  `left.?[Ff]ibration|[Ii]so[Ff]ibration|reflect.*equivalence` returned zero hits.
  A broader unscoped query using invertible/conservativ also returned unrelated
  algebra and measure-theory declarations; none concerns this statement.
- Direct rg over all of WeilConjectures with
  `left.?fibration|isofibration|reflect.*equival|equival.*lift` found only five
  incidental ordinary-equivalence, ULift and torsor-action lines; I inspected each.
  The same conceptual search in lean/Sheaf/CategoryTheory found the dependency
  definitions and downstream outer-horn, relative-coslice and isofibration results.
  I opened the outer-horn theorem signature: its conclusion is absolute outer-horn
  filling, not conservativity or the two lift clauses for a given left fibration.
  No exact existing declaration was found. The proposed full declaration name
  also has no match in dag/lean_names_upstream.json or WeilConjectures.

Mismatch found and repaired: the Lean statement itself needs no change, but H8
requires the node's proof step by step. The worker's docstring compressed node
Steps 1--2 into a homotopy-category criterion and omitted the two explicit inner
3-horn fillings. I replaced that compression by the node's four-step proof, giving
the faces and shared edges of both horns and naming the two dependency nodes.
All faces were checked against the ordered vertices: Λ³₁ produces (id_X,c,a),
and Λ³₂ then produces (b,a,id_Y), the missing inverse triangle. The source- and
target-fixed lifts use Λ¹₀ and Λ²₀ with the exact base simplex, as the node says.

The worker report's sentence "The node has no stored proof steps or proof
dependencies to import" is inaccurate for the current node: it has four steps
and proof_deps equal to its two statement dependencies. Both corresponding
modules are already public imports, so no import repair is needed. The original
Worker report is retained above as requested; this section records the correction.
No mathematical statement, node field, dependency, definition, or proof term was
changed. There remains precisely one named theorem whose whole proof is sorry.
Both docstrings have the source and blueprint marker, all Lean lines are at most
100 characters, and the node's lean.statement is verbatim the unchanged signature.
All variables and universe u are explicitly bound with autoImplicit false.

Validation after the repair: the prescribed scompile.py wrapper compiled the sole
delivered module separately in both sandbox and library-path modes, exit 0 with
no errors or warnings (1.2 seconds each). No global build or live-library edit
was run.

## Second reading by Q22

I reread the node copy, the module, both dependency node signatures and source
modules, and the two cited Kerodon source pages. The item is a statement node, with
no statement correction, new definition node, or dependency repair.

The node's objects, hypotheses, and conclusion clauses match the Lean as follows.

1. The node introduces two small quasicategories `𝓛` and `𝓜`. Lean renders these as
   `{L M : SSet.{u}} [Quasicategory L] [Quasicategory M]`, with one explicitly bound
   arbitrary universe `u`. Verdict: exact; there is no finiteness, Kan, inhabitedness,
   or lower-universe restriction.
2. It introduces a simplicial map `r : 𝓛 ⟶ 𝓜` and assumes it is a left fibration.
   Lean renders `(r : L ⟶ M) (hr : leftFibration r)`. I read
   `SSet.Enhanced.leftFibration`: it quantifies over `n ≥ 1` and every
   `i < Fin.last n`, hence exactly the left/initial horns, including the one-horn
   case. Verdict: exact, with no stronger fibration assumption.
3. The conservativity clause says every edge whose image is an equivalence is itself
   an equivalence. Lean renders
   `∀ a : L _⦋1⦌, IsEquivalenceEdge M (r.app _ a) →
   IsEquivalenceEdge L a`. I read `IsEquivalenceEdge` in
   `EnhancedDiagramsCones`; it is the inverse edge plus both specified inverse
   2-simplex witnesses. Verdict: exact, with the dependency's notion and quantifier.
4. The isofibration's inner-horn clause is rendered as `InnerFibration r`. Mathlib's
   declaration is the right lifting property for all and only inner horns
   (`n ≥ 2`, `0 < i < n`). Verdict: exact; no outer or zero-dimensional lifting was
   added.
5. The prescribed-source equivalence lift is rendered by
   `∀ (x : L _⦋0⦌) (e : M _⦋1⦌), M.δ 1 e = r.app _ x →
   IsEquivalenceEdge M e → ∃ a, L.δ 1 a = x ∧ IsEquivalenceEdge L a ∧
   r.app _ a = e`. Here `δ 1` is the source, the image equality is strict, and the
   target is unrestricted. Verdict: exact.
6. The additional prescribed-target clause is rendered by
   `∀ (y : L _⦋0⦌) (e : M _⦋1⦌), M.δ 0 e = r.app _ y →
   IsEquivalenceEdge M e → ∃ (x : L _⦋0⦌) (a : L _⦋1⦌),
   L.δ 1 a = x ∧ L.δ 0 a = y ∧ IsEquivalenceEdge L a ∧ r.app _ a = e`.
   Thus `y` is the prescribed target, `x` is existential, and the image is exactly
   `e`; naturality gives the required source-over-`m₀` relation without an extra
   hypothesis. Verdict: exact.

The module expands “isofibration” into the two clauses stated by the node instead of
importing the downstream `IsIsofibration` definition. This is necessary to avoid the
recorded dependency cycle and introduces no second notion. The declaration docstring
contains all four node proof steps: lift an inverse triangle, obtain the second inverse
triangle by the two inner 3-horn fillings, deduce inner/source lifting, and lift an
inverse from the prescribed target followed by its left 2-horn. Each step names the
relevant dependency and preserves the strict image equalities.

Edge cases checked: empty `L` makes the edge and vertex conclusions vacuous; an empty
`M` admits only the corresponding empty-source map. Degenerate and identity edges are
included. No surjectivity or nonemptiness is assumed. Left fibrations include dimension
one initial-horn lifting, while inner fibrations begin at dimension two. The common
arbitrary universe `u` covers all simplicial sets in that universe; no characteristic,
index, scheme, or zero-object case occurs.

Independent duplicate searches found no existing declaration. LeanFinder, queried with
“left fibration quasicategory reflects equivalences prescribed source target”, returned
only all-horn Quillen/model-category fibrations. Loogle queried with
`SSet.Enhanced.leftFibration IsEquivalenceEdge` returned zero hits (unknown side-project
constant). Direct `rg` over Mathlib AlgebraicTopology, slopmaster2 `WeilConjectures`,
project `lean/Sheaf`, and `dag/lean_names_upstream.json` found no theorem with this
statement or declaration name; the only project matches are the dependency definitions,
the downstream outer-horn citer, and unrelated isofibration results.

No mismatch was found in the current module or node copy, and no change to the item
statement, dependencies, or proof fields was needed. The prior worker's compressed proof
comment was already replaced in the module by the explicit four-step docstring before
this reading. I added the item's `lean` record to the node copy, retaining its verbatim
multiline signature. The prescribed `scompile.py` check compiled the module separately
in sandbox and library modes with no errors or warnings beyond the postponed `sorry`.
