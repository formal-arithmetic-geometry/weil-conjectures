## Worker report

The module `Sheaf.AlgebraicTopology.OrdinaryTwoSidedBarComparison` states
`SSet.OrdinaryTwoSidedBar.ordinary_two_sided_bar_comparison` with `sorry`.
It explicitly constructs the trisimplicial two-sided bar and its diagonal, and the
canonical maps of those objects under all changes of the base and endpoint data.
The second end uses the already published ordinary two-sided category and its
canonical functor, rather than making a second category of triples.

The retained sandbox originally contained only dispatcher brief markers. N9's
existing delivery was the stage-1 split, not a Lean statement. The present delivery
adds the missing stage-2 `lean` record, module and worker report. It changes no
other node field. There is no statement correction or disputed mathematical clause.
There are no new nodes or dependency modules.

### Clause-by-clause reading

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small ordinary category C; values small in a fixed larger universe | `Data.base : Cat.{u,u}` and `Data.left`, `Data.right` valued in `Cat.{max u v,max u v}`. Both universes are explicit and independent; enlarging the universe covers all small data. |
| Contravariant F and covariant G | `Data.left : baseᵒᵖ ⥤ Cat ...` and `Data.right : base ⥤ Cat ...`. |
| Objects `(a,c,b)` of E | `TwoSidedSimplicialGrothendieck.Total X.left X.right`, already published: `Grothendieck (projection X.left ⋙ X.right)`. Its first base object is `op ⟨op c,op a⟩`, and its second fiber object is b. |
| Arrows `(h,u,v)` | In the opposite first Grothendieck construction, the base is h and the fiber is `u : a ⟶ F(h)a'`; the second Grothendieck arrow adds `v : G(h)b ⟶ b'`. |
| Composition and identities in E | Mathlib's `Grothendieck.comp` and `Grothendieck.id`, with the first category taken opposite, give `(h'h,F(h)(u')u,v'G(h')(v))` and the component identities, with functoriality equality transports. No arbitrary category structure is supplied as a hypothesis. |
| Trisimplicial degree `(i,k,j)` | `Indices` orders coordinates as `((i,k),j)`. `terms X n` is a sigma over `ComposableArrows X.base k.len` of the product of the i-nerve of F at the last vertex and the j-nerve of G at the first vertex. `trisimplicial` packages these real data. |
| Ordinary nerve operators in i and j | `operator` uses the `.map f.1.1` and `.map f.2` operators of the actual Mathlib nerves, respectively. |
| Interior k faces compose arrows | The base chain is `z.1.whiskerLeft a` for the monotone functor a of the k-operator. Omitting an interior vertex composes its adjacent arrows. |
| k face d_0 applies G(h_1) | The right factor is transported by `X.right.map (z.1.map (homOfLE (Fin.zero_le (a.obj 0))))`. For d_0 this is the arrow c_0 to c_1. |
| k face d_k applies F(h_k) | The left factor is transported by `X.left.map (z.1.map (homOfLE (Fin.le_last (a.obj (Fin.last ...))))).op`. For d_k this is the arrow c_(k-1) to c_k, with the required opposite variance. |
| k degeneracies repeat a vertex with identity | Restriction along the corresponding noninjective monotone map repeats that vertex. The chain functor sends the resulting repeated-vertex arrow to an identity. The two endpoint transports are identities. |
| All trisimplicial identities and commuting directions | `operator_laws` is the named proof obligation, followed by the actual `trisimplicial` functor. It includes identity and composition for every morphism in the threefold product category, hence interchange. |
| B_r = T_(r,r,r), all operators together | `diagonalIndex` repeats the index and operator in all coordinates, and `bar X := diagonalIndex ⋙ trisimplicial X`. |
| Arbitrary H:C'→C, α:F'⇒F Hᵒᵖ, β:G'⇒GH | A `Change X Y` contains `base : X.base ⥤ Y.base`, `left : X.left ⟶ base.op ⋙ Y.left`, and `right : X.right ⟶ base ⋙ Y.right`. It has no additional field. |
| At B, apply H to the chain and α,β to endpoint nerves | `changeTerms` uses `z.1 ⋙ f.base` and the actual nerve maps of `f.left.app (op z.1.right)` and `f.right.app z.1.left`. `barMap` uses its simultaneous diagonal. |
| At NE, the nerve of `(α,H,β)` | `totalNerveMap f := nerveMap (TwoSidedSimplicialGrothendieck.totalMap f.base f.left f.right)`. The existing `totalMap` applies exactly those three components. |
| Functoriality, including identities and composition | `identity`, `compose`, `change_laws`, and `dataCategory` specify the parameter category; `changeTerms_laws` and `totalNerveMap_laws` make `barFunctor` and `totalNerveFunctor` honest functors. |
| One finite zigzag of a fixed shape, natural in all data | The main theorem is `Relation.ReflTransGen` on the type `Data ⥤ SSet`, from `barFunctor` to `totalNerveFunctor`. A link is a natural transformation in either orientation whose every component is a weak homotopy equivalence. Reflexive-transitive closure is the finite inductive closure (`refl` and `tail`), not an objectwise assertion. The entire path, its length, orientations and intermediate functors are chosen before evaluating at any Data. |
| Every arrow commutes with every change; intermediate maps preserve identity and composition | Each link is a natural transformation of genuine functors on the whole parameter category. Its naturality square is exactly the required commuting square for every `(H,α,β)`; intermediate functor laws give identity and composition. |
| Weak homotopy equivalence means the realization criterion | Every link uses the already published `SSet.Enhanced.IsWeakHomotopyEquivalence`, the same predicate used by the recorded zigzag-calculus dependency. |
| No equivalence hypothesis on H, α, β | There is no such hypothesis in `Change`, in the two endpoint functors, in the link relation, or in the main statement. |

### Dependencies and reuse

Read the complete item statement, its seven proof steps, both statement dependencies,
and the recorded dependency declarations and docstrings.

* `def-coef-zigzag-homotopy-calculus` records
  `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus`, particularly
  `CategoryTheory.RelativeZigzag.HasTwoSidedHomotopyCalculus` and `zigzagNerve`.
  They use Mathlib's ordinary `nerve` and `nerveMap` and the published realization
  weak-equivalence predicate in `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
  This item uses exactly those notions, without a new weak-equivalence definition.
* `def-weil-pbc-simplicial-set` is a Mathlib leaf. Its `mathlib_match` lists `SSet`,
  `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, and `SSet.Finite`.
  Read their full definitions in Mathlib's Basic, Degenerate, Subcomplex and Finite
  modules. This statement needs `SSet` and `SimplexCategory`; it imposes no finiteness
  or nondegeneracy condition.
* `CategoryTheory.TwoSidedSimplicialGrothendieck.projection`, `Total`, `oplaxMap`,
  and `totalMap` are reused from
  `Sheaf.CategoryTheory.Localization.TwoSidedSimplicialGrothendieckInvariance`.
  Read their definitions in the shared source and confirmed the current source via
  `scompile.py --source`. They already supply exactly E and its canonical map.
  This import is for construction helpers, not the downstream invariance theorem.
* All five stated proof-dependency modules are directly imported, without `public`:
  `Sheaf.AlgebraicTopology.BisimplicialDiagonalEquivalence`,
  `Sheaf.AlgebraicTopology.BousfieldKanComparisonCalculus`,
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `Sheaf.CategoryTheory.NerveNaturalHomotopyEquivalence`, and
  `Sheaf.AlgebraicTopology.ThomasonGrothendieckComparison`.
  Read the BK chain operators and Thomason's Gr/grMap/grPre definitions before
  writing the bar operators.

Import-cycle note for the maintainer: the existing downstream simplicial-invariance
module owns the ordinary Total/totalMap helpers. To reuse them without duplicate
notions, the present module imports it. Consequently the reverse proof-dependency
import from that module to this one must be omitted by the ordinary import-cycle
rule. The downstream module currently has no reverse import. No parent theorem is
used in this item's construction or proof plan; the inherited DAG remains unchanged.
A later movement of those helpers to an earlier common module can remove this
organizational limitation, but is outside this worker's authorized file changes.

### Edge cases and universes

* Empty C: `terms` has no base chain because every ordinal has vertex zero. Both
  the bar and the iterated Grothendieck nerve are empty. Changes from empty bases
  are included; no Nonempty instance is required.
* Empty endpoint fibers: the corresponding nerve factor is empty, so exactly its
  summands vanish. No inhabitedness is required for either endpoint functor.
* k=0: a chain has one object. Both endpoint transport arrows are identities;
  the term is precisely N_iF(c) × N_jG(c). There is no invalid last face at k=0.
* i=0 or j=0: a nerve zero-simplex is an object. The same formulas apply, including
  simultaneous degree zero on the bar and total nerve.
* Terminal C: the construction reduces to the product of the two fiber nerves,
  and E to the product category, with the expected endpoint actions.
* Terminal endpoint functors: bar terms reduce to base chains, hence to NC;
  E reduces to C. Empty bases remain included in this specialization.
* Identity changes and composite changes are part of the explicit construction-law
  statements; no equivalence or fibrancy assumption is hidden in the interface.
* `u` and `v` are explicitly bound. The base is u-small; endpoint values are small
  in `max u v`. No equality between independent universes is imposed. The universe
  linter on the bundled `Data` declaration is locally disabled because the two
  levels occur together in its resulting type while its fields genuinely use
  the base universe and larger value universe separately. No mathematical size
  assumption is added by this linter setting.

### Searches and source check

Fresh prescribed searches for this item:

* LeanFinder: `two sided bar construction of nerves of categories weak equivalence
  Grothendieck construction` — eight hits, all nerve/homotopy-category adjunction,
  truncation or product-comparison results; none states this comparison.
* Loogle: `"Grothendieck", "nerve"` — zero hits.
* Mathlib grep through msearch: `two.?sided.*bar|Thomason` — zero hits.
* `rg` over upstream `WeilConjectures` for `two.?sided.*bar|Thomason` — no match;
  exact item-id grep over the same source — no match.
* `rg` over `lean/Sheaf` for `OrdinaryTwoSided`, `ordinaryTwoSided`,
  `TwoSidedBarComparison`, `ordinary two-sided`, and `two_sided` — the downstream
  simplicial-invariance module has the reusable ordinary constructions but only
  states invariance, with no ordinary bar-to-total-nerve comparison.
* Additional LeanFinder query `simplicial set functor simplex category finite
  nondegenerate simplices` confirmed SSet.N, SSet.Finite and the standard SSet API.

The original node also records independent LeanSearch, LeanFinder, Loogle and
Mathlib grep searches; those records were retained unchanged and are not attributed
to this worker. Mathlib's ComposableArrows and Grothendieck definitions were read;
they give the chain and category data, not the requested comparison theorem.

Opened the cited Dwyer--Kan PDF online and read Definition 9.1, Proposition 9.5,
Lemma 9.7 and proofs 9.9–9.10 (PDF pages 14–17, printed pages 31–33), including
its terminal-slice homotopy-colimit argument and the naturality before 9.2.
The node uses the same convention after reversing the source's base-chain indices.
The complete seven-step natural-language proof is in the main theorem's docstring.
The four named law theorems are only the construction and functoriality clauses of
this same node, each with its own source, blueprint id and complete proof docstring.
No data are chosen from an unproved existence statement.

### Validation

`scompile.py Q62 lem-coef-ordinary-two-sided-bar-comparison` compiled the single
module both under the sandbox name and at its intended library path, with no
errors or warnings (1.9 s and 2.0 s). Every definition has real data, all five theorem
proofs are exactly `sorry`, and every declaration is recorded in `lean.declarations`.
All lines are at most 100 characters. The signature is copied verbatim into the
node's `lean.statement`; the node retains its original non-Lean fields and JSON
layout (indent 1, Unicode retained, final newline).

The required deliver2 dry run is the final validation step. No push is authorized;
the independent second reader supplies the second-reading section.

## Second reading by Q62

I read the node statement against Dwyer--Kan, *Calculating simplicial localizations*,
Definition 9.1, Proposition 9.5, Lemmas 9.7--9.8 and proofs 9.9--9.10 (printed
pp. 31--33, PDF pp. 15--17), then matched every clause with the Lean declarations.

* The small base category and fixed larger universe are `Data.base : Cat.{u,u}` and
  endpoint values `Data.left` and `Data.right` in `Cat.{max u v,max u v}`. Verdict:
  same smallness convention, with both universe parameters explicit.
* The contravariant and covariant functors are exactly
  `Data.left : baseᵒᵖ ⥤ Cat ...` and `Data.right : base ⥤ Cat ...`. Verdict: variance
  and domains match, with no extra hypotheses.
* The category of triples and its arrows are the published
  `TwoSidedSimplicialGrothendieck.Total`, whose iterated Grothendieck construction
  has objects `(a,c,b)` and components `(h,u,v)` with the stated composition.
  Verdict: the existing canonical construction is reused; no private duplicate is
  introduced.
* `terms` is the coproduct over `ComposableArrows` of the base of
  `N_i F(c_k) × N_j G(c_0)`. Verdict: this is exactly the trisimplicial degree
  `(i,k,j)` in the node.
* `operator` restricts chains, composes interior arrows, applies `G(h₁)` at `d₀`,
  applies `F(h_k)` at `d_k`, and repeats vertices for degeneracies; `operator_laws`
  supplies all three-direction identities and interchange. Verdict: every listed
  bar operator is present with the correct endpoint variance.
* `diagonalIndex` and `bar` give `B_r = T_{r,r,r}` with all operators together.
  Verdict: exact diagonal clause.
* `Change` contains precisely `H`, `α : F' ⇒ F Hᵒᵖ`, and `β : G' ⇒ G H`; `changeTerms`
  applies these to chains and endpoint nerves. Verdict: arbitrary changes are allowed,
  with no equivalence, nonemptiness, or fibrancy assumption.
* `barFunctor`, `totalNerveFunctor`, `changeTerms_laws`, and `totalNerveMap_laws`
  encode identity and composition in the full data category. Verdict: maps commute
  with every change and preserve identities/composition as required.
* `ordinary_two_sided_bar_comparison` is `Relation.ReflTransGen` of natural
  transformations in either direction, pointwise satisfying
  `Enhanced.IsWeakHomotopyEquivalence`, between the two endpoint functors. Verdict:
  this gives one finite, fixed-shape zigzag before evaluation at any data and has the
  exact weak-equivalence predicate from the dependency node.

Edge cases checked: an empty base category gives empty coproducts; empty endpoint
fibers simply remove the corresponding summands; a zero-length base chain has both
endpoint actions equal to identities; `i = 0` and `j = 0` use ordinary nerve
zero-simplices; a terminal base or terminal endpoint functor reduces to the expected
product or base nerve. No `Nonempty`, characteristic, finiteness, or universe equality
hypothesis is introduced. The `u,v` binders are all explicit under `autoImplicit false`.

For the independent H4 search I ran LeanFinder for “ordinary two-sided bar
Grothendieck nerve weak equivalence”, Loogle for “two-sided bar nerve Grothendieck”,
and `rg` searches for `two-sided bar`, `bar.*Grothendieck`, `ordinaryTwoSided`, and
`OrdinaryTwoSided` through Mathlib, the upstream `WeilConjectures` tree, this
project's `lean/Sheaf`, and `dag/nodes`. The searches found only ordinary nerve,
Grothendieck helper, or this item's downstream use; no existing declaration states
the comparison. The published `Total` and `totalMap` helpers were read in full and
are the correct canonical notions.

No mismatch was found, so no Lean or node field was changed. The module was compiled
with `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q62
lem-coef-ordinary-two-sided-bar-comparison
lean/Sheaf/AlgebraicTopology/OrdinaryTwoSidedBarComparison.lean`; sandbox and library
compilations completed with no errors or warnings beyond permitted `sorry` declarations.
The sole direct citer, `lem-coef-two-sided-simplicial-grothendieck-invariance`, uses
the ordinary comparison exactly as stated, so its `holds` verdict remains true.
