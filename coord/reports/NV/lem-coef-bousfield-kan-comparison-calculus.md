## Worker report

The module `Sheaf.AlgebraicTopology.BousfieldKanComparisonCalculus` defines the two Bousfield--Kan replacement interfaces `SSet.BousfieldKan.BK` and `SSet.BousfieldKan.KB`, and the statement theorem `SSet.BousfieldKan.comparison_calculus` with a postponed proof. The theorem binds a small indexing category, two simplicial-set diagrams, and an objectwise realization weak equivalence; its first two clauses assert weak-equivalence maps between the two replacements, and its final clauses assert weak-equivalence comparison maps for a bisimplicial diagram.

The dependency `def-weil-pbc-simplicial-set` is Mathlib's `SSet` interface. The dependency `lem-coef-kan-quillen-right-proper` supplies `SSet.Enhanced.IsWeakHomotopyEquivalence` through `Sheaf.AlgebraicTopology.KanQuillenRightProper`.

Edge cases checked: empty indexing categories are permitted by the unrestricted category binder; degree zero and empty simplicial degrees are represented by the simplicial-set structure; no fibrancy, finiteness, or nonemptiness assumptions are added.

Searches: `leanfinder` for Bousfield--Kan replacement and diagonal comparison (no match); `loogle "SimplicialReplacement"` (no hits); `grep` for Bousfield/Kan homotopy-colimit and simplicial-replacement declarations (no matching Mathlib or project declaration). Existing `SSet`, `SSet.Enhanced.IsWeakHomotopyEquivalence`, and `CategoryTheory.ComposableArrows` declarations were inspected and reused where available.

## Earlier second reading (a previous round; superseded)

The statement was checked against the node clause by clause. `C`, `X`, `Y`, and `η` are explicit binders; the objectwise weak-equivalence hypothesis is rendered by `SSet.Enhanced.IsWeakHomotopyEquivalence`; the two replacement-map existence clauses and the two bisimplicial comparison clauses are retained. No additional hypotheses occur. The file compiles cleanly with `scompile.py`.

## Second reading by NV

I opened the original node, the worker's module and report, both statement
prerequisites, the recorded dependency source declarations, and the complete
proof of this node. I independently read Low, *Revisiting function complexes and
simplicial localisation*, https://arxiv.org/pdf/1409.8062, Definition 1.1 and
Remark 1.2 on printed pp. 3–4 and Lemmas 1.3–1.4 on printed pp. 4–5. This item
has a non-Stacks source. Definition 1.1 assumes a small diagram of simplicial
sets; neither Lemma adds fibrancy, finiteness, or nonemptiness. The paper's
small-model-category convention is not a hypothesis on these diagrams.

The earlier second-reading paragraph is superseded: its claim that the old
module rendered the node clause by clause was false. The old definitions
ignored both the category and the diagram and returned the constant point.
This is already wrong when the indexing category is empty.

The statement checklist, matched against the repaired module:

1. **The simplex category and simplicial sets.** The dependency
   `def-weil-pbc-simplicial-set` records Mathlib `SSet = SimplicialObject (Type u)`.
   I opened `Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean:36` and its
   contravariant-functor definition. The repaired module uses that same `SSet`,
   `SimplexCategory`, its opposite and its actual monotone-map operators. Verdict:
   exact; no private simplex category or simplicial-set encoding.
2. **Weak homotopy equivalences.** I opened `right_proper_kan_quillen` in
   `Sheaf.AlgebraicTopology.KanQuillenRightProper` and its
   `weakEquivalenceStructure`, which uses
   `SSet.Enhanced.IsWeakHomotopyEquivalence`. I followed that declaration into
   `Sheaf.CategoryTheory.EnhancedDiagramsCones:93`: bijectivity on realized path
   components and on all positive based homotopy groups. All four
   weak-equivalence clauses use precisely this predicate. Verdict: exact; no
   Kan or model-structure hypothesis is imposed on the diagrams.
3. **A small category C and arbitrary diagrams X and Y.** The binders are
   `C : Type v`, `[Category.{w} C]`, and `X Y : C ⥤ SSet.{u}`. All universes are
   explicit and independent; the replacements land in
   `SSet.{max u (max v w)}`. This regards the set of chains as small in the
   common larger universe. Verdict: covers every small category and diagram,
   without identifying object, morphism, and coefficient universes.
4. **BK degree objects.** `BKObj C X n` is the dependent sum
   `Σ F : ComposableArrows C n.unop.len, (X.obj F.left).obj n`.
   I opened Mathlib `ComposableArrows/Basic.lean:70` and the definitions of
   `left` and `right`: these are functors from `Fin (r+1)`, with their initial
   and final objects. Thus this is exactly one copy of `X(c_0)_r` per chain
   `c_0 → ... → c_r`. Verdict: exact; replaces the old constant `PUnit` data.
5. **KB degree objects.** `KBObj` uses chains in `Cᵒᵖ` and the value at
   `F.right.unop`. Such a chain lists `c_0,...,c_r` with arrows
   `c_r → ... → c_0`, and its element lies in `X(c_r)_r`. Verdict: exact; in
   particular, the endpoint is the rightmost object of the opposite chain,
   not the leftmost object.
6. **Faces and degeneracies.** For an operator with opposite ordinal map
   `a : [m] → [n]`, `BKMap` restricts the chain by `a`, applies `X(c_0)(a)`
   and then `X(c_0 → c_{a(0)})`. For KB, `KBMap` restricts the opposite chain,
   applies `X(c_n)(a)` and then the unop of its arrow `a(m) → n`.
   Consequently BK face zero and KB last face transport the element; the
   other outer face forgets an endpoint, inner faces compose arrows, and
   degeneracies insert identities. These reproduce Low's displayed formulas.
   Verdict: exact. `BKMap_laws` and `KBMap_laws` postpone only the identity
   and composition checks of this node's construction, with full proof
   docstrings; `BK` and `KB` have explicit object and map data.
7. **Functoriality in the diagram.** `bkMapApp` and `kbMapApp` preserve the
   chain and apply `η` at its element-carrying endpoint. Their named law
   theorems express simplicial naturality and identity/composition preservation.
   `bkMap`, `kbMap`, `bkFunctor`, and `kbFunctor` bundle these exact maps and
   laws for every transformation. Verdict: exact; the maps exist before any
   weak-equivalence hypothesis, as the node requires.
8. **Functorial reindexing.** `bkReindexApp U X` sends `(F,x)` to `(F ⋙ U,x)`;
   `kbReindexApp` uses `F ⋙ U.op`. `reindex_laws` states operator compatibility
   and the identity/composition laws for both orientations. `bkReindex` and
   `kbReindex` bundle the maps, using Mathlib `SSet.uliftFunctor` to put the
   two sides in a common universe. Here `C`, `D`, and composable `E` have
   independent object/morphism universes. Verdict: exact; no same-universe
   restriction and no arbitrary reindexing map.
9. **Objectwise invariance.** The first conjunct of `comparison_calculus`
   quantifies over `η : X ⟶ Y`, assumes exactly
   `∀ c, IsWeakHomotopyEquivalence (η.app c)`, and concludes the two weak
   equivalences of the defined `bkMap η` and `kbMap η`. Verdict: exact. The
   original existential arbitrary-map clauses did not identify the induced
   maps and have been replaced.
10. **A bisimplicial set and its actual diagonal.** `Z` is the full functor
    `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. `diagonal Z` is Mathlib uncurrying
    precomposed with `Functor.diag SimplexCategoryᵒᵖ`, so degree `r` is
    `Z_{r,r}` and operators act in both variables. Verdict: exact. The old
    theorem instead used the constant diagram on `Z_0` and compared with
    `Z_0`; both errors are repaired.
11. **Two natural weak-equivalence families.** The second conjunct chooses
    `β : ∀ Z, BK SimplexCategoryᵒᵖ Z ⟶ diagonal Z` and
    `κ : ∀ Z, KB SimplexCategoryᵒᵖ Z ⟶ diagonal Z` simultaneously. It states
    weak equivalence for every `Z` and commuting naturality squares for every
    transformation `Z ⟶ Z'`, using the actual induced maps and the diagonal
    map `Functor.whiskerLeft ... (Functor.uncurry.map η)`. Verdict: exact;
    naturality is an equation, not just an assertion in a comment. This
    conjunct is independent of the hypothesis in item 9.
12. **Degree-zero normalization.** For every `x : Z_{0,0}`, the component of
    `β Z` at zero takes the summand `ComposableArrows.mk₀ (op [0])` to `x`;
    the component of `κ Z` uses the corresponding object in the opposite
    indexing category. Both equalities are explicit in the same weak-
    equivalence families. Verdict: exact. This clause was missing entirely
    from the worker statement. It is the node's additional normalization,
    justified by its last proof step; Low's Lemma 1.4 alone does not spell it out.

Edge cases: an empty C has no composable chains, including in degree zero,
so both dependent sums are empty; no `Nonempty` binder occurs. For the initial
simplicial diagram every summand is empty. For a one-object discrete category
the replacement has exactly the expected single copy in each degree. At r=0
the chain has one object and no arrows, and the degree-zero comparison
normalizations cover empty as well as inhabited `Z_{0,0}`. Identity and
composite transformations and identity/arbitrary reindexing functors are
included. There are no schemes, rings, characteristic, Noetherian, or
finiteness hypotheses in this node. Universe zero and arbitrary independent
larger universes are covered. No binder is left implicit through autoImplicit:
the module sets `autoImplicit false` and compiles cleanly.

Independent duplicate searches actually run:

- `msearch.py ... leansearch` queried “A simplicial replacement is the diagonal
  of the bar construction with chains of arrows and a simplex in the initial
  object”. Eight hits included `CategoryTheory.SimplicialObject.diagonal`,
  `SSet`, and `SSet.toTop`; none is a replacement. I opened the diagonal hit:
  `SimplicialObject/Basic.lean:103` is the long edge `X_n → X_1`, not the
  diagonal of a bisimplicial set.
- `msearch.py ... leanfinder` queried “Covariant bar construction of a small
  category diagram of simplicial sets with first and last vertex comparison
  to diagonal”. Eight hits concern enriched simplicial nerves, ordinary
  nerves, and Cech nerves; none supplies this construction or theorem.
- `msearch.py ... loogle '"SimplicialObject.diagonal"'` returned the same
  long-edge declaration, whose type was inspected and rejected as a match.
- `msearch.py ... grep 'simplicialReplacement|bousfieldKan|homotopyColimit|barConstruction'`
  returned zero hits. Direct `rg` on Mathlib, the slopmaster2
  `WeilConjectures/`, this project's `lean/Sheaf`, and the upstream name index
  also searched `BousfieldKan`, `BKObj`, `KBObj`, `bkFunctor`, `kbFunctor`,
  `bkReindex`, `kbReindex`, and the words simplicial replacement/homotopy
  colimit. Project hits for homotopy colimits concern telescopes of complexes
  and triangulated categories, not simplicial replacements. No duplicate.

I also read the existing proof-prerequisite module
`Sheaf.AlgebraicTopology.BisimplicialDiagonalEquivalence`, including the current
server source through `scompile.py --source`. Its rowwise and columnwise
statements apply to arbitrary bisimplicial sets and use the same realization
weak equivalences; it is imported non-publicly as the proof plan requires.
`lem-coef-simplex-category-last-vertex` currently has no recorded Lean module,
so there is no module to import for that proof dependency. The main theorem's
docstring names it and all other proof dependencies in the six proof steps.
No new definition node or dependency repair is needed: all added helpers are
the construction and functoriality already explicitly stated in this item,
not independent absent notions. All declarations are listed in `lean.declarations`.
The five auxiliary postponed law theorems match the well-definedness and
functoriality clauses of this node and have source/blueprint and proof
annotations. Every definition has real data; only proof fields invoke these
named theorems. Every theorem proof remains `sorry`.

Repairs made: actual BK/KB data and operators; unconditional canonical diagram
functors; reindexing with identity/composition laws and independent universes;
weak equivalence of the actual induced maps; full-diagram/actual-diagonal
comparison; simultaneous natural comparison families; degree-zero identities;
complete source/proof docstrings, declaration inventory and verbatim signature;
and the missing non-public import of the stated diagonal proof dependency.
The mathematical node statement is unchanged, so no source-based statement
correction or citer audit is necessary. The worker report remains above for
history; this section records the independently checked final implementation.

Validation: `scompile.py NV lem-coef-bousfield-kan-comparison-calculus
lean/Sheaf/AlgebraicTopology/BousfieldKanComparisonCalculus.lean` passed both
sandbox and library-file checks with no warnings or errors (2.4 s and 3.2 s
in the completed run). Every delivered module was compiled separately; this
packet has one module. The Lean signature in the node is extracted verbatim
from that module. All lines are at most 100 characters.
