## Worker report

The module `Sheaf.Topology.CompactClosedT1Chain` states
`TopCat.compact_closedT1_chain_factorization`, with one `sorry` and no definitions or
helper theorems. The node is unchanged except for `lean`. There are no new nodes,
dependency repairs, statement corrections, or disputed statements.

Source checked: Hovey, *Model Categories*, Section 2.4, Lemma 2.4.1 and Proposition
2.4.2, printed pp. 49–50. I opened the online PDF and downloaded it into this item's
`scratchpad/hovey-model-cats.pdf`; extracted pp. 49–50 are in
`scratchpad/hovey-49-50.txt` (with the preceding printed p. 48). The source identifies
Top colimits with set colimits carrying the final topology. Its printed definition
of closed T1 inclusion contains the previously documented extra “not”; the node
already uses the intended relative condition, closedness of points outside the image.
I followed the node, including its expanded proof repairing the source's abbreviated
compactness contradiction.

Clause-by-clause correspondence:

- A nonzero limit ordinal is `(κ : Ordinal.{u}) (hκ : Order.IsSuccLimit κ)`.
  `Order.IsSuccLimit` excludes both zero and successors, as confirmed in
  `Mathlib.SetTheory.Ordinal.Arithmetic` (`Ordinal.isSuccLimit_iff`). Lean reserves
  the character lambda as syntax, so the formal ordinal binder is named kappa.
- The ordinal chain of topological spaces is `F : Set.Iio κ ⥤ TopCat.{v}`.
  Objects are exactly the ordinals less than kappa, with the inherited preorder
  category; the functor supplies continuous transition maps and their composition
  and identity laws.
- Continuity at every nonzero limit below kappa is `[F.IsWellOrderContinuous]`.
  Its source definition quantifies over `Order.IsSuccLimit m` and makes the canonical
  cocone from all objects less than `m` a colimit. For the initial ordinal interval,
  these are exactly its nonzero limit ordinals. In TopCat this gives the underlying
  set union with the final topology, not just a topology equality on an unrelated set.
- Successor pairs are `(i j : Set.Iio κ) (hij : i ⋖ j)`. Covering in an initial ordinal
  interval means exactly that j is the successor of i. `homOfLE hij.le` is the
  corresponding transition arrow.
- The injective continuous closed-subspace condition is
  `hclosed : ∀ i j hij, IsClosedEmbedding (F.map (homOfLE hij.le))`.
  `Topology.IsClosedEmbedding` extends `IsEmbedding` with closed range;
  `IsEmbedding` includes injectivity and the induced source topology. Continuity
  is also already supplied by the TopCat morphism. This is precisely a closed
  inclusion, rather than only an injective closed-range continuous map.
- The relative T1 condition is `hT1`: for every such successor pair and
  `y : F.obj j`, `y ∉ Set.range (F.map (homOfLE hij.le))` implies
  `IsClosed ({y} : Set (F.obj j))`. No global T1 assumption occurs.
- The final union X and its canonical stage inclusions are `(c : Cocone F)` and
  `(hc : IsColimit c)`, with X represented by `c.pt` and inclusions by `c.ι.app i`.
  This is exactly the dependency's colimit universal property. TopCat colimits are
  set colimits with final topology, as in Hovey and Mathlib's
  `TopCat.coinduced_of_isColimit` and `TopCat.isOpen_iff_of_isColimit`.
  The successor embedding and continuity assumptions ensure the resulting set
  colimit is the set-theoretic union. Choosing an arbitrary universal cocone changes
  no mathematical assertion: it identifies with the constructed union by its unique
  TopCat isomorphism. I do not assume embeddings of the final cocone maps; those
  are proved by the transfinite closed-subset argument in the proof plan.
- The compact topological source is `(A : TopCat.{v}) [CompactSpace A]`.
  CompactSpace is compactness by finite subcovers, without separation assumptions.
- Every continuous map is quantified by `∀ f : A ⟶ c.pt`. A continuous lift is
  `∃ (i : Set.Iio κ) (g : A ⟶ F.obj i)`, and the factorization equation is
  `g ≫ c.ι.app i = f`. These are bundled continuous maps, not arbitrary functions.
- The equivalent continuous-map-set diagram is `F ⋙ coyoneda.obj (op A)`.
  Co-Yoneda evaluates at a stage to the set `A ⟶ F.obj i` and acts by
  postcomposition with its transition maps. It carries no compact-open topology.
- A chosen set colimit is `(s : Cocone (F ⋙ coyoneda.obj (op A)))`
  with `(hs : IsColimit s)`. The compatible family to `A ⟶ c.pt` is precisely
  `((coyoneda.obj (op A)).mapCocone c)`. Its canonical map is
  `hs.desc ((coyoneda.obj (op A)).mapCocone c)`, and the second conjunct says
  `Function.Bijective` of this map. Quantification over all choices of the universal
  cocone is equivalent to the assertion for the chosen colimit of the dependency.
  This quantification is inside the second conjunct: no Hom-colimit-existence
  hypothesis restricts the continuous-factorization clause.

Dependency declarations read and used:

- `def-weil-pbc-category-colimit` is a Mathlib leaf. Its recorded module is
  `Mathlib.CategoryTheory.Limits.HasLimits`, imported publicly. I read its
  `colimit`/`colimit.desc` interface (generated by duality from the displayed limit
  declarations) and the full `IsColimit` definition in
  `Mathlib.CategoryTheory.Limits.IsLimit`, also imported by HasLimits. The statement
  uses `CategoryTheory.Limits.Cocone`, `CategoryTheory.Limits.IsColimit`, and
  `CategoryTheory.Limits.IsColimit.desc` directly, as the leaf's recorded
  universal-property interface permits. No private colimit is defined.
- `Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous`:
  `CategoryTheory.Functor.IsWellOrderContinuous`, whose full docstring and field
  were read; its canonical cocone is `(Set.principalSegIio m).cocone F`.
- `Mathlib.Topology.Category.TopCat.Limits.Basic`: the TopCat colimit and final
  topology interface. `Mathlib.CategoryTheory.Yoneda`: `CategoryTheory.coyoneda`.
- `Mathlib.Topology.Defs.Induced` (through TopCat):
  `Topology.IsClosedEmbedding`, `Topology.IsEmbedding`, and `Topology.IsInducing`.
- `Mathlib.Topology.Compactness.Compact`: compactness; and
  `Mathlib.SetTheory.Ordinal.Arithmetic`: ordinals and their limit-order interface.
- The only proof dependency is the same colimit leaf, already publicly imported.

Edge cases checked mathematically against the signature and seven-step proof plan:

- Empty A is allowed: kappa is nonzero, so the zero stage exists and admits the
  empty continuous map. Neither `Nonempty A` nor an unnecessary nonempty-stage
  condition is imposed. Empty stages, and the entirely empty diagram of spaces,
  are allowed (the index interval itself remains nonempty).
- Kappa equals omega: there are no nonzero internal limit stages; continuity is
  then vacuous, as it should be, and the countable closed-discrete-set contradiction
  still gives bounded image. Kappa zero or a successor is excluded exactly as stated.
- Non-T1 and non-Hausdorff A, initial stage, and ambient spaces are allowed.
  A constant chain of a non-T1 space satisfies the relative successor condition
  vacuously outside its image. This does not remove the relative condition for
  general chains: adding points with nonclosed singletons need not satisfy hT1.
- Both countable-supremum possibilities, mu less than kappa and mu equal to kappa,
  are covered by internal continuity and the final colimit respectively. No
  countable-cofinality assumption or regularity assumption is imposed on kappa.
- Bijectivity uses no stagewise nonemptiness: equality is tested at the larger
  of two ordinal indices, strictly below kappa, and the injective stage map
  identifies the representatives. Surjectivity is precisely factorization.
- Universes u and v are explicit and independent. The index interval has universe
  u+1; the theorem assumes the specified TopCat colimit cocone, not a global
  instance of colimits with an artificial universe equality. The source, stages,
  and their given colimit can inhabit any common universe v, with no bound imposed
  by the ordinal universe. The Hom-colimit clause likewise quantifies over supplied
  universal cocones rather than requiring a restrictive colimit-size instance.

Searches for an existing exact statement (all prescribed msearch calls used group
Q81 and this item's id):

- `leanfinder`: “Continuous maps from compact spaces into continuous ordinal
  colimits of closed T1 inclusions factor through a stage”. Eight hits, including
  `CompactT2.Projective`, `CompactT2.ExtremallyDisconnected.projective`, and
  `Profinite.NobelingProof.GoodProducts.smaller_factorization`; these concern
  projectivity or profinite projection factorizations, not this theorem.
- `loogle`: `"CompactSpace", "colimit"`. Successful query, zero hits.
- `leansearch`: “Compact spaces are finite relative to continuous transfinite chains
  of closed T1 inclusions”. Eight hits headed by `CompactSpace` and ordinary
  compactness theorems; no exact statement.
- `grep` via msearch, subdirectory Topology:
  `closed.*T1|compact.*(colimit|transfinite)|IsWellOrderContinuous`. Twenty-five
  reported hits concern T1 closed-set facts and topology of algebraic spaces;
  no compact-source ordinal factorization theorem.
- Direct `rg` in Mathlib Topology found `IsClosedEmbedding` and TopCat's final
  topology API; direct `rg` in Mathlib CategoryTheory found the existing
  `Functor.IsWellOrderContinuous` interface, which I reused.
- Direct `rg` for `compact.*(chain|ordinal|colimit)|closedT1|ClosedT1` in upstream
  WeilConjectures and side-library Sheaf found unrelated cohomology, profinite,
  and compact-object colimit statements. None is the requested topological theorem.
- `grep -rn 'lem-coef-compact-closed-t1-chain'` in upstream WeilConjectures had
  no hits. Direct exact-name search for `compact_closedT1_chain_factorization`
  in Mathlib, upstream WeilConjectures, side-library Sheaf, and
  `dag/lean_names_upstream.json` had no hits before writing the module.

Validation: prescribed `scompile.py Q81 lem-coef-compact-closed-t1-chain <module>`
accepted the statement with no errors or warnings. The first draft used the reserved
lambda character for its binder; it was renamed to kappa and recompiled successfully.
The required deliver2 dry run is run after this report and records its own result.
No proofs were attempted, no live source was edited, no global build was run, and
no delivery is pushed by this worker. The second reader supplies their own reading.

## Second reading by Q81

I independently read the sandbox node and module, the repository node and its sole
dependency, and Hovey's source PDF (extracted in `scratchpad/hovey-all.txt`). I also
read Definitions 2.1.1, 2.1.3 and 2.1.4, Section 2.4's construction of Top colimits,
Lemma 2.4.1, Proposition 2.4.2 and the relative-T1 argument of Lemma 2.4.5. The source
is Hovey, not a Stacks topology lemma; the dependency's categorical universal
property is the one of Stacks 002F. There is no repair note for this item.

The node's objects, hypotheses and conclusions, matched independently:

1. Nonzero limit ordinal lambda: `(κ : Ordinal.{u})` and
   `(hκ : Order.IsSuccLimit κ)`. I read `Order.IsSuccLimit`: it excludes minimal
   elements and elements covering a predecessor. For ordinals this is precisely
   nonzero limit, with neither regularity nor a cofinality bound. Verdict: exact.
2. The ordinal-indexed spaces and continuous transition maps:
   `(F : Set.Iio κ ⥤ TopCat.{v})`. The preorder category has one arrow for each
   comparison of indices. Functoriality supplies the composition laws. Verdict: exact.
3. Continuity at each nonzero internal limit: `[F.IsWellOrderContinuous]`. I read
   its field `nonempty_isColimit (m) (hm : Order.IsSuccLimit m)` and the principal
   initial-segment cocone it uses. It asserts the colimit of all earlier stages,
   with the actual transition arrows into `F.obj m`, not merely a topology on an
   unrelated set. Initial intervals preserve these limit elements. Verdict: exact.
4. Successor maps: `(i j : Set.Iio κ) (hij : i ⋖ j)` ranges over precisely adjacent
   ordinals below κ; `homOfLE hij.le` is their transition arrow. Verdict: exact.
5. Closed inclusion hypothesis: `hclosed` applies `IsClosedEmbedding` to this
   arrow. I read its fields: induced source topology, injectivity, and closed
   image. Its continuity is also part of the TopCat arrow. It is neither just
   closed range nor a stronger separation assumption. Verdict: exact.
6. Relative T1 hypothesis: `hT1` says `y ∉ Set.range (...)` implies
   `IsClosed ({y} : Set (F.obj j))`, only for successor maps. It imposes nothing
   on points already in the image. Hovey's printed extra “not” before the
   complement is the documented typo: Lemma 2.4.5 explicitly treats points outside
   the image, agreeing with this node and Lean. Verdict: exact.
7. Final-topology union and its canonical injections: `(c : Cocone F)` and
   `(hc : IsColimit c)`, with union `c.pt` and maps `c.ι.app i`. The recorded
   dependency explicitly provides `Cocone`, `IsColimit` and their canonical maps.
   I read `IsColimit.desc/fac/uniq`, and TopCat's
   `coinduced_of_isColimit` and `isOpen_iff_of_isColimit`. The forgetful functor
   preserves colimits, so this is the underlying set colimit with final topology.
   For the continuous chain of embeddings its set colimit is the union, up to
   canonical bijection; the proof's first step establishes the stage embeddings.
   An arbitrary colimit cocone represents exactly the same object up to unique
   isomorphism and adds no restriction. Verdict: exact, with no private copy.
8. Compact topological source: `(A : TopCat.{v}) [CompactSpace A]`. I read
   `CompactSpace` and `IsCompact`; the usual finite-open-subcover notion is used,
   without T1, Hausdorff or nonemptiness assumptions. Verdict: exact.
9. Every map factors continuously through some stage: the first conjunct is
   `∀ f : A ⟶ c.pt, ∃ (i : Set.Iio κ) (g : A ⟶ F.obj i),
   g ≫ c.ι.app i = f`. The existential stage follows the map quantifier and
   the lift is a bundled continuous map. Verdict: exact.
10. The set-valued continuous-map diagram is
    `F ⋙ coyoneda.obj (op A)`. I read `coyoneda := yoneda.flip`: its objects
    are Hom sets and its arrows are postcomposition. There is no compact-open
    function-space topology in this expression. Verdict: exact.
11. The equivalent canonical-map bijection is the second conjunct, quantifying
    `(s : Cocone ...) (hs : IsColimit s)` and asserting
    `Function.Bijective (hs.desc ((coyoneda.obj (op A)).mapCocone c))`. The
    codomain is exactly `A ⟶ c.pt`; the cocone consists of postcomposition with
    `c.ι.app i`. It asserts both surjectivity and injectivity, not merely
    existence of lifts. Changing the chosen universal cocone changes this map
    only by the unique comparison isomorphism. The quantification is inside
    the second conjunct, so no existence assumption weakens factorization.
    Moreover factorization and stagewise injectivity make `Hom(A,c.pt)` itself
    a set colimit, so the formulation does not hide an absent colimit. Verdict: exact.

Edge cases checked independently: empty A factors through stage zero, available
because κ is nonzero; individual stages and the union may be empty. The ordinal
index interval itself is correctly nonempty, since an empty chain is not in the
node's hypotheses. For κ = omega there are no nonzero internal limit conditions.
The proof covers both countable suprema μ < κ and μ = κ. A constant chain on a
non-T1 space is allowed: the relative T1 requirement is vacuous on its empty
complement, so no initial-space separation condition slipped in. No zero-object,
scheme, characteristic or natural-number parameter occurs in this topological
statement. Universes `u v` are explicit and independent; there is no smallness
instance forcing equality. The spaces, A, and the supplied colimit have a common
arbitrary universe, and independent-sized spaces can all be lifted to a common
universe. The Hom diagram is in `Type v`, not in TopCat. Its universal cocones
are quantified without assuming a global colimit-size instance.

Independent searches, using different wording from the first reader:

- `msearch.py ... leanfinder "Compact domain continuous map into increasing union
  with weak topology of closed subspaces has bounded image"`: eight hits, headed
  by `IsCompact.bddAbove_image`, `IsCompact.bddBelow_image` and norm bounds. Their
  displayed types are order-topology or normed-space assertions, not this theorem.
- `msearch.py ... loogle '"CompactSpace", "IsClosedEmbedding"'`: seven hits.
  These transfer compactness, local compactness, sigma compactness or
  paracompactness across an embedding, or state Arzela-Ascoli; none has a chain
  or a canonical Hom-colimit map.
- `msearch.py ... leansearch "Compact topological space is finite relative to
  closed T1 inclusions"`: eight hits, ordinary finite-subfamily characterizations
  and compact discrete-space facts; no exact statement.
- Direct `rg -n -i` over Mathlib Topology, upstream WeilConjectures and project
  `lean/Sheaf` for `small.*relative|finite.*relative|compact.*(transfinite|colimit|
  chain|ordinal)|((transfinite|ordinal).*(compact|closed))`: unrelated scheme
  finiteness, sheaf-cohomology colimits, profinite projections and categorical
  compact objects. None is this topological result. An exact-name/source-phrase
  search in all three roots also found no duplicate.

No mismatch was found, and I changed neither the Lean nor the node. There are
no new definition nodes or dependency modules to audit, no statement correction
or citer audit, and no hollow definitions. The module has one named theorem,
whose sole proof is `sorry`; its source/blueprint docstrings and seven numbered
proof steps agree with all seven node steps. All imports serve the statement or
its sole colimit dependency; there is no private notation, local instance,
unbound universe or hidden variable. A textual check confirmed the node's
`lean.statement` is verbatim the module signature and that only `lean` differs
from the repository node. All Lean lines are at most 100 characters.

Validation: I ran the prescribed `scompile.py Q81
lem-coef-compact-closed-t1-chain` on the delivered module. Both sandbox and
library compilation succeeded (1.4 s and 1.5 s), without errors or warnings.
