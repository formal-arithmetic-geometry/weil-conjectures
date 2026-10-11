## Worker report

The module `Sheaf.CategoryTheory.CoskeletonMatchingTuples` states
`CategoryTheory.SimplicialObject.exists_coskeleton_matching_tuples`, with one `sorry` and no
new definitions. The node is unchanged except for `lean`.

Clause-by-clause correspondence:

- The arbitrary category with finite limits is `{C : Type u} [Category.{v} C]
  [HasFiniteLimits C]`. Object and morphism universes are explicitly independent.
- The simplicial object is `(K : SimplicialObject C)`; `(n : ℕ) (_hn : 1 ≤ n)` is precisely
  the degree condition. The local abbreviations `m := n - 1`, `i :=
  SimplexCategory.Truncated.inclusion m`, and `V := (truncation m).obj K` implement the
  stipulated truncation, not Mathlib's left-Kan-extension endofunctor `sk`.
- `∃ (L : SimplicialObject C) (ε : (truncation m).obj L ⟶ V),
  L.IsRightKanExtension ε` says that the pair is an `(n-1)`-coskeleton, using the exact
  universal-property declaration recorded in def-weil-pbc-simplicial-coskeleton. It adds
  no chosen global coskeleton functor and assumes no right Kan extensions exist in advance.
- A family is written inline as the subtype `F W`. Its data are `x k α : W ⟶
  K.obj (op (i.obj k))` for every `k : SimplexCategory.Truncated m` and every
  `α : i.obj k ⟶ SimplexCategory.mk n`. These are exactly all order-preserving maps in
  the stated range, including noninjective maps. No separate new notion is needed to
  express a dependent function satisfying the displayed equation.
- The subtype condition is `x k α ≫ K.map (i.map ψ).op = x k' (i.map ψ ≫ α)` for
  all `k', k` in the truncation and all `ψ : k' ⟶ k`. Mathlib composition runs from left
  to right, so this is precisely the node's `K(ψ) ∘ x_α = x_{α ∘ ψ}`.
  As the node's reviewed proof and Stacks source specify, both degrees are truncated:
  otherwise the right-hand side would not be a component of the indexed family.
- `∃ (e : ∀ W : C, (W ⟶ L _⦋n⦌) ≃ F W)` is the bijection for every object `W`.
  The first conjunct specifies its forward map component by component as
  `h ≫ L.map α.op ≫ ε.app (op k)`, precisely the map the node requires.
- The second conjunct, for every `g : W' ⟶ W`, states that the forward map of `g ≫ h`
  has components `g ≫ (e W h).val k α`. This is naturality in the variable `W`.
  Componentwise equality is equality of families, since their remaining fields are proofs.
- The morphism `c : K ⟶ L` is characterized by `(truncation m).map c ≫ ε = 𝟙 V`.
  The preceding right-Kan-extension property makes this the unique canonical morphism
  corresponding to the identity, rather than an arbitrary comparison map. The last
  conjunct says its degree-`n` image has each component `K.map α.op`, exactly the final
  clause of the node.

Dependency declarations read and used:

- def-galois-finite-limits-colimits (status mathlib):
  `CategoryTheory.Limits.HasFiniteLimits` in
  `Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits`. Only the finite-limit clause is
  required here, so finite colimits are not assumed.
- def-weil-pbc-simplicial-object (status mathlib): `CategoryTheory.SimplicialObject` in
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`; its functor maps and natural
  transformations give all operators and the comparison morphism. Its `δ` and `σ`
  definitions were read; the theorem concerns all operators, so does not restrict to those.
- def-weil-pbc-simplicial-coskeleton (status mathlib):
  `CategoryTheory.SimplicialObject.Truncated`, `CategoryTheory.SimplicialObject.truncation`
  in the same Basic module; `CategoryTheory.Functor.IsRightKanExtension` in
  `Mathlib.CategoryTheory.Functor.KanExtension.Basic` (imported transitively by Basic).
  The docstrings/signatures of `Truncated.cosk`, `coskAdj`, and
  `homEquivOfIsRightKanExtension` were also checked. The latter sends a transformation
  to its whiskering followed by the counit; its inverse is the canonical lift.

Source check: the literature checkout is absent on this machine. Opened Stacks
[Tag 0183](https://stacks.math.columbia.edu/tag/0183), Lemma 14.19.2, including its proof;
this is the source formula and mapping property that the node expands. No source correction
is needed. The proof docstring follows the node's three steps, including the counit/projection
comparison automorphism rather than assuming these two maps are equal.

Edge cases checked:

- `n = 1`: the truncation has only `[0]`, and the two vertex maps to `[1]` give two
  arbitrary components with only identity compatibility. This describes `K₀ × K₀`.
- `n = 2`: all maps from `[0]` and `[1]`, including constant maps, occur; compatibility
  includes degeneracies and does not accidentally restrict to proper faces.
- `n = 0` is explicitly excluded by the node and by `1 ≤ n`; natural-number subtraction
  therefore implements the intended predecessor.
- No nonemptiness assumption is placed on `C` or on Hom sets. For an empty category there
  is no `K`; for a terminal category the family spaces and Hom spaces are singletons.
- Zero objects and empty-valued simplicial objects are allowed whenever the ambient category
  has them. There is no assumption about rings, fields, characteristic, or inhabited terms.

Searches performed before drafting (actual msearch records are in `searches.jsonl`):

- `msearch.py leanfinder`: "coskeleton degree n represents compatible families of simplices
  indexed by maps from truncated simplex category". Eight hits, including
  `SimplicialObject.Truncated.cosk`, `cosk`, and `isCoskeletal_iff`; none states the tuple formula.
- `msearch.py leansearch`: "coskeleton simplicial object compatible truncated families".
  Service unavailable (Internal Server Error), recorded as unavailable.
- `msearch.py loogle`: `CategoryTheory.Functor.IsRightKanExtension`. Twelve hits give the
  universal property, its lift, and induced equivalence of natural transformations; they do
  not give the degreewise truncated-family bijection under finite limits.
- `msearch.py grep`: `cosk|compatible.*famil|matching.*tuple`, in Mathlib/AlgebraicTopology.
  Twenty-five hits give coskeleton constructions and coskeletal objects, no matching theorem.
- `rg` in WeilConjectures for `coskeleton|matching` and the exact node id: no relevant
  declaration (the id has no hits; "matching" hits are unrelated descriptive comments).
- `rg` in `lean/Sheaf` for `coskeleton|matching`, then `matching|Compatible|coskeleton`:
  no coskeleton-family theorem; compatible-module gluing and derived-limit tuples are unrelated.
- Exact proposed-name collision search for `exists_coskeleton_matching_tuples` and
  `CoskeletonMatchingTuples` in Mathlib, WeilConjectures, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no hits.

Validation: `scompile.py K1 lem-weil-pbc-coskeleton-matching-tuples` compiled the module on
its first run in 1.2 seconds, exit code 0, without errors or warnings. All variables and
universes are explicitly bound. No statement dispute, correction, or dependency fault.

## Second reading by K1

I read the node statement, its Stacks source (Simplicial Methods, Lemma 0183), the three
dependency records, and the module independently. The correspondence is as follows.

- The category is rendered by `{C : Type u} [Category.{v} C] [HasFiniteLimits C]`; this
  supplies exactly finite limits and introduces no finite-colimit, ring, field, or
  finiteness hypothesis.
- `K : SimplicialObject C` is the contravariant functor on the simplex category, and
  `n` with `_hn : 1 ≤ n` is the node's degree restriction. `m := n - 1`, `i :=
  SimplexCategory.Truncated.inclusion m`, and `V := (truncation m).obj K` render
  `sk_(n-1) K` using the recorded coskeleton declaration.
- The existential pair `(L, ε)` has `ε : (truncation m).obj L ⟶ V` and
  `L.IsRightKanExtension ε`, exactly the stated `(n-1)`-coskeleton universal property;
  the additional canonical `c` is supplied with its defining equation.
- `F W` is the subtype of all maps `x k α : W ⟶ K.obj (op (i.obj k))`, with `k` in
  degrees at most `m` and every order-preserving `α : i.obj k ⟶ [n]`. Its equation
  `x k α ≫ K.map (i.map ψ).op = x k' (i.map ψ ≫ α)` is precisely the compatibility
  condition for every order-preserving `ψ : k' ⟶ k`, including degeneracies and
  noninjective maps.
- `e : ∀ W, (W ⟶ L_[n]) ≃ F W` is the required bijection. The first quantified
  conjunct identifies its forward map with
  `h ≫ L.map α.op ≫ ε.app (op k)`, component by component. The second conjunct gives
  naturality under every `g : W' ⟶ W`, with the same quantifier order as the node.
- The final conjunct evaluates the family of the canonical `c` at degree `n` and gives
  `K.map α.op` for every indexed `α`, exactly the node's last clause.

No mismatch was found and no source or node correction was needed. The Lean statement
contains no unbound variables and introduces no stronger assumptions. Edge cases checked
again were `n = 1` (two degree-zero vertex components), exclusion of `n = 0`, constant
and identity maps in the indexing family, empty or terminal categories, zero objects,
and absence of any characteristic or ring assumptions. The subtraction `n - 1` is safe
because of the explicit hypothesis `1 ≤ n`.

For the one-definition-per-notion check I repeated searches with `msearch.py` LeanFinder,
LeanSearch, and Loogle queries for compatible coskeleton families, and `rg` searches in
Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`. They found
only Mathlib's `Truncated.cosk`, `truncation`, and right-Kan-extension API; no theorem
states this degreewise tuple bijection and no project declaration collides with the name.
Thus the module is required and correctly uses the recorded dependency declarations.

The module compiled cleanly with `scompile.py`; its sole proof is the permitted named
`sorry`, and all declaration docstrings carry the source and blueprint id. No changes
were necessary in this second reading.
