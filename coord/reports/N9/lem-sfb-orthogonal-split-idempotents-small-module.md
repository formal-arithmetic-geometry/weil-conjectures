## Worker report

The module `Sheaf.LinearAlgebra.OrthogonalSplitIdempotentsSmallModule` states
`Module.orthogonal_split_idempotents_small_module`. Its single proof is `sorry`.
It defines no new notion and changes only the item's `lean` record.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/` followed by
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
That paragraph gives the coefficient stability context, not this auxiliary lemma.
The node expressly identifies its auxiliary and its four-step proof as agent-formulated
extractions from returned reconstruction steps 8–9. The module preserves that attribution;
it does not claim an external reference was found. The recorded reconstruction module
`Sheaf.LinearAlgebra.CountableEndomorphismModuleReconstruction` was also read, especially
steps 6–9 of its proof docstring and its scalar-tower binder.

Hypothesis and conclusion correspondence:

- A field K is `(K : Type u) [Field K]`.
- A unital, potentially noncommutative K-algebra D is `(D : Type v) [Ring D]
  [Algebra K D]`. The algebra map is central by the Mathlib Algebra definition.
- A unital left D-module Q is `(Q : Type w) [AddCommGroup Q] [Module D Q]`.
  Its induced K-vector-space structure is `[Module K Q] [IsScalarTower K D Q]`.
  The tower equation at `1 : D` gives
  `(algebraMap K D a) • x = a • x`, so this is exactly scalar restriction.
  Conversely restriction of a D-module has this tower structure. No independent
  action or compatibility assumption beyond the induced structure is requested.
- An arbitrary index set is `(I : Type t)`, with its own independent universe.
  The two families are `(u r : I → D)`.
- The splitting relation is `_hsplit : ∀ i : I, r i * u i = 1`.
- The notation p_i = u_i r_i is expanded in `_horthogonal`; for all distinct i,j
  and every x, `((u i * r i) * (u j * r j)) • x = 0`.
- The first conjunct quantifies over every `q : Q` with `q ≠ 0` and states
  `LinearIndependent K (fun i : I ↦ u i • q)`. Mathlib's
  `linearIndependent_iff'` (LinearIndependent/Defs.lean:731–733) identifies this
  with the node's finite-relation formulation, including every coefficient in F.
- The second conjunct quantifies over every `W : Set Q`, with exactly the spanning
  condition `Submodule.span K W = ⊤`. Under `Nontrivial Q` it gives
  `∃ f : I → W, Function.Injective f`. Here W as a type is the subtype of elements
  of the spanning set, not an arbitrary indexing family. For an additive group,
  `Nontrivial Q` is equivalent to existence of an element unequal to zero.
- The final conjunct assumes `¬ Countable I` and existence of `W : Set Q` with
  `Countable W ∧ Submodule.span K W = ⊤`; it concludes `Subsingleton Q`, which
  for the additive group Q means that every element is zero, exactly Q = 0.
- There is no topology, faithful action, commutativity of D, or product-zero
  equation inside D in the signature.

Dependency declarations used and read:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, line 180,
  including its docstring and inherited CommRing/DivisionRing signature.
- `def-sfb-countable-set`: Mathlib `Countable`, `Mathlib.Data.Countable.Defs`,
  lines 39–43; its field is an injection into the natural numbers.
  Both dependencies are Mathlib matches and need no project Lean record.
- The proof dependency `lem-sfb-independent-family-spanning-cardinality` is
  `linearIndependent_le_span''` in
  `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`, lines 287–300,
  imported as a proof-only dependency. Its signature and docstring were read.
  Its same-universe cardinal comparison can be used after lifting to a common
  universe; the delivered statement itself allows all four universes independently.
- Mathlib's `Algebra` (Algebra/Defs.lean:91–99), `IsScalarTower`
  (Group/Action/Defs.lean:205–212), `LinearIndependent`, and `Submodule.span`
  supply the existing algebra, action compatibility, independence, and span notions.
  `Mathlib.Algebra.Algebra.Tower` and `Mathlib.LinearAlgebra.LinearIndependent.Defs`
  expose these in the public signature; Field and Countable are public imports too.

Edge cases checked mathematically before writing:

- Empty I: independence of the empty family and the empty injection hold;
  the uncountability antecedent is false. There is no Nonempty I binder.
- Zero Q: the first clause has no nonzero q, the second clause's Nontrivial
  antecedent fails, and the final clause gives the already subsingleton module.
- Empty W can span exactly the zero module, so it causes no impossible injection
  in the second clause. Nonempty finite spanning sets and finite I remain included.
- Singleton I: the orthogonality hypothesis is vacuous, and applying r to u • q
  still gives q, so independence of that one nonzero vector holds.
- A zero algebra D is permitted and its unital modules are zero; no Nontrivial D
  assumption was added. A nonfaithful module action remains permitted.
- Arbitrary characteristic and unrelated sizes for K, D, Q, I cause no exclusions.

Actual searches (logged by msearch.py in this sandbox, 2026-10-24):

- LeanFinder: `Split idempotents orthogonal on a module give linearly independent
  translates of a nonzero vector and bound the index set by any spanning set`.
  Eight hits: seven Profinite.Nobeling results and `exists_linearIndependent'`;
  none states this split-action criterion and its conclusions.
- Loogle: `LinearIndependent, IsIdempotentElem`; zero hits.
- Mathlib grep: `(orthogonal|idempoten).*(LinearIndependent|linearIndependent)|
  (LinearIndependent|linearIndependent).*(orthogonal|idempoten)` (one regex
  without the displayed line break); zero hits.
- LeanSearch: `A family of split injections with pairwise orthogonal image
  projections on a module yields a linearly independent family of translates
  of any nonzero vector`. Eight hits, including `Module.Basis.ofSplitExact`,
  `OrthogonalFamily.independent`, `LinearIndependent`, and span/image lemmas.
  The split-exact basis theorem already assumes independence of a family;
  the orthogonal-family theorem requires an inner product. Neither is this item.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `orthogonalSplit|orthogonal_split|split_idempotent|splitIdempotent`, then for
  independence paired with orthogonal/idempotent, found no exact declaration.
  Matrix `splitIdempotent` is a different finite-matrix construction; the
  `CountableUltrametricBasis` hit concerns normed-space orthogonality.
- The prescribed `grep -rn` of the item id in `lean/WeilConjectures` and `rg` of
  the id in `dag/lean_names_upstream.json` had no hits.

No statement dispute or correction, new node, or dependency repair is required.

Validation: scompile.py compiled the file as both sandbox and library module,
without errors or warnings (4.1 s and 2.7 s). All variables and universes are
explicit, and autoImplicit is disabled. deliver2.py --no-push passed the preflight
and per-file compilation, producing dry-run commit 9a9be581607 without a push.

## Second reading by N9

The dispatcher forbids starting other agents; this is a separate rereading by the
same worker, with the node and the final Lean file open, not a claimed second agent.
The maintainer's independent delivery review remains separate.

I rechecked the field, unital algebra, both module instances and scalar tower,
then the unrestricted index type, the order r_i u_i of the splitting equation,
and the order (u_i r_i)(u_j r_j) of the product acting on every x. These match.
The first conjunct uses all nonzero q; its finite-sum meaning was compared with
Mathlib's linearIndependent_iff'. The second uses every actual subset W with
span top and asks for an actual injective function into its subtype, with
nonzeroness conditional rather than a global exclusion of the zero module.
The third uses precisely injection-to-naturals countability and concludes
Subsingleton, so it also covers the zero module. I rechecked that the four
universes are independent and that no faithfulness, topology, product-zero
identity in D, or additional commutativity condition appears. No mismatch was
found and no mathematical signature change was needed on this reading.
The module docstring accurately labels the source's auxiliary as agent-formulated,
and the declaration docstring includes all four DAG proof steps. The only sorry
is the named theorem corresponding to the delivered node.
