## Worker report

The module `Sheaf.AlgebraicTopology.OrderedJoinPartialContraction` gives the actual
ordered-join groups, specified basis, and every displayed operator in the node,
then states `AlgebraicTopology.OrderedJoin.partialContraction` with proof `sorry`.
All definitions contain real data. The only postponed theorem is this one, and
its docstring gives all eight steps of the node's proof, including deletion signs,
the prescribed composition order, naturality, and the unreduced subset expansion.
No statement correction, new DAG node, or dependency repair is needed. Only the
item's `lean` field changes.

Hypotheses and constructions, clause by clause (names below are in
`AlgebraicTopology.OrderedJoin`):

- `r : ℕ` and `hr : 1 ≤ r` are exactly the positive number of colors.
- `X : Fin r → Type u` is the arbitrary family of sets, with no finiteness,
  topology, ordering, or decidable-equality assumption on any `X i`.
  `v : ∀ i : Fin r, X i` is exactly the specified element of each set.
- `Face X` consists of `colors : Finset (Fin r)` and
  `vertex : ∀ i, i ∈ colors → X i`. The increasing order of the finite color
  set uniquely recovers the ordered list in the node. There is exactly one
  vertex for every present color, and repeated colors are impossible.
- `Symbol X q` imposes `(σ.colors.card : ℤ) = q + 1`.
  `Chain X q` is `Symbol X q →₀ ℤ`, the group of finite formal integer sums.
  Its specified basis is the existing `Finsupp.basisSingleOne`, whose vectors
  are `Finsupp.single σ 1`. This implements precisely the basis notion in
  `def-weil-pbc-free-module`; no substitute notion of freeness is defined.
  The empty face is the sole symbol for q=-1, giving the integer group;
  q<-1 and q>=r have no symbols and give zero groups.
- `erase` deletes a color and its vertex. `positionSign C i` is
  `(-1 : ℤ) ^ (C.filter (fun j ↦ j < i)).card`, hence precisely the sign of
  its zero-based position in increasing order.
  `boundary X q (q-1)` extends the signed sum of deleted faces by
  `Finsupp.linearCombination ℤ`. A singleton has sign +1 and maps to the
  empty-face basis vector; the empty sum makes d of the empty face zero.
- `insert v i` inserts the chosen vertex at its color position.
  `insertion v i q (q+1)` is zero if i is present and otherwise the
  position sign times that inserted basis vector. In particular it sends
  the empty face to the singleton with vertex `v i`.
- `replaceColors v {i}` replaces the color-i vertex by `v i`.
  `remainder v i q` is zero when i is absent and otherwise the original
  basis vector minus its chosen replacement, exactly R_i.
- `remainderPrefix v n q` is a right fold of increasing `List.range n`:
  the fold step is `(remainder v j q).comp P`. Thus for n=i it is
  R_0 composed with ... composed with R_{i-1}, with the rightmost factor
  applied first, and n=0 is `LinearMap.id`.
- `contraction v q (q+1)` is the finite sum over `i : Fin r` of
  `(remainderPrefix v i.val (q+1)).comp (insertion v i q (q+1))`.
  This is exactly the displayed S, rather than an unspecified filling map.
- `mapFace f` preserves colors and applies `f i` to each vertex.
  `chainMap f q` extends that formula by integer linear combination,
  hence is precisely J_q(u), without an injectivity assumption.

Conclusions, in the order of the conjunction in `partialContraction`:

1. For every integer q,
   `(boundary X (q-1) (q-2)).comp (boundary X q (q-1)) = 0`
   states d squared zero in every degree.
2. For every q with `-1 ≤ q` and `q ≤ (r : ℤ)-2`, the sum of
   `(boundary X (q+1) q).comp (contraction v q (q+1))` and
   `(contraction v (q-1) q).comp (boundary X q (q-1))`
   equals `LinearMap.id`. This is dS_q+S_{q-1}d=id on the exact requested
   range. The next conjunct is `contraction v (-2) (-1) = 0`, the stipulated
   S_{-2}=0. No identity is asserted on the potentially nonzero top homology.
3. For arbitrary `Y : Fin r → Type v`, arbitrary `f : ∀ i, X i → Y i`,
   and every integer q, `chainMap f (q+1)` composed with S for v equals
   S for `(fun i ↦ f i (v i))` composed with `chainMap f q`.
   The chosen target vertices are exactly w_i=u_i(v_i); their own universe
   is independent of that of X. All maps, including constant maps, are included.
4. For every basis symbol σ, S applied to `Finsupp.single σ 1` equals the
   `List.sum` of the terms prescribed by `expansionRecipe r σ.val.colors`.
   Each entry is an integer coefficient together with an insertion color i
   and a subset A of earlier colors to replace. The recipe lists the i-th
   block only when i is absent and every earlier color is present; it lists
   all subsets A with coefficient `positionSign C i * (-1)^A.card`.
   Its type and arguments contain no X, v, or vertex values. Evaluation only
   inserts a chosen vertex and replaces vertices by chosen vertices.
   Repeated output faces remain repeated list entries, so even coincident
   input/chosen vertices never require an equality test. This is the final
   clause of the node, including its uniform coefficient-list requirement.

The maps with two integer arguments give their source and target degree
components. The theorem uses only the indicated adjacent components. This avoids
casts between arithmetically equal degrees, without adding hypotheses or
changing any chain group or operator. `symbolTerm` checks the color cardinality
before making its basis vector; for each prescribed component every summand has
the correct degree. It never inspects vertex values.

Dependencies used:

- `def-weil-pbc-free-module` records `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic`, with the underlying basis notion
  `Module.Basis`. I read that class signature and its docstring. This module
  is imported explicitly. The actual specified basis and basis extension
  use `Finsupp.basisSingleOne` in
  `Mathlib.LinearAlgebra.Finsupp.VectorSpace` and `Finsupp.linearCombination`
  in `Mathlib.LinearAlgebra.Finsupp.LinearCombination`; I read their full
  definitions and docstrings as well.

Edge cases checked before delivery:

- r=1: only the augmentation degree -1 is contracted; q=0 is correctly excluded.
- q=-1: the empty symbol is present, d=0 and S gives the color-0 chosen vertex;
  all higher i terms are killed by R_0.
- q=-2 and q<-1: the symbol type is empty, so the chain group and S_{-2} are zero.
- q=r-1: the top symbols contain every color; the theorem does not contract
  this degree. q>=r gives an empty symbol type.
- Empty individual X_i cannot supply v_i, just as in the node; infinite X_i
  are fully allowed, since each chain has finite support and only colors
  are finitely indexed. Independent source/target universes are retained.
- Singleton X_i, vertices already equal to v_i, and constant/non-injective
  maps: differences can cancel, but all unreduced recipe terms still exist.
- An independent finite arithmetic sanity check enumerated 120 symbols for
  two-point X_i and r=1,...,4, checking d squared zero, the contraction in
  the prescribed degrees, and equality with the subset expansion. It also
  checked naturality for every map of two-point sets for r<=3. All passed.
  This is only a check of the statement's signs and edge cases; the Lean
  theorem intentionally remains unproved in this stage.

Searches for an existing declaration:

- `msearch.py leanfinder`: "The augmented integral chains of an ordered join
  of pointed sets admit a natural partial contracting homotopy below the top
  degree" returned eight hits, including augmented extra-degeneracy homotopy
  equivalences and Dold-Kan homotopies. None defines the distinct-color ordered
  join complex or this partial contraction. Extra degeneracies contract an
  entire augmented complex, unlike the possible nonzero top degree here.
- `msearch.py leansearch`: "The reduced integral chain complex of an ordered
  join of nonempty sets is contractible below its top dimension" returned
  singular chains, abstract chain-complex augmentation/truncation, and
  simplicial dimension lemmas; none is this statement.
- `msearch.py loogle`: `Finsupp.linearCombination, Finsupp.lmapDomain,
  Finset.powerset, Module.Basis` returned zero combined hits. The existing
  basis and extension APIs were then found and read directly in Mathlib.
- `msearch.py grep` with
  `(join|colored|coloured).*(chain|contract)|(chain|contract).*(join|colored|coloured)`
  in Mathlib's AlgebraicTopology directory returned zero hits.
- `rg` for `OrderedJoin`, `orderedJoin`, `ordered.join`, and the item id in
  project and upstream sources found the downstream homogeneous-cocycle
  proof's citation, plus simplicial ordinal doubling and an etale hypercover
  reference. These do not give this chain complex or formula. The expected
  declarations `partialContraction` and `expansionRecipe` are also absent
  from Mathlib and both project roots.

I read the specified blueprint source in full: paragraph (3) is the
compactification argument, not this combinatorial calculation. The node already
accurately identifies its ordered-join proof as an agent expansion below that
paragraph, and this attribution is preserved. There is no repair note on the
item. NN's reviewed delivery is the stage-1 split, not a Lean statement; the
live node has no `lean` record, so this stage-2 delivery does not split it again.
No STATEMENT-DISPUTED issue was found.

Validation: the prescribed `scompile.py` compiled this module both as a sandbox
module and at its library module path, cleanly with no warnings or errors.
The dry run and delivery are performed through `deliver2.py` only.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
