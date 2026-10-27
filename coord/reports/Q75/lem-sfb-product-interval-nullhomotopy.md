## Worker report

States `lem-sfb-product-interval-nullhomotopy` in
`Sheaf.AlgebraicTopology.ProductIntervalNullhomotopy`, namespace
`AlgebraicTopology.AugmentedPosetChains.ProductInterval`. No statement correction,
new DAG nodes, or dependency repairs. The only changed node field is `lean`.

Clause-by-clause correspondence:

- A commutative ring is `(R : Type u) [CommRing R]`, with explicit universe `u`.
- The dimension and its lower bound are `{r : ℕ} (hr : 1 ≤ r)`.
- The tuple and selected coordinate are `(m : Fin r → ℕ) (j : Fin r)`, with
  `(hj : 2 ≤ m j)`.
- The coordinatewise proper product interval T is the existing Mathlib subtype
  `Set.Ioo (0 : Fin r → ℕ) m`. In the partial order on functions, strict comparison
  means coordinatewise weak comparison and strictness in at least one coordinate
  (`Pi.lt_def`, Mathlib/Order/Basic.lean:550). Consequently `0 < x < m` says
  exactly `x ≤ m`, `x ≠ 0`, and `x ≠ m`, since all coordinates are natural numbers.
  This includes zero coordinates of m; it does not require every coordinate to
  be strictly positive or strictly below its bound. The subtype inherits precisely
  the coordinatewise order.
- `coordinate_laws` states membership of `Function.update 0 j 1`, membership of
  every raised vector, coordinatewise monotonicity, and both comparisons. Its
  proof is postponed as a named theorem belonging to this same DAG statement.
- `vertex hr m j hj` is the actual vector e, `Function.update 0 j 1`, bundled
  with its interval-membership proof. No arbitrary choice is made.
- `raise hr m j hj` is the actual order homomorphism sending x to
  `Function.update x.val j (max (x.val j) 1)`. Its data are explicit; only its
  membership and monotonicity proofs use `coordinate_laws`.
- The complex is always dependency `AugmentedPosetChains.complex R T`.
  No chain module, differential, or prism is copied.
- `contractionComponent R hr m j hj n k` gives the linear maps as morphisms in
  `ModuleCat R`. At `k = n + 1` and `n ≥ 0` it is exactly dependency
  `prismComponent R (OrderHom.const T e) u n k -
  prismComponent R OrderHom.id u n k`.
- At `n = -1`, `k = n + 1`, it is `Finsupp.linearCombination` assigning
  `bracket R k [vertex hr m j hj]` to each basis element. There is exactly one
  basis element in degree -1, the empty list, so this is precisely the required
  empty-generator assignment. At `n < -1` it is zero. The extra target index
  avoids transports for `(n - 1) + 1 = n` in the identity; it introduces no
  mathematical assumption and is used only in the indicated adjacent degrees.
- `nullhomotopy` records `OrderHom.id ≤ raise` and `OrderHom.const T vertex ≤ raise`.
  Existence of the vertex and monotonicity are already encoded by the definitions'
  types. Its last clause quantifies over `∀ n : ℤ` and states
  `t n (n+1) ≫ d (n+1) n + d n (n-1) ≫ t (n-1) n = 𝟙 _`.
  Categorical composition reads left to right, hence these are exactly the node's
  `d_{n+1} t_n + t_{n-1} d_n`.

Dependency declarations read in full and used:

- `Sheaf.AlgebraicTopology.AugmentedPosetChains`:
  `AlgebraicTopology.AugmentedPosetChains.Simplex`, `chains`, `bracket`,
  `boundary`, `boundary_laws`, `complex`. This is the recorded declaration of
  `def-sfb-augmented-poset-chains`; its list-length convention supplies degree -1
  and the vanishing lower modules.
- `Sheaf.AlgebraicTopology.AugmentedPosetChainPrism`:
  `mapComponent`, `map_comm`, `map`, `map_id`, `map_comp`, `prismComponent`,
  `prism_identity` in the same namespace. These are the recorded declarations of
  `lem-sfb-poset-augmented-chain-prism`. The explicit signed formula and the
  orientation `g_* - f_*` determine the subtraction order in this module.
- `Mathlib.Order.Interval.Set.Basic` supplies `Set.Ioo`; `OrderHom.id` and
  `OrderHom.const` are the existing Mathlib monotone maps.
  Statement dependencies are publicly imported; both proof dependencies are
  already among those imports.

Proof obligations left: `coordinate_laws` (the node's step 1), and `nullhomotopy`
(the full identity, steps 1–4). Their docstrings carry complete natural-language
proofs with the source and blueprint id. All definitions have explicit data,
with no sorry inside a definition. Every variable is explicitly bound and both
forms of automatic implicit insertion are disabled.

Edge cases checked mathematically before writing: with r=1 and m=(2), T has
one point, all nonnegative prism terms vanish, and the augmentation inverse is
exactly t_{-1}. For m=(3), u is the identity on the two-point proper interval,
so the sign `h(c_e,u)-h(id,u)` gives the usual positive contraction. For m=(0,2)
with j the second coordinate, e=(0,1) is allowed; this checks that `Ioo` uses
partial-order strictness rather than pointwise strictness. Coordinates equal to
zero and one outside j are unrestricted. The hypothesis on j excludes r=0 and
an empty T. Zero rings and arbitrary positive characteristic are included.
Degree zero requires the augmentation correction; degree -1 has d[e]=[empty];
lower degrees have no basis. No finiteness or decidable-equality hypothesis is
added to the theorem. The finite interval needed for the prism proof follows
from its coordinate bounds; the explicit prism data itself needs no such instance.

Searches actually run through msearch.py:

- LeanFinder: `Explicit contracting homotopy of augmented strict chains of the
  proper part of a product of finite chains via coordinatewise maximum`.
  Eight hits, including DoldKan.homotopyPInftyToId, homotopyPToId,
  ExtraDegeneracy.homotopyEquiv, and generic inductive homotopy constructors.
  Read the corresponding DoldKan/HomotopyEquivalence and ExtraDegeneracy signatures:
  they require a simplicial object or extra-degeneracy data, and neither defines
  this interval, coordinate map, or the stated augmented contraction.
- Loogle: `"Homotopy", "OrderHom"`. Successful search, zero hits.
- Mathlib grep, AlgebraicTopology: `properInterval|proper.interval|poset.*contract|orderComplex`.
  Successful search, zero hits.
- LeanSearch: `The proper part of a finite product of chains with a coordinate
  at least two has an explicit contracting homotopy on augmented strict chains`.
  Eight hits on generic homotopy constructors, OmegaCompletePartialOrder.Chain.zip,
  and ExtraDegeneracy.homotopyEquiv; no exact statement.
- Direct rg of the same interval/contraction patterns plus `productInterval` in
  lean/WeilConjectures and lean/Sheaf: found the specialized rational
  ProductChainProperIntervalHomology module and consumers, not this explicit
  general-coefficient contraction. Read that module: its ProperInterval is the
  same subtype described differently, but its chain construction is specialized
  to rational coefficients and its theorem gives homology, not the explicit maps.
  The present module uses Mathlib's interval directly instead of copying that
  abbreviation or importing the downstream homology theorem. The general poset
  chains and prism modules were found and reused.
- `grep -rn` of the item id in lean/WeilConjectures: no match.

Sources read: latest blueprint direct-images.proof.md, especially paragraph (3),
and Stacks simplicial.tex equation-homotopy-to-homotopy and lemma-homotopy-s-N
(Tag 019S). The former gives context only, as the node explicitly records;
this contraction is the agent-written extraction in the node, not a purported
verbatim blueprint assertion. The source's general prism assertion is used
through the dependency's augmented strict-chain specialization.

Validation: scompile.py compiled the sandbox and final module cleanly. The first
attempt used a nonexistent extra Mathlib module path; that redundant import was
removed and the required wrapper compile then passed. No disputed statement or
other node fault was found.

## Second reading by Q75

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
