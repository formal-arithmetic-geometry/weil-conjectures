## Worker report

The module `Sheaf.AlgebraicTopology.InnerHornCollapseFiltration` states
`SSet.exists_inner_horn_collapse_filtration`, with its entire proof `sorry`.
It defines no new notion. The node is unchanged except for `lean`.

The previous worker confused Q132's reviewed stage-1 split with a stage-2 statement.
The Q132 report and ledger record the finite combinatorial proof split, with no Lean
module or binding. This delivery supplies its previously absent Lean statement.
There is no repair note for this item.

### Hypotheses and objects

- `N : ℕ`, `hN : 3 ≤ N` render the integer dimension at least three. Negative
  integers cannot satisfy this bound, so natural dimensions cover precisely the
  intended cases.
- `i : Fin (N + 1)`, `hi : 1 < i.val`, `hiN : i.val < N` render `1 < i < N`.
- `c : SimplexCategory.mk N ⟶ SimplexCategory.mk 3` is the monotone vertex map.
  Its induced simplicial map is `SSet.stdSimplex.{u}.map c`.
  `hc` specifies its value at every vertex as precisely the node's four cases.
  The last branch is `k > i`, since the preceding branches exhaust `k < i - 1`,
  `k = i - 1`, and `k = i`. The constrained `c` is exactly the stated collapse,
  not a hypothesis about an unspecified extra map. No existence or choice is
  used to define it, and the formula uniquely determines it.
- Universe `u` is explicit and arbitrary; all subcomplexes are of `SSet.{u}`.
  `set_option autoImplicit false` prevents any automatically bound variable.

### Every clause of the conclusion

- Existential `t : ℕ` encodes the positive number of attachments `m = t + 1`.
  `K : Fin (t + 2) → (Δ[N] : SSet.{u}).Subcomplex` provides exactly stages
  `0, ..., m`. `Antitone K` and `K 0 = ⊤` give the descending filtration and
  its initial simplex. Subcomplexes are the dependency's degreewise subsets
  closed under simplicial operators; their lattice union is degreewise union.
- `S : Fin (t + 1) → Finset (Fin (N + 1))` enumerates the attaching vertex sets.
  `Function.Injective S` supplies the exactly-once clause. For every finite
  vertex set `T`, the biconditional between `∀ b : Fin 4, ∃ k ∈ T,
  c.toOrderHom k = b` and `∃ j, S j = T` says the image of this enumeration is
  exactly the faces mapping surjectively onto the four target vertices. Thus
  it includes no extraneous faces and omits none.
- `n : Fin (t + 1) → ℕ` gives the dimensions. The order isomorphism
  `e j : Fin (n j + 1) ≃o ↥(S j)` says that each face is identified with its
  standard simplex by the increasing enumeration. In particular it implies
  `n j + 1 = (S j).card`, hence precisely `n_j = |S_j| - 1`. It also ensures
  the face is nonempty and its parametrizing simplex is nondegenerate.
- `Antitone n` means nonincreasing dimension, and `S 0 = Finset.univ` gives
  the first face equal to the full simplex.
- `p j : Fin (n j + 1)` and `((e j) (p j)).val = i` identify exactly the
  zero-based increasing-order position of vertex `i`.
- The per-face conjunction `3 ≤ n j ∧ n j ≤ N ∧ 1 < (p j).val ∧
  (p j).val < n j` is exactly the four dimension and position inequalities.
- For every position `q` with `q.val + 1 = (p j).val`, the vertex at `q`
  has value `i.val - 1`. Because `1 < (p j).val`, this predecessor position
  exists and is unique, so this is exactly the immediate-predecessor clause.
- `0 < j.val → n j < N` says that every attachment after the first has
  smaller dimension. Attachment `j : Fin (t + 1)` corresponds to the node's
  one-based attachment `j.val + 1`.
- The map inside `(K j.succ).preimage (...)` is the actual increasing face
  inclusion: the order isomorphism `e j` followed by the order-preserving
  subtype inclusion, turned into an ordinal map with `SimplexCategory.Hom.mk`
  and then into a simplicial map. Its inverse image of the next stage is
  `horn (n j) (p j)`. This is precisely the node's intersection equality
  under its specified increasing-order identification, in every degree.
- `K j.castSucc = K j.succ ⊔ stdSimplex.face (S j)` is the other equality,
  `K_(j-1) = K_j ∪ sigma_j`, with the index shifted as above.
- `K 1 = horn N i` is the first endpoint. Since `t + 2 ≥ 2`, this literal
  finite index is the actual stage one, including the one-attachment case.
- `K (Fin.last (t + 1)) = (horn 3 2).preimage (SSet.stdSimplex.{u}.map c)`
  is the terminal endpoint as an equality of subcomplexes of the original
  simplex. `Subcomplex.preimage` is degreewise set inverse image, exactly
  the degreewise pullback along the horn inclusion viewed as a subset.

### Dependency declarations and source

The sole statement dependency, also the sole proof dependency, is
`def-cbc-enhanced-diagrams-cones`. Its recorded module
`Sheaf.CategoryTheory.EnhancedDiagramsCones` is publicly imported. I read its
module documentation and the signature, docstring and body of its principal
recorded declaration `SSet.Enhanced.coneCategory`; that construction itself is
not used by this combinatorial statement. The module explicitly adopts the
Mathlib primitives `SSet`, `SSet.stdSimplex`, `SSet.horn`, and simplicial
subcomplexes rather than duplicating these notions. Those are the exact
simplicial primitives used here, with `SSet.stdSimplex.face` and
`SSet.Subcomplex.preimage`. I read their definitions in Mathlib's
`AlgebraicTopology/SimplicialSet/{StdSimplex,Horn,Subcomplex}.lean`, as well as
`SimplexCategory.Hom.mk` and `Hom.toOrderHom` in `SimplexCategory/Defs.lean`.
No dependency interface needs repair and no additional node is required.

I opened the official Higher Algebra PDF at
https://people.math.harvard.edu/~lurie/papers/HA.pdf and read Lemma the project server,
printed pp. 308–309, especially the `i > 1` paragraph. It supplies exactly
this collapse, surjective-face family, face deletion, inner-horn attachments,
and terminal inverse horn. Its ordering typo is already corrected in the
node: nonincreasing dimension is forced by putting the full simplex first.
No statement correction is made in this delivery. The theorem docstring
carries all four existing proof steps, including upward closure and the
precise final forbidden blocks 0, 1, 3. There is no statement dispute.

### Edge cases

For `N = 3, i = 2`, the collapse is the identity, there is exactly one
surjective face, and `t = 0` gives two stages, a single 3-dimensional
attachment with position 2, and both endpoints equal to `horn 3 2`.
For `N = 4, i = 2`, the dimensions are 4, 3, 3, with arbitrary ordering
of the last two faces. The symmetric extreme `i = N - 1` also keeps the
last block nonempty. The hypotheses exclude `i = 1` and `i = N`, as the
node does. An empty face cannot be surjective onto the four vertices.

An independent finite-set calculation enumerated every nonempty subset for
all `3 ≤ N ≤ 8`, `1 < i < N`, with two tie-breaking orders: 42 filtrations
across 21 parameter pairs. It checked upward deletion/closure under subsets,
exact enumeration, first full face, every horn intersection and union,
all position/dimension bounds, the immediate predecessor, both endpoints,
and strict dimension decrease after the first face. Every check passed.
Since a simplex factors through its image vertex set and precomposition
shrinks that image, the node's proof explains why these checks model every
degree, including degenerate simplices.

### Searches

- `msearch.py leanfinder`, query `Descending filtration of an ordinal four
  block collapse by inner horn attachments`: eight hits, all fixed
  three-dimensional horn descent/gluing declarations such as
  `SSet.horn₃₁.desc` and `SSet.horn₃₂.desc`; no filtration theorem.
- `msearch.py loogle`, query `SSet.horn, SSet.stdSimplex`: twelve hits,
  including `SSet.horn`, `horn.face`, `horn.const`, `horn_obj_eq_univ`,
  and `horn.faceι`; these define or describe one horn, not this family.
- `msearch.py grep`, query `horn.*filtration|collapse.*horn|preimage.*horn`,
  subdirectory `AlgebraicTopology`: five hits in
  `SimplicialSet/AnodyneExtensions/RelativeCellComplex.lean`.
  I read `Cell.preimage_filtration_map` at line 337: it assumes a supplied
  proper pairing and rank function, and does not construct this four-block
  pairing or assert these endpoints.
- `msearch.py leansearch`, query `finite descending filtration of a standard
  simplex by inner horns under a four block ordinal collapse`: eight hits,
  including `SSet.horn`, `SSet.Finite`, `SSet.horn_obj`, `horn.edge`, and
  `stdSimplex.face`; none is the node's assertion.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, and this project's
  `lean/Sheaf` for `inner_horn_collapse_filtration|four.block.*collapse`
  returned no existing declaration. Upstream blueprint-id search also
  returned no attachment. Broader `horn.*filtration|collapse.*horn|four.block`
  project searches found `InitialPrismHornFiltration`,
  `TwistedArrowBoundaryFiltration` and `TwistedArrowJoinHorn`; the former
  filters a product relative to outer horns, and the latter two use
  twisted-arrow join domains, not the present simplex and collapse.
  I read the initial-prism statement and checked these module signatures.

### Validation

Single-file compilation uses only the authorized `scompile.py` wrapper,
with the standard 60-second limit. The first attempt exposed an ambiguity
with the geometric `stdSimplex.map`; the simplicial functor is now explicitly
qualified as `SSet.stdSimplex.{u}.map`.
The corrected module compiled cleanly both as the sandbox probe (28.3 seconds)
and under its library module name (53.3 seconds), with no errors or warnings.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
