## Worker report

The module `Sheaf.AlgebraicTopology.CubeRelationRealization` states
`SSet.CubeRelation.realization`. Its only postponed proof is this theorem's `sorry`.
The node statement is unchanged. The module supplies the concrete auxiliary objects
introduced by this very node, with no new independent notion and no dependency repair.

The hypotheses and clauses correspond as follows.

- `n : ℕ` renders `n ≥ 0`. The binder `i : Fin (n + 1)` renders exactly `0 ≤ i ≤ n`.
  The indices describe a particular finite set, so no universe parameter is necessary.
- `Face n i` is the subtype `{U : Set (Fin (n + 1)) // i ∈ U}`. Its inherited order
  is subset inclusion, so it is exactly the node's `F_{n,i}`.
- `RelationPoset n i` is a subtype of `Face n i × Face n i`; its predicate is
  `∀ j, i < j → (j ∈ UV.1.val ↔ j ∈ UV.2.val)`. Membership equivalence for all tail
  elements is precisely equality of the intersections with `{i+1,...,n}`. Its inherited
  order is inclusion in both components. `first` and `second` are the actual order
  projections, converted to functors using `OrderHom.toFunctor`.
- `CoordinateSpace n i` is the subtype of two functions `Fin (n+1) → unitInterval`
  requiring `pq.1 i = 1`, `pq.2 i = 1`, and `∀ j, i < j → pq.1 j = pq.2 j`.
  Here `unitInterval` is Mathlib's real closed interval `[0,1]`; product and subtype
  topology give exactly the ordinary finite real coordinate subspace topology.
- `nerve` is the ordinary category nerve. An `r`-simplex `σ` is a functor from
  `Fin (r+1)` into the indicated inclusion poset, so `σ.obj a` is the `a`-th chain entry.
  The notation `|K|` means `SSet.toTop.obj K`, the ordinary quotient realization
  required by the recorded enhanced-diagram dependency.
- In the first conjunct, `SSet.toTop.map (SSet.yonedaEquiv.symm σ) t` is the point
  represented by the chain `σ` and simplex parameter `t`. The real barycentric weight
  is `(⦋r⦌.toTopHomeo t) a`; the real characteristic coordinate is the displayed
  `if j ∈ ... then 1 else 0`. The two equalities give both sums in the node's formula.
  The existential `h : |nerve (RelationPoset n i)| ≃ₜ CoordinateSpace n i` asserts
  a well-defined map with this formula and a continuous inverse. Quantifying the
  formula over every simplex and every parameter includes all quotient identifications.
  Thus this is the specified characteristic map, not an unspecified homeomorphism.
- The next conjunct specifies the face chart `c` on every face-chain representative
  by exactly its characteristic-vector sum. It is a `ContinuousMap` to the whole cube,
  as in the node's proof step 6. The representative formulas determine both `c` and `h`
  uniquely because characteristic simplices cover the realization. No arbitrary map,
  assumed homeomorphism, or data chosen using `sorry` is introduced.
- Finally, for every point `x`, the two equalities are respectively
  `c (SSet.toTop.map (nerveMap (first n i)) x) = (h x).val.1` and the same equation
  for `second` and `.val.2`. These are exactly the two required projection compatibilities.

Dependency declarations and sources read:

- `def-cbc-enhanced-diagrams-cones` records
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, with main declaration
  `SSet.Enhanced.coneCategory` and its additional enhanced constructions. I read its
  module docstring, imports, and the relevant realization convention; it explicitly
  reuses Mathlib's ordinary `CategoryTheory.nerve` and `SSet.toTop`. This module is
  publicly imported and no copy of either notion is defined.
- The proof dependency `lem-cbc-realization-cw-subcomplex` records
  `Sheaf.AlgebraicTopology.RealizationCWSubcomplex`,
  `SSet.realization_cw_subcomplex`. Its full theorem signature and proof docstring were
  read: the first conjunct supplies the unique positive nondegenerate representative
  used in proof step 4. It is imported without `public`, solely for the future proof.
- The exact types and docstrings of `CategoryTheory.nerve` and `CategoryTheory.nerveMap`
  were read in Mathlib's `AlgebraicTopology/SimplicialSet/Nerve.lean`.
  `SimplexCategory.toTopHomeo`, in `AlgebraicTopology/SimplicialSet/TopAdj.lean`, is the
  homeomorphism to the real barycentric standard simplex; this module is publicly imported.
  The characteristic maps in the signature use Mathlib's Yoneda equivalence and realization
  directly, avoiding a second definition of the proof dependency's characteristic maps.

The source was checked in [HTT, Section 2.2.2, printed p.76](https://people.math.harvard.edu/~lurie/papers/HTT.pdf#page=94).
The displayed quotient retains only the coordinates above `i` on the face where coordinate
`i` is one. This matches the relation used here. The node explicitly records that its
finite triangulation proof is an agent expansion of the relation-space comparison.
The theorem docstring preserves all six proof steps, including sorting coordinates,
normal-form injectivity, finite closed-cover inverse continuity, and both projections.

Edge cases checked before writing:

- `n = i = 0`: both face and relation posets have one object, and the coordinate
  space consists of the unique pair whose only coordinates are one. The formula works
  in all simplex degrees, including constant degenerate chains.
- `i = 0`: there are no independent coordinates below `i`; all tail coordinates
  are shared, with no extra condition in the Lean statement.
- `i = n`: the tail condition is empty. The two lower-coordinate blocks are independent.
- For `n = 1`, `i = 0` gives the diagonal interval and `i = 1` gives a square.
- The simplex parameter ranges over the entire closed standard simplex. Zero weights,
  repeated vertices, and equal coordinate levels are all allowed. No nondegeneracy,
  positivity, or strict-chain hypothesis is added to the theorem.
- Empty subsets are correctly excluded in `Face` only because they do not contain `i`;
  after the proof's removal of the fixed coordinates, the empty independent-label subset
  remains present. No nonempty-label hypothesis excludes the zero-dimensional case.

Searches for an existing declaration:

- `msearch.py`, LeanFinder: "The geometric realization of the nerve of pairs of subsets
  containing i and agreeing above i is homeomorphic to the subspace of pairs of cubes
  with coordinate i equal to one and equal coordinates above i by barycentric
  characteristic vectors". Eight results: `Cube.splitAt`, `Cube.insertAt`, standard-simplex
  comparisons, a singular-simplex equivalence, and nerve degeneracy. None states this result.
- `msearch.py`, Loogle: `CategoryTheory.nerve, SSet.toTop, Homeomorph`. No hits.
- `msearch.py`, grep in Mathlib `AlgebraicTopology`:
  `characteristic.*(cube|vector)|cube.*(Homeomorph|realization)|Boolean.*realiz`. No hits.
- `msearch.py`, LeanSearch: "Geometric realization of a Boolean inclusion poset is
  homeomorphic to a cube by barycentric characteristic vectors". Eight results concern
  Cantor space, cube coordinate insertion, real parallelepipeds, and Boolean order
  structures; none is the characteristic-coordinate realization theorem.
- `rg` in the upstream `WeilConjectures` tree and `dag/lean_names_upstream.json`, and
  the explicit upstream item-id search: no matching declaration or occurrence of this id.
- `rg` in the project's `lean/Sheaf`: `PinchedCubeLatching.lean` has the related nonempty
  subset poset `P`, the face subcomplex `face`, and its existing simplicial coordinate map
  `faceCoordinates`, but it neither defines this relation poset nor states its realization
  homeomorphism. The mentions of characteristic coordinates and the relation poset are in
  its proof docstring. `JoinBoundaryCubicalExtension.splitCube` splits a simplicial product
  coordinate and is also a different construction. The helpers here introduce only the
  objects of the assigned node, not a replacement for either existing simplicial construction.
- A search for the proposed `SSet.CubeRelation` names found no existing declaration.

Validation: `scompile.py Q89 lem-coef-cube-relation-realization` compiled the delivered
module successfully under the required per-file 60-second limit, in both its sandbox and
library module positions, with no errors or warnings. The first compile identified only
missing decidability for set-membership characteristic functions; `open Classical in` on
the theorem supplies these decisions. All variables and simplex dimensions are explicit.

No statement dispute, statement correction, new node, or dependency module is needed.

## Second reading by Q89

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
