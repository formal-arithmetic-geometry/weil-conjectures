## Worker report

The module `Sheaf.AlgebraicTopology.WhiteheadCWHomotopyInverse` states
`SSet.Enhanced.whitehead_cw_homotopy_inverse`, with its entire proof `by sorry`.
No definition or helper theorem is introduced. The natural statement is unchanged.
The source is [Kerodon Proposition the project server](https://kerodon.net/tag/013X), read online,
with the CW convention described in Remark the project server. The current node acquired its
five-step proof while this work was in progress; the delivered node copy includes
that current proof unchanged, and the theorem docstring follows all five steps.
The source is not archived in literature/: WANTED, an archived Kerodon reference
for Proposition the project server and Lemma the project server.

Clause-by-clause correspondence:

- Arbitrary topological spaces: `{X : Type u} [TopologicalSpace X]` and
  `{Y : Type v} [TopologicalSpace Y]`. No separation, connectedness, or
  nonemptiness assumption is imposed on these spaces.
- The continuous map being tested: `{f : C(X, Y)}`. The conclusion applies to
  this same `f`, rather than merely asserting that the two spaces have some
  unrelated homotopy equivalence.
- Each space has CW homotopy type: `hX` and `hY` existentially quantify CW models
  `Z : TopCat.{w}` and `W : TopCat.{z}`, together with CW structures on the entire
  spaces and `Nonempty (ContinuousMap.HomotopyEquiv X Z)` / the corresponding
  expression for `Y`. Existential, independent model universes `w,z` do not
  restrict models to the universe of either source space.
- A CW complex is represented by `Topology.CWComplex (Set.univ : Set Z)` and
  `T2Space Z`, and similarly for `W`. This is the classical Mathlib CW structure,
  not its alternative categorical definition. Its actual fields were inspected:
  `cell`, `map`, `source_eq`, `continuousOn`, `continuousOn_symm`,
  `pairwiseDisjoint'`, `mapsTo'`, `closed'`, and `union'`.
  The cells are indexed by a set in each natural dimension, their characteristic
  maps are defined on closed unit disks in `Fin n → ℝ` (the sup norm disk is
  homeomorphic to the usual disk), their open-cell restrictions are
  homeomorphisms, cell interiors are disjoint, boundaries lie in a finite union
  of lower-dimensional cells, and all cells cover the entire space. The
  `mapsTo'` axiom is precisely closure finiteness. The union of cells through
  dimension `n` gives the node's skeleton and its attaching-disk presentation.
- **Why the model includes `T2Space`:** Mathlib's `closed'` tests closedness of
  intersections with closed cells *in the ambient space*, rather than directly
  testing inverse images in disks. Without a separation property, this class
  alone is too permissive for the node's disk-quotient weak topology. On a
  Hausdorff space, each characteristic disk has compact domain and hence gives
  a closed quotient onto its closed-cell image. Therefore `closed'` is exactly
  the closed-set test on all characteristic disks. Hausdorffness of the CW
  model is intrinsic to the node's standard construction starting from the
  empty space and attaching disks with weak topology: each skeleton is
  Hausdorff by the attaching pushout construction, and the weak colimit is the
  usual Hausdorff CW space. Conversely a Hausdorff classical CW structure
  gives that construction. Thus this pair of Mathlib conditions encodes the
  stated CW notion, without adding a hypothesis on `X` or `Y`. In particular,
  the non-Hausdorff indiscrete two-point space with two nominal zero-cells is
  not accidentally treated as a discrete zero-dimensional CW complex.
- A homotopy equivalence of a space with a CW model is Mathlib's existing
  `ContinuousMap.HomotopyEquiv`: it contains two continuous maps and ordinary
  unbased homotopies of their composites to the identities. Its direction is
  immaterial since the structure has a symmetry operation.
- Path-component bijection: `hπ₀ : Function.Bijective (componentsMap f)`, using
  the recorded dependency's quotient map on `ZerothHomotopy`.
- All positive based homotopy-group isomorphisms:
  `hπ : ∀ (n : ℕ), 1 ≤ n → ∀ (x : X),
  Function.Bijective (homotopyGroupMap f n x)`.
  This uses the recorded cubical map with codomain based at `f x`; it quantifies
  over every source basepoint and every positive dimension. Postcomposition
  preserves boundary-fixed homotopies and concatenation, so the induced maps
  are homomorphisms; their bijectivity is exactly the group-isomorphism
  condition. This is the encoding already used by the dependency's
  `IsWeakHomotopyEquivalence` and the homotopy-equivalence-weak theorem.
- The conclusion is `∃ r : C(Y, X)`, with
  `ContinuousMap.Homotopic (r.comp f) (ContinuousMap.id X)` and
  `ContinuousMap.Homotopic (f.comp r) (ContinuousMap.id Y)`.
  These are both required inverse equations. `Homotopic` means nonempty
  ordinary `ContinuousMap.Homotopy`, whose domain is the product
  `unitInterval × X` or `unitInterval × Y`. Swapping the factors gives the
  node's `X × [0,1]` convention. There is no relative/basepoint-fixed
  condition and no demand for coherent triangle identities.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.componentsMap` and `SSet.Enhanced.homotopyGroupMap`.
  Their full signatures and docstrings were read. The former is the path
  component quotient map; the latter is postcomposition on the quotient of
  continuous based cubes by boundary-fixed homotopies.
- `Mathlib.Topology.CWComplex.Classical.Basic`: `Topology.CWComplex`, with
  `Topology.CWComplex.closed` and the closed-cell compactness/closedness lemmas
  inspected to check the exact weak-topology meaning. No new CW definition.
- `Mathlib.Topology.Homotopy.Equiv`: `ContinuousMap.HomotopyEquiv`, and the
  underlying `ContinuousMap.Homotopic` / `ContinuousMap.Homotopy`.
- Proof-only import `Sheaf.CategoryTheory.HomotopyEquivalenceWeak` supplies
  `SSet.Enhanced.homotopy_equivalence_weak` for proof step 3. Its full statement
  and docstring were read. The other proof prerequisite,
  `lem-cbc-cw-source-homotopy-lift`, currently has no Lean record; no import is
  possible yet. This is a proof prerequisite, not an absent statement notion,
  and is not restated in this delivery. Its future module import is for the
  maintainer to add when it is stated, as stages/2-statements.md §3.7 specifies.

Edge cases checked:

- Empty CW models are allowed by the cell-family structure (all index sets
  empty); `T2Space` also allows the empty space. A homotopy equivalence with an
  empty model forces the corresponding space empty, rather than asserting
  arbitrary maps out of a nonempty space.
- If `X` is empty, surjectivity of `componentsMap f` forces `Y` empty. If `Y`
  is empty, the map `f` forces `X` empty. No basepoint is silently selected.
- Disconnected CW complexes are allowed and every source basepoint is tested.
- `n = 0` is intentionally excluded from `hπ` and handled by `hπ₀`; `n = 1`
  is included, with no abelian-group requirement imposed on the fundamental
  group. Higher dimensions have no cutoff.
- `X` and `Y` need only have CW homotopy type, and need not be Hausdorff or
  themselves carry any CW structure. Homotopies may move all basepoints.
- Distinct universes for `X`, `Y`, and their two models are explicit. All
  variables and universes are bound and `autoImplicit` is disabled.

Searches for an existing theorem (all via the prescribed `msearch.py` wrapper
or the read-only source trees):

- LeanFinder: “A continuous map between spaces of CW homotopy type inducing a
  bijection on path components and isomorphisms on all based homotopy groups
  has a continuous homotopy inverse”. Eight hits: homotopy-equivalence
  structures, their projections/symmetry and homotopy symmetry. No Whitehead
  theorem for these spaces.
- Loogle: `Topology.CWComplex, ContinuousMap.HomotopyEquiv`. Zero hits.
- LeanSearch: “Whitehead theorem for spaces of CW homotopy type”. Eight hits:
  abstract left/right Whitehead, contractible-space equivalences,
  `TopCat.CWComplex`, and related notions. The full left/right Whitehead
  signatures in `ModelCategory/Homotopy.lean` were read: they assume a supplied
  model structure and cofibrancy/fibrancy, so do not state this topological
  result on arbitrary spaces of CW homotopy type.
- Mathlib grep in `Topology`:
  `[Ww]hitehead|[Ww]eakHomotopyEquiv|weakHomotopyEquiv`. Four hits, consisting
  of Whitehead-manifold remarks and classical CW documentation. No theorem.
- `rg` in upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `CWComplex`, `Whitehead`, and the proposed
  name; also `grep -rn` for this item id in upstream. No existing upstream
  declaration or duplicate name. The shared realization-weak-equivalence
  module mentions this item in its proof plan, rather than stating it.
- Read both Mathlib CW definitions. The categorical one uses relative cell
  complexes; the classical one explicitly exposes the closure-finiteness
  condition of the node and is used with the separation condition explained
  above. These existing notions are reused, not copied.

Validation: `scompile.py N4 lem-cbc-whitehead-cw-homotopy-inverse` compiled
both the sandbox copy and the library module path cleanly, each within the
60-second limit. The only postponed result is the named main theorem.
There is no statement correction, missing dependency interface, new node,
or unresolved statement dispute.

## Second reading by N4

I reread the copied node `dag/nodes/sec-smooth-purity/lem-cbc-whitehead-cw-
homotopy-inverse.json`, Kerodon Proposition the project server (013X), and the complete
Lean file. The source proposition says: for a continuous weak homotopy
equivalence `f : X → Y`, when both spaces have the homotopy type of CW
complexes, `f` has a continuous two-sided homotopy inverse. The node expands
that proposition as follows, and the Lean signature renders each item as
shown.

1. `X` and `Y` are arbitrary topological spaces: `{X : Type u}
   [TopologicalSpace X]` and `{Y : Type v} [TopologicalSpace Y]`. No
   separation, connectedness, or inhabitedness is added to the source spaces.
2. The tested map is the given `{f : C(X, Y)}`. It is the same `f` used in
   both `componentsMap f` and `homotopyGroupMap f n x`; there is no unrelated
   existential map.
3. `X` has CW homotopy type: `hX` existentially supplies `Z : TopCat.{w}`,
   `T2Space Z`, `Nonempty (Topology.CWComplex (Set.univ : Set Z))`, and
   `Nonempty (ContinuousMap.HomotopyEquiv X Z)`. `Y` is rendered identically
   by `hY` with independent model universe `z`. The homotopy-equivalence
   structure is symmetric, so its orientation `X ≃ₕ Z` (respectively
   `Y ≃ₕ W`) expresses the node's existence of a CW-to-space equivalence.
   `Topology.CWComplex univ` supplies the disk characteristic maps, boundary
   closure-finiteness, and weak-topology condition; `T2Space` records the
   Hausdorff condition intrinsic to the standard disk-attachment CW model.
4. The weak-equivalence component clause is exactly
   `hπ₀ : Function.Bijective (componentsMap f)`, using the dependency's
   path-component quotient map.
5. For every natural dimension `n` with `1 ≤ n` and every source basepoint
   `x : X`, the positive based homotopy-group map is bijective:
   `hπ : ∀ n, 1 ≤ n → ∀ x, Function.Bijective (homotopyGroupMap f n x)`.
   This is the node's integer `n ≥ 1` clause under the cubical convention of
   `def-cbc-enhanced-diagrams-cones`; degree zero is handled by item 4.
6. The conclusion is the existential inverse `∃ r : C(Y, X)` together with
   `ContinuousMap.Homotopic (r.comp f) (ContinuousMap.id X)` and
   `ContinuousMap.Homotopic (f.comp r) (ContinuousMap.id Y)`. These are the
   two ordinary, unbased inverse homotopies. Mathlib's `Homotopic` uses the
   interval product with the other factor first; the coordinate swap is the
   canonical homeomorphism of ordinary products and imposes no extra
   condition.

No mismatch was found and no Lean text was changed. In particular, the
`T2Space` conjunct is not a separation hypothesis on `X` or `Y`: it is on the
chosen CW model and expresses the standard Hausdorff CW-space convention
behind the node's disk-attachment description. The model universes `w` and
`z` are independent, and all variables are explicitly bound with
`autoImplicit false`.

Edge cases checked: the cell families may all be empty, so the empty CW model
is admitted; a homotopy equivalence with that model forces the corresponding
space empty. If either source space is empty, the existence of `f` and the
component bijection force the other to be empty. Disconnected CW models are
allowed. `n = 0` is excluded from `hπ` and represented by `hπ₀`; `n = 1` and
all higher dimensions are included. No basepoint is chosen when a space is
empty, and the homotopies are not basepoint-fixed.

I searched for an existing declaration with the required three searches:
LeanFinder query “Whitehead theorem for spaces of CW homotopy type inducing
component and based homotopy-group bijections” (hits were abstract model-
category Whitehead operations and `ContinuousMap.HomotopyEquiv`, no theorem);
Loogle query `Topology.CWComplex, ContinuousMap.HomotopyEquiv` (zero hits);
and grep of Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and
`dag/lean_names_upstream.json` for `Whitehead`, `CWComplex`, and the proposed
declaration (only unrelated CW documentation and proof-plan references).
The existing dependency declarations were read in full:
`SSet.Enhanced.componentsMap` and `SSet.Enhanced.homotopyGroupMap` in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, and the proof-only theorem
`SSet.Enhanced.homotopy_equivalence_weak` in
`Sheaf.CategoryTheory.HomotopyEquivalenceWeak`. Neither dependency is
restated or altered. The two DAG citers found by `grep -rl` are
`lem-cbc-cw-source-homotopy-lift` and `lem-cbc-realization-weak-equivalence`;
the item is used by both only as the final Whitehead step, so their uses hold.

The module was recompiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N4
lem-cbc-whitehead-cw-homotopy-inverse
lean/Sheaf/AlgebraicTopology/WhiteheadCWHomotopyInverse.lean`; both sandbox
and library checks passed with only the permitted `sorry` postponement.
