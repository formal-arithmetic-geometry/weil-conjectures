## Worker report

Item: `lem-coef-ex-comparison-weak-equivalence`, group Q93, stage 2.

The module `Sheaf.AlgebraicTopology.ExComparisonWeakEquivalence` states
`SSet.exLastVertexUnit_isWeakHomotopyEquivalence`, with the entire proof `by sorry`.
No definitions or other DAG statements are added. The node is changed only in `lean`.
Its seven proof steps are written in the theorem docstring, including the explicit
homotopy formula, inverse-on-classes argument, chain-of-chains homotopy and the two
adjunction endpoint checks. Every universe and variable is explicitly bound and
`set_option autoImplicit false` is present.

### Statement, hypothesis by hypothesis and clause by clause

- “For every small simplicial set X”: the sole binder `(X : SSet.{u})`, with explicit
  `universe u`. There is no restriction on u, no finite-dimensionality, finiteness,
  Kan, nonempty or injectivity assumption.
- The simplicial-set notion is exactly Mathlib's `SSet`, the contravariant functor
  from `SimplexCategory` to `Type u`, as recorded by `def-weil-pbc-simplicial-set`.
  I opened the signatures/docstrings of `SSet`, `SSet.degenerate`,
  `SSet.nonDegenerate`, `SSet.Subcomplex` and `SSet.Finite` in its recorded Mathlib
  files. The latter four notions are not needed in this theorem's signature.
- The nonempty-subset poset in degree n is already Mathlib's
  `PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1)))`, in
  `SimplexCategory.sd`. Since the ordinal is linearly ordered, every nonempty finite
  subset is a chain. Its partial order is inclusion of the underlying finsets.
  Every subset of a finite ordinal is finite, so this excludes no subsets.
- The nerve of that poset is `SimplexCategory.sd.obj n`. I read Mathlib's
  `Subdivision.lean`, `Order/NonemptyFiniteChains.lean`, `Nerve.lean` and the
  `SSet.stdSimplex`/`SSet.yonedaEquiv` signatures in `StdSimplex.lean`.
- “Ex X has simplices Hom(N(P_+([n])), X)”: the existing `SSet.ex`, defined as
  `Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd`. Its hom sets have an
  inessential `ULift.{0}` wrapper. Operators are precomposition with
  `SimplexCategory.sd.map`; that map takes images of the finite subsets.
- “lambda_n sends S to max S”: the existing `SSet.sdLastVertexOrderHom` sends S to
  `S.finset.max' S.nonempty`; `SSet.sdLastVertex` applies these maxima to the flag
  of subsets in each simplex. `SSet.sdLastVertexCosimplicial` supplies naturality
  for every monotone map, including noninjective maps.
- “The natural j_X sends sigma to sigma composed with lambda_n”: the theorem's
  map is exactly `exLastVertexUnit.app X`. I read the full definition, including
  its naturality proofs, in the local published module and confirmed the current
  server source using `scompile.py --source Sheaf.AlgebraicTopology.ExInfinityFiniteProducts`.
  Its degree-n component is
  `fun x ↦ ULift.up (sdLastVertex n.unop ≫ yonedaEquiv.symm x)`.
  `yonedaEquiv.symm x` is the map from the standard simplex corresponding to x;
  Lean's categorical composition `lambda ≫ sigma` is the node's `sigma ∘ lambda`.
- “Weak homotopy equivalence defined by realization”: the conclusion is precisely
  `Enhanced.IsWeakHomotopyEquivalence (exLastVertexUnit.app X)`, using the recorded
  `def-cbc-enhanced-diagrams-cones` declaration, not a model-category replacement
  or a newly defined predicate.
- “Bijection on path components”: the first conjunct of that existing predicate is
  `Function.Bijective (componentsMap (SSet.toTop.map f).hom)`. Its `componentsMap`
  is the induced map on `ZerothHomotopy`, hence path components of the realization.
- “An isomorphism on every homotopy group at every source basepoint”: the second
  conjunct is `∀ r : ℕ, 1 ≤ r → ∀ x : SSet.toTop.obj X,
  Function.Bijective (homotopyGroupMap (SSet.toTop.map f).hom r x)`.
  The dependency's `homotopyGroupMap` is postcomposition on cubical homotopy classes
  relative to the boundary. It preserves concatenation, so bijectivity is exactly
  the group-isomorphism condition. Degree zero is covered by the component clause.

### Dependency declarations and imports

`def-weil-pbc-simplicial-set` is a Mathlib leaf, with the multi-declaration match
listed above. `def-cbc-enhanced-diagrams-cones` is recorded in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; I read the relevant definitions
`SSet.Enhanced.componentsMap`, `homotopyGroupMap` and `IsWeakHomotopyEquivalence`
and their full signatures/docstrings. Both dependency interfaces are usable.

The exact canonical map is already owned as a helper by the landed node
`lem-coef-ex-infinity-finite-products`, in
`Sheaf.AlgebraicTopology.ExInfinityFiniteProducts`. That module is publicly imported
for `SSet.exLastVertexUnit` and its last-vertex definitions; none of its theorem
clauses is used or assumed. Reusing it avoids a second definition of the same map.
The two original `stmt_deps` suffice to state the node's own specified construction,
and no downstream DAG edge is added.

Import-order note for the maintainer and stage 3: the Ex-infinity node lists this
item as a proof dependency. Because the canonical helper currently lives in its
module, the reverse proof import into `ExInfinityFiniteProducts` must be omitted
under stages/2-statements.md §3.7 (it would close an import cycle). To use this
lemma directly in its eventual proof, the canonical definitions can be moved to
a common construction module by an authorized maintainer/interface refactor.
This delivery neither copies definitions nor edits that downstream node/module.
The current import graph is acyclic and the statement has no logical assumption
of `ex_infinity_finite_products`.

The other proof dependencies currently have no Lean record or Mathlib match:
`lem-cbc-realization-weak-equivalence`,
`lem-coef-subdivision-face-poset-calculus`,
`lem-coef-subdivision-last-vertex-equivalence` and
`lem-coef-subdivision-ex-homotopy-adjunction`.
I read their node statements; their nonexistent modules are not imported, as
required by the “proof dependencies that are stated” rule. Their proofs are not
part of this statement task and none is restated here.

### Edge cases and source check

The empty simplicial set is included: subdivided standard simplices have vertices,
so Ex of the empty simplicial set is again empty, and the component bijection is
empty-to-empty with the basepoint clause vacuous. At n = 0 the subset poset has
only {0}, the last-vertex map is the canonical identification, and j has the
expected degree-zero component. Noninjective monotone maps are included:
max(image S) = image(max S), including a constant map [1] → [0]. Disconnected X
and arbitrary basepoints of the realization, including nonvertex basepoints, are
covered by the existing realization predicate. Positive homotopy degrees have
no upper bound. There is no requirement that Ex X itself be Kan.

I opened the actual source pages:
[Kerodon Theorem the project server, 00Z2](https://kerodon.net/tag/00Z2),
[Construction the project server, 00YU](https://kerodon.net/tag/00YU),
[Proposition the project server, 00Z7](https://kerodon.net/tag/00Z7) and
[Proposition the project server, 00Z8](https://kerodon.net/tag/00Z8).
They agree with the node's statement, canonical comparison and proof route.
No node fault, disputed statement or statement correction was found.
WANTED: an archived copy of these Kerodon pages, as already requested in the node.

### Searches for an existing statement

The following prescribed searches were run; their raw msearch records are also in
sandbox `searches.jsonl`.

- `msearch.py ... leanfinder "For every simplicial set X the canonical last vertex
  comparison X to Ex X is a weak homotopy equivalence"`: eight hits concerning
  Kan/Quillen horn generators, KanComplex and ordinary homotopy-category products;
  no theorem for the one-step Ex comparison.
- `msearch.py ... leansearch "For every simplicial set X the last vertex comparison
  from X to Ex X is a weak homotopy equivalence"`: eight hits concerning realization,
  extra degeneracies, relative homotopies and Yoneda; no one-step Ex comparison theorem.
- `msearch.py ... loogle "SSet.ex, SSet.sdExAdjunction"`: one hit,
  `SSet.sdExAdjunction`, the subdivision/Ex adjunction, not this weak equivalence.
- `msearch.py ... grep "lastVertex|last_vertex|exComparison|ex_comparison"
  AlgebraicTopology`: zero Mathlib hits.
- `rg` for `SSet.ex`, `sdEx`, and subdivision in the pinned Mathlib simplicial-set
  directory located `Subdivision.lean`; the entire file was read. It defines sd,
  ex, their adjunction and the standard-simplex subdivision isomorphism only.
- `rg` for `exComparison|lastVertex|last_vertex|ex_comparison` in
  `WeilConjectures/`: no hits. `grep -rn` for the item id there: no hits.
- `rg` for `exComparison|lastVertex|last_vertex|ex_comparison|SSet.ex|SimplexCategory.sd`
  in the published `lean/Sheaf` tree found the exact last-vertex definitions in
  `ExInfinityFiniteProducts.lean`, which are reused, and unrelated comparison names.
  That module has only an Ex-infinity weak-equivalence theorem, not the one-step
  assertion. The proposed theorem name was also checked against `lean/Sheaf`,
  `WeilConjectures/` and `dag/lean_names_upstream.json`: no collision.

### Validation

`scompile.py Q93 lem-coef-ex-comparison-weak-equivalence <module>` compiled the
module cleanly, including sandbox and final-module paths, with no errors or
warnings (2.1 s and 1.9 s respectively; required overlay 3.2 s). The module has
one named theorem with its proof entirely `sorry`, no new definitions, no local
notation or instances, and no lines over 100 characters.

`deliver2.py Q93 lem-coef-ex-comparison-weak-equivalence --no-push` printed
`OK (dry run)`: the module compiles and preflight passes except for the independent
second-reading section, which is correctly reserved for the second reader. Nothing
was pushed. The dry run is repeated after recording this result and the final search.

## Second reading by Q93

I read the node statement, its Kerodon source place (Theorem the project server, tag 00Z2,
with Construction the project server), the two dependency records, and the complete module.
The item-by-item rendering is:

- “simplicial sets” is the binder `X : SSet.{u}` in
  `exLastVertexUnit_isWeakHomotopyEquivalence`; this is Mathlib's `SSet`, with no
  finiteness, Kan, nonempty, characteristic, or universe restriction beyond the
  single arbitrary universe `u`.
- The degreewise Ex construction
  `Hom(N(P_+([n])), X)` and its subset-image operators are rendered by the existing
  `SSet.ex` used in `exLastVertexUnit`; no private copy or alternate Ex notion occurs.
- The map `S ↦ max S` and the map
  `j_X : X ⟶ Ex X`, with simplex formula `σ ↦ σ ∘ λ_n`, are rendered by the
  existing `SSet.sdLastVertex` and `SSet.exLastVertexUnit` declarations imported from
  `Sheaf.AlgebraicTopology.ExInfinityFiniteProducts`.
- “for every small X” is exactly the universal theorem binder `(X : SSet.{u})`.
- “weak homotopy equivalence after realization” is exactly
  `Enhanced.IsWeakHomotopyEquivalence (exLastVertexUnit.app X)`, whose definition
  expands to bijectivity on `componentsMap` and, for every `r` with `1 ≤ r`,
  bijectivity on `homotopyGroupMap` at every source realization point. Thus the
  component clause, all positive based homotopy-group clauses, quantifier order,
  and source-basepoint convention agree with the node.

No mismatch was found and no source, dependency, or Lean file was changed. The
dependency declarations are usable: `def-weil-pbc-simplicial-set` supplies `SSet`,
and `def-cbc-enhanced-diagrams-cones` supplies the realization predicate. The
canonical comparison is already owned by the landed Ex-infinity module, so a second
definition would violate the one-definition rule. Filtering textual search hits to
actual `stmt_deps` and `proof_deps` gives exactly one citer,
`lem-coef-ex-infinity-finite-products`; its use is a proof dependency and still
holds. Its reverse import is correctly omitted to avoid an import cycle.

Edge cases checked: the empty simplicial set gives the empty component bijection and
vacuous basepoint clauses; `n = 0` has the singleton nonempty-subset poset and the
identity last-vertex map; empty index data and zero-dimensional realization are not
excluded; noninjective monotone maps are covered by the existing naturality proof;
arbitrary disconnected realizations and nonvertex basepoints are allowed; every
positive homotopy degree is quantified; and no Kan assumption is imposed on `X`.
There are no schemes, rings, characteristic assumptions, or independent index types
in this statement, so those families of edge cases do not apply.

I independently repeated the searches with different terms:

- LeanFinder: “The natural map from a simplicial set to its extension functor Ex
  induces isomorphisms on realized homotopy groups” returned homotopy-category and
  product-comparison declarations, none stating this result.
- Loogle: `SSet.ex` returned `SSet.ex`, `SSet.instIsRightAdjointEx`, and
  `SSet.sdExAdjunction`; these construct the functor and adjunction only.
- LeanSearch: “Barycentric subdivision right adjoint one step comparison is a weak
  homotopy equivalence” returned realization/singular adjunction, ordinary
  homotopy-category, and generic model-category results, with no exact match.
- `rg` for `barycentric`, `sdExAdjunction`, `def ex`, `weak.*[Ee]x`,
  `[Ee]x.*weak`, `[Ll]ast[Vv]ertex`, and `last_vertex` in Mathlib's subdivision
  source, upstream `WeilConjectures`, and published `lean/Sheaf/AlgebraicTopology`
  located the reused helper definitions and the different Ex-infinity theorem.
  I opened Mathlib's complete `Subdivision.lean`, its nonempty-chain construction,
  and the server source of `ExInfinityFiniteProducts` through `scompile.py --source`.

The sole theorem has its whole proof `by sorry`, its docstring reproduces all seven
node proof steps, no definitions or dependency modules are added, every binder and
universe is explicit, and its longest source line is 93 characters. A direct string
comparison confirmed `lean.statement` is verbatim the file's signature; comparing
the node copy with the read-only base found only the authorized `lean` field change.
The independent `scompile.py` run compiled both sandbox and library paths cleanly
(1.1 seconds each). No Lean repair or node statement correction was needed.
