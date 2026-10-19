## Worker report

The module `Sheaf.CategoryTheory.SliceConePrismSimplicial` states
`SSet.Enhanced.slice_cone_prism_simplicial`. Its sole postponed proof is `sorry`.
All helper definitions have real data and all their construction proofs are supplied.
The node statement and proof are unchanged. Its statement dependencies gain the already
landed `lem-coef-infinity-slice-arrow-equivalence`, which owns `rightVertexSlice`.
No new node and no dependency repair is needed.

Source read: https://kerodon.net/tag/0302, Proposition the project server, especially the final
rho/rho-prime formulas and the displayed square for gamma-minus. The node extends those
formulas across the right cone and explicitly gives the elementary simplicial checks.
The theorem docstring includes all nine proof steps. This is a statement delivery;
it does not assert that the postponed theorem is proved.

Hypothesis and clause correspondence:

- Arbitrary small simplicial set and vertex: the family quantifies over every
  `(X : SSet.{u}) (c : X _⦋0⦌)`. There is no Quasicategory, Kan or horn-filling binder.
  The arbitrary universe `u` is explicitly declared.
- The right slice L and its operators: `rightVertexSlice X c` is the existing subtype
  of `X _⦋n+1⦌` with its last vertex equal to c. Its operators use the existing
  `appendLast`. This is exactly the node's L, rather than the coherent arrow fiber.
- W: `rightJoinCone (rightVertexSlice X c)` is the existing ordered join with `Δ[0]`.
- J: `relativeJoin (evaluation Δ[1] X (stdSimplex.obj₀Equiv.symm 1)) (𝟙 X)` uses
  target evaluation of the internal hom and the identity of X, as required.
- Epsilon and the base cut: the first two clauses of `IsSliceConePrism` quantify over
  ordinal morphisms epsilon. The pure-base clause is cut r=n. The mixed clause
  has base dimension r and final dimension s, in total degree r+s+1. The pure-final
  clause is cut r=-1. These exhaust the unique normal forms of the ordered join.
- Tau ending at c: in both nonempty-base clauses, tau belongs to `rightVertexSlice`;
  its `.val` is the `(r+1)`-simplex with exactly the required last-vertex condition.
- Rho: `sliceConeRho r epsilon` sends a product simplex point to r+1 precisely when
  both its arrow coordinate and epsilon of its base coordinate equal 1, and to its
  base coordinate otherwise. This is the full map of nerves of the ordered posets,
  not just a list of vertex values. The mixed clause restricts epsilon along
  `sliceConeInitial (r+s+1) r ...` to the initial base block.
- Nu: `sliceConeNu n r epsilon` is j for j≤r and epsilon(j)=0 and r+1 otherwise.
  Its monotonicity is part of the actual construction. The full target coordinate
  is `X.map (sliceConeNu ...).op tau.val` in both nonempty-base clauses.
- Initial arrow prism: `sliceConeArrow` is `yonedaEquiv` of the curry of
  `sliceConeRho ... ≫ yonedaEquiv.symm tau.val`. It is therefore exactly tau-rho
  as a simplex of `Fun(Δ[1],X)`.
- Relative-join cut, initial block and final block: the first two clauses prescribe
  equality of `.val`, meaning both pullback coordinates, including the join simplex,
  interval word and full target coordinate. In the mixed clause the join simplex is
  `sliceConeJoinSimplex` of the initial arrow and the constant c-simplex; its parameter
  is the existing `joinBlockWord` on the identity of the concatenated ordinal. In the
  pure-base clause it is `orderedJoinInl` and the constant-zero interval word. Thus the
  formal empty final block at r=n is included. Membership proofs of the codomain
  already impose the relative-join pullback equation.
- Pure-X case r=-1: the third clause equals the existing `relativeJoinInr` of the
  constant c-simplex, for every epsilon and degree. This includes constancy on the
  cone vertex as a simplicial map, not merely constancy on its vertices.
- All faces and degeneracies: G is an actual simplicial morphism. Naturality of that
  morphism includes every ordinal operator, including operators deleting a whole
  join block and degeneracies with repeated values.
- Pointed naturality: the theorem's second conjunct is the induced-map formula on
  every simplex, for all h:X→Y and c. The target vertex is explicitly h(c), which
  parametrizes every pointed map. `sliceConeSliceMap h c` postcomposes tau by h;
  `orderedJoinFunctor.map` acts on the cone and on the arrow/X blocks; the interval
  is unchanged and the full base simplex is postcomposed by h. Equality of these
  ambient coordinates is equality of the induced relative-join simplices, since
  relativeJoin is a subcomplex of that product. No arbitrary comparison map is used.
- Every base vertex e:a→c: the last clause of `IsSliceConePrism` is an equality of
  simplicial maps on the full interval. It factors G(-,e) through `relativeJoinInl`.
  Its internal-hom edge is the curry of `sliceConeRho 1 (𝟙 _)` followed by the
  degeneracy `[2]→[1]`, (0,1,2)↦(0,0,1), and then e. This square is e precomposed
  with (t,j)↦1 iff t=j=1. Thus its horizontal arrows are 1_a,e, its source side
  is 1_a and its target side is e, including the whole square's simplicial data.
- The theorem supplies one family G with all the clauses together, so the naturality
  assertion concerns the maps with the prescribed formulas. No hollow definition,
  arbitrary map parameter or mere Nonempty choice replaces the canonical construction.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.evaluation`,
  `SSet.Enhanced.appendLast`; Mathlib's standard simplices and internal hom are
  exposed by the same interface. Its mappingSpace was also read to verify that
  rightVertexSlice is the unpinched slice, not the pinched mapping space.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `SSet.Enhanced.rightJoinCone`.
- `Sheaf.CategoryTheory.RelativeJoin`: `SSet.Enhanced.relativeJoin`,
  `SSet.Enhanced.relativeJoinInl`, `SSet.Enhanced.relativeJoinInr`,
  `SSet.Enhanced.joinBlockWord`. The definitions of relativeJoinMap and the
  degreewise subcomplex/projections were read to check the naturality formula.
- `Sheaf.CategoryTheory.SliceArrowEquivalence`: `SSet.Enhanced.rightVertexSlice`,
  from the added, already landed statement-dependency node. This helper has no
  Quasicategory assumption; that module's equivalence theorem is not invoked.
- Transitive join infrastructure: `SSet.Enhanced.orderedJoinFunctor`,
  `joinAugmentation`, `joinGenerator`, `orderedJoinInl`, `orderedJoinInr`.
  The new `sliceConeJoinSimplex` only inserts ordinary simplices into this existing
  generator via the augmentation counits; it does not redefine the join.

Edge cases checked before drafting and on rereading: n=0 (both pure factors), a
mixed 1-simplex with r=s=0, empty base r=-1, empty final block r=n, arbitrary
repeated values and missing vertices in ordinal operators, constant-zero and
constant-one epsilon, degenerate e, X=Δ[0], and the empty simplicial set (no c,
so no pointed instance). In particular nu is constant at the last vertex whenever
the inverse-image base block disappears, and the pure-final rule then agrees.
No size equality or nonemptiness assumption was introduced.

Searches made (2026-10-17):

- msearch LeanFinder: "A simplicial map from the interval times the right cone on
  the slice over a vertex to the relative join of the arrow simplicial set with
  its target, given by ordinal prism formulas". Eight hits, on pointed Kan
  multiplication/relation structures, horns, coskeleta, ordinary interval
  inclusions and Cech conerves. None states the slice-cone relative-join prism.
- msearch Loogle: `SSet, "prism"`. Zero hits.
- msearch grep: `sliceConePrism|rightVertexSlice|sliceArrowPrism|relativeJoin`
  in Mathlib AlgebraicTopology. Zero hits.
- msearch LeanSearch: "simplicial right slice cone prism relative join arrow target
  evaluation". Eight hits, on augmented simplicial objects and ordinal-generator
  evaluation. No matching construction or theorem.
- rg of the source WeilConjectures and side Sheaf trees for the item id,
  `rightSlice`, and `sliceConePrism`: no matching theorem. More detailed side
  searches found `rightVertexSlice` in SliceArrowEquivalence and the relative
  join in RelativeJoin; both are reused. Searches of Mathlib, WeilConjectures and
  Sheaf for all proposed helper names and `slice_cone_prism_simplicial` found
  no existing declarations. The existing sliceArrowPrism has a different formula
  (independent of epsilon) and is not this two-parameter prism.

No statement correction and no STATEMENT-DISPUTED issue.

## Second reading by Q126

No second worker was started: the dispatch brief explicitly prohibits other agents
and specifies direct delivery followed by the maintainer's independent review.
I reread the node against the file, checking the full-coordinate mixed-summand
formula, both empty blocks, epsilon restriction to the base, the direction of the
currying, and the sigma-zero square. The hypothesis/clause correspondence above
records that reading. The independent mathematical review remains the maintainer's.
