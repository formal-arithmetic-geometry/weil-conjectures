## Worker report

The module `lean/Sheaf/CategoryTheory/InfinityLocalUnionCellAttachment.lean` states
`SSet.Enhanced.infinity_local_union_cell_attachment`. It formalizes the reviewed node
using the canonical ordered-join collage: `localUnionCollage U` is the object `M`, and
`localUnionOver U Y` is the relative object `M_Y`. The theorem keeps the node's small
nonempty partially ordered index, increasing family, strict positive-dimensional chain,
chain-boundary inclusion, exact cell image, exact old intersection, pushout attachment,
zero-skeleton vertex formula, and pairwise local-cone overlap. The theorem is statement
only; its proof is `sorry`.

The Lean rendering of each clause is as follows. `K : SSet.{u}`, `I : Type u` with
`[PartialOrder I] [Nonempty I]`, `U : I → K.Subcomplex`, and `hmono : Monotone U`
render the small simplicial set, nonempty poset, increasing family, and inclusions.
`Y : (nerve I).Subcomplex`, `n : ℕ`, `tau : (nerve I) _⦋n⦌`, `hn : 1 ≤ n`, and
`hstrict : StrictMono tau.obj` render the old upper subset and the nondegenerate strict
positive-dimensional chain. `htau : tau ∉ Y.obj _` and
`hboundary : Subcomplex.range ((boundary n).ι ≫ yonedaEquiv.symm tau) ≤ Y` render
that the chain is new and its entire simplicial boundary is old.

The first conclusion, `Mono (localUnionCell U n tau)`, renders the degreewise injective
natural cell map. The next conclusion places its range in
`localUnionOver U (Y ⊔ Subcomplex.ofSimplex tau)`, rendering the map into `M_{Y'}`.
The preimage equality
`(localUnionOver U Y).preimage (localUnionCell U n tau) = Subcomplex.range (...)`
renders the exact intersection with `M_Y` as the join of `K_{i₀}` with the standard
simplex boundary. The existential `h`, `top`, and `bottom` and the three equations
render the displayed attachment square, while `IsPushout ...` renders the induced
comparison as a simplicial pushout (the colimit universal property recorded by the
Mathlib colimit dependency). The equality at `(nerve I).skeleton 1` renders
`M_{N(I)^(0)} = K ∪ ⋃ i (K_i ⋆ {i})`; `skeleton 1` is the constant-chain subcomplex.
Finally, for `i ≠ j`, the equality
```
range (localUnionCell U 0 (ComposableArrows.mk₀ i)) ⊓
  range (localUnionCell U 0 (ComposableArrows.mk₀ j)) =
range ((U i ⊓ U j).ι ≫ orderedJoinInl K (nerve I))
```
renders that two distinct local cones meet exactly in the pure lower copy of
`K_i ∩ K_j`.

The item’s recorded dependencies were read in full. The declaration
`SSet.Enhanced.coneCategory` is in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; its module supplies the simplicial-set,
standard-simplex, and nerve conventions. The declaration
`SSet.Enhanced.join_cocone_associativity` is in
`Sheaf.CategoryTheory.InfinityJoinCoconeAssociativity`; its ordered-block join is used
for all pure and mixed summand calculations. The Mathlib leaf is
`CategoryTheory.Limits.colimit` in `Mathlib.CategoryTheory.Limits.HasLimits`; its
`Cocone`/`IsColimit` universal property is the meaning of the displayed pushout.
The canonical constructions needed to give the informal `M` and `M_Y` actual Lean
objects are the already landed `localUnionCell`, `localUnionCollage`, `localUnionShape`,
and `localUnionIndex` in
`Sheaf.CategoryTheory.InfinityDirectedUnionLocalColimits`, together with the landed
`localUnionOver` definition in `Sheaf.CategoryTheory.DirectedCoverMixedSubsetCells`.
No private copy of any of these notions was introduced.

Edge cases checked before writing the statement were `K = ∅`, an empty `K_i`, all
`K_i = ∅`, `n = 1`, `n = 2`, equal members of the family, and distinct indices with
nontrivial `K_i ∩ K_j`. The universal quantifiers allow empty lower simplicial sets and
empty family members. The vertex-stage expression uses the zero skeleton and therefore
includes all degeneracies of constant nerve vertices. No directedness or covering
hypothesis was added.

Searches: the inherited reviewed node record contains LeanFinder, LeanSearch, Loogle,
and Mathlib grep searches for ordered-join collage attachments, boundary joins, and
unions as pushouts; each returned no exact theorem. I ran fresh searches with
`msearch.py`: LeanFinder query `simplicial subset collage attaches a strict nerve chain
by a join with its boundary` returned only generic nerve/Segal declarations; Loogle
query `SSet.Subcomplex, orderedJoin, IsPushout` returned zero hits (unknown identifier
`orderedJoin`); grep query `localUnionCollage|localUnionCell|orderedJoin.*boundary`
under `AlgebraicTopology/SimplicialSet` returned zero hits. I also searched the source
checkout and project tree for the item id, collage, ordered join, and cell attachment;
no exact pre-existing declaration was found. The canonical helper declarations above
were found and reused.

Compilation with the required `scompile.py` wrapper succeeds for the delivered module
with no errors or warnings (the expected `sorry` declaration warning is suppressed by
the module option).

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
