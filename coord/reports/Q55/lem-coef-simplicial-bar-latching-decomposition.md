## Worker report

The module `Sheaf.CategoryTheory.SimplicialBarLatchingDecomposition` states the
reviewed stage-1 item. `simplicialBarStage` is the coproduct over chains in
`Over j`, hence its summands are exactly `V(i₀)` with a final arrow to `j`.
`simplicialBarNondegenerateAt` tests only internal arrows using the typed
`eqToHom` formulation of an identity arrow; the final arrow is not tested.
The two coproducts `simplicialBarDegenerateStage` and
`simplicialBarNondegenerateStage` and their split coproduct
`simplicialBarBinaryStage` render the degenerate/nondegenerate partition.

`simplicialBarSurjection` is the proper-surjection object of `D_n`. Its field
`a : Fin n` is the strict inequality `a < n`, `θ` is the order-preserving map,
and `surjective` is its surjectivity. `simplicialBarLatchingUniversal` is the
colimit universal property from the recorded category-colimit definition:
`ι` gives one leg per proper surjection, `compat` is the equation for every
`ρ` with `θ = θ' ≫ ρ`, `desc` gives a factorization for every compatible
cocone, and `uniq` gives uniqueness. The `latching` field supplies the
latching object, its canonical map `u` to the degree-n stage, an isomorphism
to the degenerate coproduct, and the summand equations identifying that map
with the coproduct injection. `decomposition` states the complementary
nondegenerate coproduct isomorphism.

The `stage` field is functorial in `V`; `stageIso` renders
`S_nV(j) = ∐_{i₀→⋯→i_n→j} V(i₀)`. `stageOperator` gives the first-vertex map
for an arbitrary simplex operator and therefore includes the face, internal
face, final face, and degeneracy clauses. `stagePostcompose` is the action on
the final arrow `j → k`. `stageMap` is the action of a natural transformation
of diagrams. The final theorem is the exact statement-only target and has
proof `sorry` as required by stage 2.

The recorded dependency declarations used are:

- `def-weil-pbc-simplicial-set`: Mathlib `SSet`, `SSet.degenerate`,
  `SSet.nonDegenerate`, and related declarations in the recorded files.
- `def-weil-pbc-category-colimit`: Mathlib `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, `colimit.desc`, and `IsFiltered`.
- `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`:
  Mathlib `SSet.exists_nonDegenerate`,
  `SSet.unique_nonDegenerate_dim`, `SSet.unique_nonDegenerate_simplex`, and
  `SSet.unique_nonDegenerate_map`.

No dependency module was needed: all three records are usable Mathlib leaves.
No new DAG node was needed. The existing project declaration
`SimplicialBarProjectiveResolution` was read but not imported, since its
statement is the parent theorem and does not state this latching notion.

Edge cases checked before writing were `n = 0` (the `Fin n` proper-surjection
type is empty and both universal-property families are vacuous), the empty
indexing category `I`, a terminal category in degrees one and two, a discrete
category, a nonidentity endomorphism, mutually inverse nonidentity arrows,
and a final identity arrow with nonidentity internal arrows. These agree with
the reviewed statement: only internal arrows determine degeneracy.

Searches made:

- `msearch.py ... leanfinder "nondegenerate chain decomposition latching object
  simplicial bar coproduct"`: Dold–Kan and `SimplicialObject.Splitting` hits,
  but no exact arbitrary-category labelled bar latching theorem.
- `msearch.py ... loogle "SimplicialObject Splitting latching"`: unavailable
  (`Unknown identifier SimplicialObject`).
- `msearch.py ... grep "latching.*nondegenerate" AlgebraicTopology/SimplicialObject`:
  no hits.
- `rg` over `WeilConjectures/` found no declaration of this item; `rg` over
  `lean/Sheaf` found only contextual latching discussions, not this statement.
- The stage-1 searches retained in the node additionally checked LeanFinder,
  LeanSearch, Loogle, Mathlib source, and project source; all concluded that
  the exact weighted forward-chain formula is absent.

No `STATEMENT-DISPUTED` flag or node correction is required.

## Second reading by Q55

I reread the current node and this module after compilation. The category and
diagram hypotheses are the explicit binders `{M : Type u}`, `Category.{v,u} M`,
`HasCoproducts M`, `{I : Type v}`, and `SmallCategory I`; no model structure or
cofibrancy hypothesis was added. The chain object and every label are rendered
by `simplicialBarStage`, with the final arrow represented by the `Over j`
object. The strict proper-surjection bound is `a : Fin n`; the map equation in
`simplicialBarLatchingUniversal.compat` has the same orientation as the node's
`θ = ρ θ'` convention (written as `θ = θ' ≫ ρ` in Lean).

The decomposition clause is an isomorphism to the coproduct indexed by the
two subtype families, so it retains both summands and does not assume
monomorphism of coproduct injections. The latching clause records the
universal factorization, its canonical map, and the componentwise injection
equations. `stagePostcompose` and `stageMap` cover both naturality clauses.
Degree zero is represented without a special exclusion: `Fin 0` is empty and
the definitions therefore give the initial latching coproduct. The file
compiled cleanly through `scompile.py`, with no errors or warnings.
