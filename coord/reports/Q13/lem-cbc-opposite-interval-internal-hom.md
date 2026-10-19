## Worker report

The target declaration is already present on `newtargets-dag` in
`Sheaf/CategoryTheory/OppositeIntervalInternalHom.lean` as
`SSet.Enhanced.oppositeIntervalInternalHom`, with the helper definition
`SSet.Enhanced.rho`. This packet records the Q13 validation of that exact
statement and declaration; the node's existing `lean` record is unchanged.

The module imports `Sheaf.CategoryTheory.EnhancedDiagramsCones`, which supplies the
recorded statement dependency `def-cbc-enhanced-diagrams-cones`, in particular
`SSet.Enhanced.evaluation` and the internal simplicial hom conventions. The helper
`rho` is the pullback lift of internal-hom postcomposition and endpoint evaluation.
It has real data and no `sorry`.

The theorem's first existential clause binds a family `R` of isomorphisms
`((ihom (Delta[1])).obj E).op ≅ (ihom (Delta[1])).obj E.op`. Its following universal
clause renders the reversal formula on every degree `n`, inner degree `m`, interval
map `i`, and simplex map `theta`, with `irev` and `thetarev` defined by
`SimplexCategory.rev.map`. The next conjunction gives both endpoint identities,
exchanging 0 and 1. The following clause gives naturality for every simplicial map
`p : E ⟶ B`. The next clause states preservation of every degreewise pullback by
`SSet.opFunctor`. The next clause states the transported endpoint-1 pullback
square. The final existential clause supplies its comparison isomorphism `T`, both
projection identities, and the corner-map identity involving `rho p 0` and
`rho (SSet.opFunctor.map p) 1`. No Kan, nonemptiness, or other hypothesis is added.

The dependency declaration used is:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations
  `SSet.Enhanced.evaluation`, `SSet.Enhanced.mappingSpace` and the internal-hom,
  product, and pullback conventions from `def-cbc-enhanced-diagrams-cones`.

Edge cases checked against the statement and module are empty `E` or `B`, the
identity and constant maps, the zero simplex degree `n = m = 0`, degeneracy and
face operators, and the non-Kan case. The construction is degreewise, so no
inhabitedness or Kan assumption is hidden.

Searches found no distinct full declaration in Mathlib or the source repository:

- LeanFinder/LeanSearch/Loogle queries for opposite internal-homs, interval
  endpoint reversal, and pullback compatibility returned only the primitive
  `SSet.op`, `SSet.op_map`, `SimplexCategory.rev`, and generic closed-category
  infrastructure, none with this complete statement.
- Grep of Mathlib `AlgebraicTopology/SimplicialSet` and
  `CategoryTheory/Monoidal/Closed` found only those primitives and unrelated
  lifting results.
- `rg` over `WeilConjectures/` and `lean/Sheaf` found this declaration only in
  the recorded module; no second independently named notion exists.

The source files read were `Mathlib/AlgebraicTopology/SimplexCategory/Rev.lean`,
`Mathlib/AlgebraicTopology/SimplicialSet/Op.lean`,
`Mathlib/AlgebraicTopology/SimplicialSet/Monoidal.lean`, and the dependency module.
The node is already reviewed and its recorded repair includes the general clause
for every cospan pullback; that clause is present verbatim in the module.

No statement correction or `STATEMENT-DISPUTED` flag is needed. No new nodes or
dependency modules are needed because the only dependency has its recorded
usable declaration.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
