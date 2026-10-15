## What changed

Proved both original theorems in `Sheaf.AlgebraicGeometry.SimplicialHomStandardSimplex`, with every existing signature and visibility unchanged. The standard-simplex family is constructed from `K.map` and represents the family functor by evaluation at the identity simplex. For the boundary, private proved helpers factor every nonsurjective operator through a face and prove independence using the face identity and matching equations. They construct the universal boundary family on the existing concrete matching object. Product and multiequalizer lifts, together with the given representing bijection, give the unique comparison isomorphism and restriction map; projection extensionality proves compatibility with the canonical matching map.

The DAG proof follows this construction and drops the two unused auxiliary matching-object dependencies. No new module, statement interface, axiom, or split-off obligation was added. All data constructions are explicit or choose from the proved face-factorization theorem.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.Scheme.simplicial_hom_standard_simplex`.
- `AlgebraicGeometry.Scheme.simplicial_hom_boundary_matching`.

Both belong to node `lem-weil-pbc-simplicial-hom-object-standard-simplex`. No `sorry` remains in the delivered module and no new holes were added. All private helper theorems are proved. The module compiles with the two proof-only imports removed. A separate `#print axioms` check shows both declarations still transitively reach the existing imported `AlgebraicGeometry.Scheme.SimplicialHomFamily.precomp_compatible` hole through the family functor/precomposition interface. This delivery closes the two direct item holes; it does not claim the entire dependency closure is axiom-free.

## No longer needed

Removed proof-only imports:

- `Sheaf.CategoryTheory.ProperFaceMatchingObject`, corresponding to `lem-weil-pbc-matching-object-proper-faces`.
- `Sheaf.CategoryTheory.SimplicialMatchingObject`, corresponding to `lem-weil-pbc-simplicial-matching-object`.

Neither auxiliary theorem is needed by either delivered proof. The proof works directly with the existing concrete matching-object definitions and Mathlib's product and multiequalizer universal properties. These are dependency-edge removals for this item; other importers may still need the modules. All other original proof dependencies are retained, and `def-weil-pbc-semi-representable-object` is recorded explicitly for the concrete definitions. The unit record `sk-prop-h2` assigns no realized statement or step to the removed auxiliary nodes, so its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The old plan allowed either abstract matching-object or proper-face machinery; the concrete product/multiequalizer route makes both auxiliary modules unnecessary. The existing `ProperFaceMatchingObject` proof supplied a useful template, but its factorization calculation does not need injectivity of the simplex operator. Applying it directly to every nonsurjective operator handles degeneracies without a separate proper-face-category comparison. The degree-one case is handled separately, since it has two arbitrary vertex maps and no matching equations. Finiteness and the nondegenerate characterization already exist in Mathlib.

## Second reading by W3

1. **Signatures and visibility.** I compared the delivered module with the repository version. The declarations `simplicial_hom_standard_simplex` and `simplicial_hom_boundary_matching` have identical signatures, namespaces, universes, and visibility. The only module-interface change is removal of two proof-only imports. The node's statement and its two Lean declarations still match clause by clause, including the all-degree boundary nonemptiness assertion and the final uniqueness equation.

2. **Proof and axioms.** The file compiles with `lcompile.py`, with no warnings or errors. It contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. The private helpers are all proved. The axiom check finds only the permitted foundational axioms plus the pre-existing `sorryAx` reached through `SimplicialHomFamily.precomp_compatible`; no new open theorem was introduced.

3. **Statements, sources, and searches.** No statement was split off and no new node was added, so there is no new public statement to duplicate an existing library or Mathlib declaration. The proof uses the existing factorization and face-identity declarations, Mathlib's finite/simplex and product/multiequalizer APIs, and the concrete semi-representable matching-object definitions. I checked the node against Stacks Tags 0177, 018V, and 0186 and tested the boundary construction at degrees `n = 0` and `n = 1`; constant boundary simplices, the degree-one cancellation case, and the higher-degree matching equations all have the required types.

4. **Pruning and route.** The removed imports and corresponding proof-dependency edges are exactly `ProperFaceMatchingObject` / `lem-weil-pbc-matching-object-proper-faces` and `SimplicialMatchingObject` / `lem-weil-pbc-simplicial-matching-object`. The replacement edge to `def-weil-pbc-semi-representable-object` records the definitions actually used. The unit assignment remains `sk-prop-h2`; no unit statement or realized route was changed.

5. **Changes made.** I made no mathematical or interface correction. The reviewed changes are the two completed theorem proofs, their private concrete matching-object helpers, the two unused proof-only import removals, and the matching DAG proof/proof-dependency metadata. The report's dependency and axiom notes accurately describe the remaining imported `sorryAx` and the absence of added holes.
