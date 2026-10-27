## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_uniformizer_cone_coordinates`
without changing its statement. The proof specializes the existing
`CategoryTheory.ringedSingletonKoszulCone` to the coefficient complex O[0],
extracts its coefficient cone isomorphism and unit equation, and tensors that
coefficient isomorphism with the given complex. The proved upstream
`CochainComplex.mapBifunctorMappingCone₂Iso` supplies the shifted inclusion,
including its sign. Explicit right-unitor and tensor-summand formulas prove the
factorization through bidegree (q+1,-1). The exact additive functor's cone
comparison and a cone map induced by a commuting square then prove both required
coordinate identities. The finished node `lem-pc-tensor-mapping-cone-iso`
attaches the upstream tensor-cone isomorphism used as a tool; this leaves the
unit route intact and adds no unproved tool from another unit.

Added the proof imports `Sheaf.CategoryTheory.RingedSingletonKoszulCone`,
`Sheaf.SixFunctors.ProEtale.InternalUniformizerKoszulScalarSquare` and
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`.
Added one public arithmetic lemma in the new module
`Sheaf.SixFunctors.ProEtale.InternalUniformizerKoszulScalarSquare` and its node.
The existing node's proof and proof dependencies follow the implemented route.
No existing signature, public import, definition or source-library file changed.
Local irreducibility settings for totalization, total tensor maps, the Koszul
dual tower, the right unitor and the tensor unit map keep elaboration through
their existing APIs. The local tensor instances remain active through the public theorem, and an
explicit total-tensor instance avoids repeated searches. The public proof applies
the generic transport lemma directly, avoiding a further dependent wrapper. All private proof
calculations remain in the item file and are checked in its single-file compile.

Validation: `lcompile.py --all` compiled the item in 47.4 s and the new module
in 26.8 s. The four private helpers and the public proof compile completely.
Profiling options used to check timings were removed before delivery.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_uniformizer_cone_coordinates`
(node `lem-sfb-internal-koszul-cone-coordinates`). The item module has zero
remaining holes. All four private helpers are proved: the cone map induced by a
square, generic transport of cone coordinates, the coefficient cone comparison,
and the arbitrary-complex inverse coordinate calculation.

Added one hole:
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.uniformizer_koszul_scalar_square`
(node `lem-sfb-internal-uniformizer-koszul-scalar-square`). It is exactly the
arithmetic change-of-generator square between scalar maps, with fixed target
change of basis. It contains no cone, dual Koszul complex or coordinate assertion.
The source and full proof in words are in its docstring. Edge cases checked in
words: zero complex, empty scheme, n=0, arbitrary unbounded complex and torsion
modules. The scalar argument uses only invertible scalars and unitors.

Thus this is a decomposition (one upper hole closed, one strictly simpler hole
added), not a net reduction in holes. The imported singleton theorem
`CategoryTheory.ringedSingletonKoszulCone` is an existing holed declaration newly
used by this proof; this packet adds no copy or new hole for that theorem.

## No longer needed

No existing imports removed and no modules withdrawn.
The item no longer directly uses
`lem-weil-pbc-ringed-negative-koszul-duality`: the existing singleton theorem
encapsulates the coefficient-dual comparison. It remains a dependency of that
theorem, so this is not a claim that it is globally unused.

The generic `lem-weil-pbc-strict-scalar-koszul-comparison` (module `Sheaf.CategoryTheory.StrictScalarKoszulComparison`) is not used: a scalar
square and the explicit tensor-cone isomorphism suffice. It is removed from this
item's proof dependencies. No assertion is made about its other consumers.

The original direct arithmetic dependencies
`det-prop-integral-criterion-constant-coefficients`,
`def-weil-pbc-ringed-ideal-generators`,
`def-sfb-internal-completion-section-transport`,
`lem-pe-internal-section-tensor-comparison` and
`def-sfb-integral-constant-model-realization` move into the scalar-square node's
proof plan as appropriate; they have not been pruned from the library. The
original statement dependencies remain unchanged. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound. Its generic strict scalar comparison
is unnecessary here, and a coefficient specialization avoids needing an inverse
coordinate formula from the singleton theorem for arbitrary complexes. That
formula follows instead from the proved upstream tensor-cone calculation.
No disputed statement, definition repair or forced adaptation is proposed.

A read-only traversal of the existing dependency closure found the pre-existing
cycle `lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`. It is outside this packet. Separate
reachability checks show that none of the three new direct dependencies leads
back to the item; no cycle through this item was introduced.

## New nodes

`lem-sfb-internal-uniformizer-koszul-scalar-square` separates the local
change-of-generator and exact scalar-transport steps of the original plan. Its
conclusion is a commuting square with a scalar source basis change, strictly
before taking cones or comparing with Koszul duals. It is the only new hole and
has its own module, source, complete proof in words, searches and Lean attachment.
No change record is needed: existing statements and definitions are unchanged.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
