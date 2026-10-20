## What changed

Proved `CategoryTheory.perfectRingHom_tensorDual_degree_map_exists` in
`Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeMap`, with its exact existing signature.
The proof constructs the signed evaluation pairing with Mathlib `dualTensorHom`, transports
it through the actual sheaf tensor comparison, and assembles its diagonal coordinates using
the Hom product and total tensor coproduct universal properties.

Three proved private helpers provide the tensor comparison at the unique point, linear dual
evaluation, and the signed evaluation block. The proof reuses the existing private
`pointLift` and `pointHomEquiv` of `RingHomExtensionDegrees` and `ringHomComplex_isLimit`
of `PerfectRingDualTermFlat` through proof-only `import all`. No existing declaration,
statement, definition, or public import was changed. The node proof now records this route. The conservative command-level interface
check is documented in
`coord/changes/H3-perfect-ring-degree-map-local-elaboration.md`; no consumer adapts.
The complete module compiled cleanly through `lcompile.py` (32.2 seconds).
Sequential elaboration and local irreducibility of `homComplexFunctor` and
`SheafOfModules.monoidalCategory` keep large chosen constructions folded during
conversion checks. The delivery probe verifies the axioms of all declarations. The unchanged direct
consumer `PerfectRingHomTensorDegrees` compiled against the proved module (8.3 seconds). The constructions cover zero rings,
zero modules, and arbitrary unbounded complexes.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.perfectRingHom_tensorDual_degree_map_exists`
(node `lem-pc-perfect-ring-hom-tensor-degree-map`).

Holes added: none. Holes left in the delivered module: none. Split off: zero.
All three new private helpers are completely proved.

## No longer needed

Removed the direct proof imports `WeilConjectures.Algebra.Homology.HomComplex` and
`Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap`; the statement import already provides
the shared Hom and ring interfaces transitively. Kept `PerfectRingDualTermFlat` as a
proof-only `import all` because its established limiting-fan lemma is used, along with
its already-public definition `perfectRingDual` supplied by the statement import.
Added proof-only imports of `Mathlib.LinearAlgebra.Contraction` and
`Sheaf.Algebra.Homology.RingHomExtensionDegrees` (the latter `import all` for its point APIs).

The theorem `perfectRingDual_term_isFlat` is unused: neither flatness nor projectivity
is needed to construct evaluation. The derived base-change construction of
`def-pc-perfect-rhom-base-change-map` is unused as a proof dependency; its transitive
ring-site definitions remain part of the unchanged statement dependencies.
No module is withdrawn, and no unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical construction is correct and is now formalized completely.
On the published compile baseline, directly importing the newly migrated upstream
`WeilConjectures.Algebra.Homology.HomComplex` conflicts with the older Sheaf Hom-complex
module already in the statement's import closure. Removing the redundant direct import
uses the same shared constants already provided by the statement import and avoids the
conflict. Reusing the established product-property lemma also avoids expensive reduction
of the chosen Hom-complex existence witness. No library definition repair was needed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
