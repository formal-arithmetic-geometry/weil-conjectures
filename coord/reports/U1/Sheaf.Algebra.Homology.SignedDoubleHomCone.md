## What changed

Proved `CategoryTheory.SignedDoubleHomCone.comparison`, following all seven
steps of `lem-sf-double-hom-cone-comparison`. Private helpers construct the
signed shift and cone isomorphisms and their inverses, and prove the component
formulas, naturality and both triangle-arrow identities.

The calculation uses a private abstract Hom/projection interface, instantiated
from the existing component API. `proj` and `productLimit` now reuse
`homComplexπ` and `homComplexIsLimit`; these bodies are definitionally equal to
the old choices. Their signatures and every other public definition are
unchanged. The full nine-clause theorem statement is unchanged.

The file publicly imports
`WeilConjectures.Algebra.Homology.HomComplexComponents` for these definitions.
Internal-Hom additivity uses the existing presheaf API, privately imported from
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit`.
No other library module is changed. The definition replacements, local proof
commands and downstream effects are recorded in
`coord/changes/signedDoubleHomCone-local-calculation.md`.

## Proved and sorry left

Closed the one original hole in
`CategoryTheory.SignedDoubleHomCone.comparison`
(node `lem-sf-double-hom-cone-comparison`). All nine clauses are proved.
There are zero remaining holes, zero added holes and zero split-off statements.
Every private helper is proved. The final module compiles through `lcompile.py`
in 21.0 seconds. The unchanged original consumers
`Sheaf.CategoryTheory.CoefficientBidualTriangles`,
`Sheaf.CategoryTheory.RelativeBidualTriangles`, `Sheaf.Paper.DualityPairing` and
`Sheaf.Paper.DeltaRestriction` compile against it in the same import-ordered
check. Separate `rfl` checks verify both replacement bodies against their old
expressions. No consumer adaptation is needed.

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.Algebra.Homology.HomComplex`. Replaced the direct public import
of `WeilConjectures.Algebra.Homology.HomComplexProjections` by the component API,
which publicly imports it. Both dependency modules remain used transitively.
Removed unused public imports `Sheaf.CategoryTheory.SiteCoveringAxioms` and
`Mathlib.Algebra.Homology.DerivedCategory.Basic`: the statement uses a general
Grothendieck topology, and the cone calculation requires no derived category.

The Hom-complex definition and cone conventions remain needed; neither declared
proof dependency is pruned. No DAG node or whole module is withdrawn. The removed imports are unnecessary
to this proof. The
seven-step route and unit route are preserved, so the existing node's proof
remains accurate. No boundedness, flatness, resolutions, infinite-product
exactness or derived internal-Hom comparison is used.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The earlier attempt had compilation and
server failures. During this session the projection module moved from `Sheaf`
to `WeilConjectures`; the import follows the current source location. Reusing
the existing component API avoids repeatedly elaborating the choice
specifications and reduced the full compile to 27 seconds. The local
irreducibility attribute keeps the chosen bifunctor abstract in this proof.
The change record lists all four downstream modules and their current holders;
their statements retain exactly the same meanings.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
