## What changed

Retired the duplicate `Sheaf.AlgebraicGeometry.PerfectAffineConeModel` under the
existing retirement assignment (`coord/retire-items.tsv`). Reattached its node
`lem-pc-perfect-affine-cone-model` to the already proved source theorem
`AlgebraicGeometry.Scheme.perfect_affine_cone_model` in
`WeilConjectures.AlgebraicGeometry.PerfectAffineConeModel`. Updated the proof text
of that node and its sole parent, `lem-pc-perfect-two-out-of-three`, to record the
actual source implementation. The parent already imports the replacement module.
All mathematical dependencies and unit realizations are retained. Change record:
`coord/changes/R7-perfect-affine-cone-model-duplicate.md`.

The retained source proof constructs the actual mapping cone. Its bounds are
`min (a₁ - 1) a₂` and `max (b₁ - 1) b₂`; its terms are finite-free retracts via the
biproduct of the given retracts and the finite disjoint-union basis. The affine
chain-map representative and the isomorphism of distinguished triangles identify
the third term with this cone. Empty opens, zero complexes and rank-zero free
summands are covered by the same construction. This is the second proof of
[Stacks Tag 08CR](https://stacks.math.columbia.edu/tag/08CR).

Validation through `lcompile.py`: the original item compiles cleanly; a scratch
probe with the complete old signature is proved by applying the source theorem,
and `@original_statement.{u, w} = @perfect_affine_cone_model.{u, w}` is proved by
`rfl`. Both full types were also printed with universe annotations. The probe
imports the actual source consumer. Axiom checks for the probe, the source cone
theorem, its affine-map representative and `isPerfect_two_out_of_three` show only
`propext`, `Classical.choice`, `Quot.sound`. Scratch code is not part of the delivery.

## Proved and sorry left

Actual holes in the original item: 0. Holes closed: 0 of 0. Holes added: 0.
No remaining `sorry` declarations in the delivered module, and no split-off results.
The already proved `AlgebraicGeometry.Scheme.perfect_affine_cone_model`
(node `lem-pc-perfect-affine-cone-model`) remains available from its source module.
This is duplicate retirement, not a new mathematical proof or a decomposition.

## No longer needed

Withdraw `Sheaf.AlgebraicGeometry.PerfectAffineConeModel`, including its duplicate
private helper `strictlyPerfect_mappingCone`. There are zero current Lean importers.
All 1,733 quarantined modules listed in `coord/rework.tsv` were also checked and
contain neither an import of the duplicate nor a use of its theorem name. The only
DAG parent is `lem-pc-perfect-two-out-of-three`, whose implementation already imports
`WeilConjectures.AlgebraicGeometry.PerfectAffineConeModel`; this delivery updates its
proof description and reattaches the cone node to that retained implementation.

The withdrawn module's imports of
`WeilConjectures.AlgebraicGeometry.PerfectComplex` and
`WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative` disappear only
as edges from the redundant module. Both source modules remain used by the retained
source proof. No mathematical node or dependency module is claimed unnecessary:
`lem-sc-derived-hom-mayer-vietoris`, `lem-pc-perfect-affine-map-representative`,
`def-weil-abstract-derived-category`, `def-pc-perfect-complex`,
`def-weil-triangulated-category`, and `lem-sf-triangle-morphism-iso` all remain.
No source declaration or source import is removed or modified.

## Where the brief, the DAG or earlier work was wrong

The item is already sorry-free and appears in the retirement inventory, rather than
being an unfinished cone proof. The inventory's DIFFERENT classification is a
textual difference: the source explicitly supplies the `overFunctor.{u}` universe.
The full old statement elaborates to the same type as the source theorem. The node's
attachment to the duplicate Sheaf module was stale after the parent switched to the
source import; this delivery reconciles it without withdrawing any mathematics.

Logged LeanFinder, Loogle and source grep searches through `msearch.py`. LeanFinder
returned generic triangle lemmas, Loogle confirmed `exists_iso_of_arrow_iso`, and
the logged grep returned no hits; direct `rg` of both library roots located the
exact existing source proof and its consumer. No statement is disputed or weakened.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
