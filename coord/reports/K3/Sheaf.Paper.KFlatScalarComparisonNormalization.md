## What changed

Filled `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization` without
changing its signature or any public definition. Added private proof helpers for
normalizing the ordinary and derived adjunctions, transporting the tensor and unit
comparisons through the trivial `ULift`, and constructing the ordinary scalar
comparison as the inverse of the ordinary adjunction mate. Its invertibility is
proved using the extension-as-tensor presentation and the given inverse-image
functors. The generalized pure-section formula then gives the unit normalization.

The derived representative equation follows from the existing generic
`mate_computes` proof in `CokernelAdjointExchange`. Preservation of K-flat complexes
and a flat-term K-flat resolution imply invertibility on the entire unbounded
derived category. Added only private proof imports. Simplified the existing
`action_existsUnique` proof: establish the section formula and its lifted
underlying-map equation first, then use the given inverse-image identifications
for naturality and reflection of isomorphisms. Removed the final broad unfolding
step. This avoids computing the concrete unlifted presentations in naturality. Its
statement and all public definitions are unchanged. The tensor, pure-section and
derived-localization constructions are locally irreducible where the proofs
use their comparison APIs. The same control applies to the existing composition
and identity calculations; all attributes are local to this file. Reconstructed the private
`unliftInverseImage` adapter with identical explicit data and graph-law proofs
projected from its former construction, retained as `unliftInverseImageAux`.
This keeps data projections small after the full module reached the compile limit.
Applied the same data/proof separation to `compositeInverseImage`, retaining its
old construction as `compositeInverseImageAux`. Both private interfaces and all
data are definitionally unchanged; no other module uses either declaration.
The changes and consumer checks are recorded in
`coord/changes/K3-kflat-scalar-private-presentation-performance.md` and
`coord/changes/K3-kflat-scalar-composite-presentation-performance.md`.
Added private underlying-map and section formulas for `moduleComparison`, then
kept that constructor locally irreducible. The component calculations in the
composition and identity proofs use these formulas instead of repeatedly
unfolding the constructor. This is recorded in
`coord/changes/K3-kflat-scalar-comparison-projection-api.md`.
Updated the node's proof, proof dependencies and proof origin to record the argument.

## Proved and sorry left

Closed the one hole present when the sandbox was copied:
`SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`
(node `lem-sfb-kflat-scalar-comparison-normalization`). No holes were added or
split off. No textual `sorry` remains in the delivered module.

The existing statements and mathematical calculations of `θ_composition` and
`θ_identity`, already landed by X7 before the sandbox copy, are retained. Their
component/underlying-map proof steps now use the private comparison API; they
are not counted as K3 holes closed.

The complete delivered module compiled cleanly through `lcompile.py` in 55.5
seconds with exit code 0. The new proof and the composition/identity API were
also checked in focused diagnostics. The unlift and composite adapters' equalities
to their former constructions were checked by diagnostic `rfl` proofs. The delivery
command runs the complete module's combined compile, axiom and preflight checks
before pushing.

## No longer needed

No original import was removed and no module or node is withdrawn. Removed the redundant
new direct import `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
its public API is already available through
`Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`. The resolution node remains
needed. Removed the direct proof dependency
`lem-weil-pbc-geometric-module-construction`: the ordinary comparison uses the given algebraic inverse images, the extension tensor
comparison, the inverse-image tensor comparison, and the inverse-image unit
comparison. It does not directly construct a new geometric module functor as
suggested by the old step 2. This is a change of proof route, not a claim that the
geometric-module-construction module is unused elsewhere or transitively.

The normalized adjunctions are obtained directly from the ordinary coefficient
adjunction, the homotopy comparison and the derived Hom comparison. The
representative calculation reuses the generic mate calculation instead of
reproving the full localization argument. Thus
`lem-pur-sheaf-ring-derived-coefficient-adjunction` is no longer a proof-step
dependency; it remains a statement dependency and its public import is retained.
All original public imports remain. Neither dependency is claimed as a module
pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The source initially read had three holes, but X7 landed the composition and
identity proofs before the sandbox was copied. The actual baseline for this
packet therefore has one hole. The original route's geometric module construction
is unnecessary for the given inverse images. No mathematical statement or public
definition repair was needed. The private presentation needed the performance
change described above; the blueprint unit's route is retained.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
