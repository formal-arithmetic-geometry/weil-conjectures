## What changed

Reproved `AlgebraicGeometry.Etale.RawModuleScalarComparison.pullback_unit`
directly from the canonical comparison's definition as an adjunction mate, using
`Equiv.apply_symm_apply`. Removed the private proof import
`import all Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition`.

Preserved every definition, public import, instance and theorem signature, including
`eq_pullback_of_unit` and `kanSheafification_eq_pullback`. Updated the proof docstring
and the second proof step of `def-sbc-raw-module-scalar-pullback-comparison` to describe
the actual proof. The node's upstream attachment and mathematical dependencies stay.

Change record: `coord/changes/C2-raw-scalar-unit-direct.md`.

## Proved and sorry left

The current item has 0 sorries. Holes closed: 0 of 0. Holes added: 0. Split off: 0.
Sorries left: none. This delivery prunes a proof dependency; it makes no hole-count claim.

The direct proof of `pullback_unit` and the retained proofs of `eq_pullback_of_unit`
and `kanSheafification_eq_pullback` compiled through the required `lcompile.py`,
exit code 0, with no diagnostics (reported compile time 14.9 seconds).
The final delivery runs the axiom probes and preflight.

The direct proof uses only the adjunction Hom equivalence and the existing canonical
mate definition. It adds no nonzero, nonempty, finiteness or geometric hypotheses;
zero rings, zero sheaves, empty schemes and identity arrows remain covered.

## No longer needed

Removed `import all Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition` from
the assigned module. Its private `AlgebraicGeometry.Etale.scalar_unit` helper is no
longer used: the unit equation follows immediately from the upstream mate definition.
This removes precisely `Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition`
from the item's transitive import closure. The assigned proof does not use
`rawModuleScalar_sheaf_composition` or its node
`lem-sbc-raw-scalar-sheaf-composition`.

The composition node still has DAG consumers in the coefficient-unshifted,
source-class-formula and source-square arguments, so neither that node nor its
module is withdrawn. No other import, module, node or blueprint unit step is pruned.
The assigned module remains available to all current and quarantined consumers.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a repeatedly split obligation. The current source instead
contains P2's canonical-construction migration and B4's three complete characterization
proofs, already landed. There is no remaining sorry or open C2 return for this item.
Repeating their work would be a no-op. This delivery removes the unnecessary private
proof dependency added by B4 while retaining all its checked characterization results.

Mathlib searches were run through `msearch.py`: LeanFinder found the adjunction
Hom-equivalence formulas, Loogle found `Equiv.apply_symm_apply`, and grep found
applications of the equivalence cancellation law. Reading the upstream coefficient
comparison definition supplies the complete shorter argument.

No statement or definition is repaired or weakened, and no arbitrary data is chosen.
No source-library module is edited. There are no new nodes or forced adaptations.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
