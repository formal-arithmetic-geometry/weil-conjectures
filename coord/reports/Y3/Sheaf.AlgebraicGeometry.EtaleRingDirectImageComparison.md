## What changed

Replaced the hole in `AlgebraicGeometry.etaleRingDirectImageComparison` with an
explicit sectionwise construction of ring homomorphisms, a proof of invertibility
by reflection through `sheafForget`, and a proof of naturality using the three
forgetful identifications. The statement and existing public imports are unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.EtaleRingDirectImageOperations`.
Updated the target node's proof route and added a node for the operation calculation.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.etaleRingDirectImageComparison`
(node `lem-weil-pbc-etale-ring-direct-image-comparison`). Added one hole:
`AlgebraicGeometry.etaleRingDirectImageOperations`
(node `lem-weil-pbc-etale-ring-direct-image-operations`). This is a decomposition,
with net zero holes closed, not a complete proof of the mathematical comparison.
The new hole states four sectionwise operation equations only. The target now
constructs the ring maps, proves restriction naturality, proves invertibility,
and proves naturality in the internal ring. No choice from an existence theorem
is used to define any data: the ring maps are constructed explicitly.

Both modules compile locally. Edge cases: zero rings and empty site categories
require no extra hypotheses; the operation calculation uses terminal singleton
sections only. No nonzero-ring or point assumptions are introduced.

## No longer needed

The proof removes the proof-only imports
`Sheaf.CategoryTheory.Adjunction.LiftedCommRingBranch` and
`Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingCore`; their conclusions
already occur as hypotheses and they remain needed by callers elsewhere. No
whole module is pruned from the targets' closure. The new operation lemma
derives its result from the supplied hypotheses rather than constructing those
functors again.

## Where the brief, the DAG or earlier work was wrong

The two original proof dependencies construct the functors and their operation
formulas, but cannot establish this arbitrary-functor comparison by themselves.
The remaining calculation is now stated precisely as four equations in a new
module. Negation is not required for bundling a RingHom: addition, zero,
multiplication and one suffice. The existing unit route is preserved.

## New nodes

`lem-weil-pbc-etale-ring-direct-image-operations` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-ring-direct-image-operations.json`
states only preservation of addition, zero, multiplication and one by the
prescribed section map. Its module is
`lean/Sheaf/AlgebraicGeometry/EtaleRingDirectImageOperations.lean`.
Its docstring explains transport through the strict inverse identifications,
evaluation of product/terminal comparisons, and substitution in the RF formulas.
No statements or definitions of existing modules changed; no change record or
forced adaptation is needed.

## Second reading by Y3

1. I compared both delivered modules with the repository versions and checked
all existing declaration signatures byte for byte. The comparison theorem's
interface is unchanged; the operations theorem is a newly split declaration.
Verdict: pass.

2. I compiled both modules with `lcompile.py --all`. There are no forbidden
commands or hollow definitions, and the only remaining `sorry` is the named
operations theorem documented above. The comparison proof constructs its maps
explicitly and uses `sheafForget` only to reflect isomorphisms and prove
naturality. Scratch `#print axioms` checks show only `propext`,
`Classical.choice`, `Quot.sound`, and the expected `sorryAx` for both theorems.
Verdict: pass.

3. I checked the split-off operations statement against its four sectionwise
equations, its docstring, and its DAG node. It is strictly smaller than the
comparison theorem and introduces no arbitrary witness or extra hypothesis;
zero rings and empty sites are covered. Independent leanfinder, loogle,
grep, and local source searches found no existing matching operation theorem.
Verdict: pass.

4. I checked the proof route and pruning. The route uses the split operation
lemma, then explicit ring-hom construction, reflection, and naturality. The
two former construction imports are no longer used and are recorded above;
the unit route remains unchanged. Verdict: pass.

5. I checked that the DAG proof, `proof_deps`, `proof_origin`, Lean imports,
and report agree, including the new operations node and its module. Verdict:
pass. The new node now records its Lean statement verbatim, including
line breaks.

I changed the new node's statement formatting and the report during this second reading: corrected the removed
import accounting and added this review record.
