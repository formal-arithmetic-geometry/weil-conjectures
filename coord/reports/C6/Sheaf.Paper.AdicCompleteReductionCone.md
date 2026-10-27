## What changed

Reduced `AlgebraicGeometry.Scheme.adicResidue_complete_reduction_cone` using a concrete
adjoint quotient tower and the existing augmented Cech completion reflector. The item
statement and its public imports are unchanged; its new proof imports are
`Sheaf.Paper.AdicResidueCechQuotientCone` and `Sheaf.Paper.AdicResidueCompletionModel`.

`AdicResidueAdjointTower` constructs uniquely normalized scalar adjunctions from the
ordinary tensor adjunction and universal left-derived comparison. It explicitly defines
the successor by reducing the counit and transposing, proves the equation for every
transposed morphism by adjunction naturality, and constructs the unit cone. Its data
choices are unique: the unit determines the entire adjunction. No definition selects an
arbitrary witness from a mere existence theorem.

`AdicResidueCompletionModel` proves finite generation of the actual slice residue
kernel from `flat_and_quotients`, then applies the existing Cech model and reflector
lemmas. The final proof inverts the Cech unit using the original completeness hypothesis,
cancels it in the leg equation, and uses the proved successor transpose identity.

The remaining `AdicResidueCechQuotientCone` comparison takes an arbitrary input, with
no completeness hypothesis, and a genuine augmented Cech model. It compares that
specified completion to the already constructed quotient tower. It does not repackage
the item's hypothesis, and it does not assert or construct the item's scalar adjunctions,
level comparisons, vertex isomorphism, or transpose compatibility.

Validation: all four modules compiled cleanly in sandbox import order via lcompile.py,
with times 25.0, 7.1, 11.1 and 12.1 seconds respectively. The final import cleanup and
source-comment corrections are checked again by deliver3.py. All referenced nodes exist,
proof_deps matches the proof-step uses, and none of the four delivery nodes has a return
path through its dependencies. Edge cases checked in the comparison proof are
J=0 (empty Koszul list, constant tower), J=A (zero completion and quotient tower),
M=0, the zero ring, and the empty scheme. The explicit adjunction construction does
not use Noetherianity or completeness.

## Proved and sorry left

Closed the item's one textual hole:
`AlgebraicGeometry.Scheme.adicResidue_complete_reduction_cone`
(node `lem-sfb-adic-complete-reduction-cone`).

Added one remaining hole:
`AlgebraicGeometry.Scheme.adicResidue_cech_quotient_cone`
(node `lem-sfb-adic-residue-cech-quotient-cone`). Its proof is exactly `by sorry`.
There are no other new holes and no holes in definitions. This is a decomposition,
not a net hole closure: one upper hole closed and one comparison hole added.

The scalar-adjunction uniqueness, successor transpose identity, unit compatibility,
finite generation of the slice kernel, and Cech-model assembly are proved in Lean.

## No longer needed

Removed the unused proof import `Sheaf.CategoryTheory.GeometricModuleConstruction`
from the new adjoint-tower helper after checking its declaration uses. The comparison
module imports `ExtendedCechCompletionModel` directly for its statement; the proved
model-existence helper is a private proof import of the item. No original
public import is removed and no original module is withdrawn. No unit
statement or realized step is bypassed. The original direct proof dependencies move
into the single comparison node where they are genuinely used. In particular,
`adic_constructible_finite_reductions` itself is not invoked: its Noetherian-scheme,
constructible and Tor hypotheses are unavailable here. Only that module's general,
already proved scalar unit and balancing declarations are needed by the tower proof.

The item no longer directly requires the product exactness, strict derived-limit,
localization, or derived-change-of-rings nodes: those remain mathematical dependencies
of the comparison or proved helper nodes, not pruned global modules. The new Cech
reflector is a general tool; the original integral-model unit route remains intact.

## Where the brief, the DAG or earlier work was wrong

The original plan conflated the scalar normalization, construction of a complete-object
cone, and compatibility for every transposed map. The cited finite-reductions theorem
cannot itself supply this cone because it requires constructibility, finite Tor bounds,
and a Noetherian scheme. Its public scalar declarations do supply the required unit and
balancing data. Also Tag 099M is in proetale.tex (lemma-naive-completion), while the
Koszul Cech comparison is algebraization.tex Tag 0A0E. No statement is disputed or
weakened. The source-library boundary is respected: no WeilConjectures module changed.

The generic extended-Cech reflector and resolving-adjunction declarations are tools
from other units, applied without replacing a step of the integral-model unit route.
The maintainer may record these tool uses; this delivery adds no tool_uses approvals.

## New nodes

`lem-sfb-adic-residue-adjoint-tower` records the completely proved normalized scalar
adjunction, explicit successor and transpose identity, with its unit cone.

`lem-sfb-adic-residue-completion-model` records the completely proved residue-kernel
finite generation and Cech-model/complete-unit construction on the slice.

`lem-sfb-adic-residue-cech-quotient-cone` records the sole remaining construction
comparison, including its unit and transition normalization. Its docstring and DAG proof
explain the Noetherian Koszul-to-quotient comparison, exact restriction, and Roos triangle.

Change record: `coord/changes/C6-adic-residue-cone-constructions.md`.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
