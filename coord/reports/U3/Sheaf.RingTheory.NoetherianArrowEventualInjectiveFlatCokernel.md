## What changed

Proved `Module.eventually_injective_flat_cokernel_of_noetherian_local_stages` in
`Sheaf.RingTheory.NoetherianArrowEventualInjectiveFlatCokernel`, preserving its full
signature. The proof follows all five planned steps. It builds the additive target
colimit, transports its scalar action and flatness through the canonical colimit
comparisons, applies `RingTheory.exists_flat_stage`, and propagates flatness with
`Module.flat_of_local_criterion_baseChange` at the zero ideal. It then constructs the
closed-fibre square explicitly and applies `flat_mod_injective` after identifying
residue tensors with maximal-ideal quotients.

Added private proof imports of Mathlib filtered ring colimits, type colimit recognition,
and module structure transfer, and of the already proved
`WeilConjectures.RingTheory.FlatSemilinearEquiv`. Updated the existing DAG node's proof,
proof dependencies, and proof origin to describe these comparisons and the Mathlib
scalar-extension injection. No definitions, statements, source-library files, or
consumer modules changed.

## Proved and sorry left

Closed the single original hole:
`Module.eventually_injective_flat_cokernel_of_noetherian_local_stages`
(node `lem-trf-noetherian-arrow-eventual-injective-flat-cokernel`).
One of one holes closed; zero holes added; zero holes remain in the delivered module;
zero statements split off. No new theorems or axioms were introduced.

Server compilation passed without warnings in 13.6 seconds with the temporary
axiom probe. `#print axioms` reports exactly `propext`, `Classical.choice`, and
`Quot.sound`; in particular no dependency on `sorryAx` remains. The probe was removed
from the delivery source.

## No longer needed

Removed proof import `Mathlib.LinearAlgebra.TensorProduct.Basis`: the field-extension
injection follows directly from `Module.Flat.tensorProduct_mk_injective` and
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. All original mathematical
proof dependencies remain used. No DAG nodes or project modules are withdrawn or
claimed prunable, and the unit route is preserved.

The proof does not need the source-module transition, colimit, or base-change data:
`hm_smul`, `hm_id`, `hm_comp`, `h_stage_arrow`, `hmu_smul`, `hmu_comp`,
`hM_represent`, `hM_equal`, and `hbaseM`. The specified injective source comparisons
already contain the required source information. The elementwise ring-colimit
hypotheses `hR_represent`, `hS_represent`, `hR_equal`, and `hS_equal` are also unneeded:
the supplied categorical colimit witnesses and Mathlib filtered-colimit preservation
suffice. All binders remain verbatim; a theorem-scoped unused-variable linter
setting suppresses warnings for these retained hypotheses.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The DAG's first step described proving
set-colimit preservation manually, while Mathlib already supplies preservation for
these filtered diagrams. The categorical interface of `exists_flat_stage` also needs
the explicit ring and module colimit comparisons; those are now written in Lean.
The basis argument in step 3 is correctly replaced by Mathlib's flat tensor injection.
The zero source fibre and singleton or non-linearly ordered directed index sets are
covered: no nonzero vector or strict-successor index is chosen, and the only index
operation is a common upper bound.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
