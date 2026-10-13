## What changed

Proved `Algebra.truncated_section_conormal_residue_kernel_comap` in
`Sheaf.AlgebraicGeometry.TruncatedSectionConormalResidueKernel`.
All existing signatures and public imports are unchanged. Added the proof-only import
`Mathlib.RingTheory.Smooth.Kaehler`.

Three fully proved private helpers compute the truncated kernel, prove it square zero,
and construct its canonical linear map to the conormal residue quotient using the
explicit Artin–Rees containment. Mathlib's section derivation is composed with this map.
The universal property of Kähler differentials and tensor base change then gives a map
whose composite with `P.cotangentComplex` is the residue quotient projection.
Its linearity makes it kill the maximal-ideal multiple of the cotangent space.
Updated both item nodes to record this route; the elementwise proof remains unchanged.

Compilation through `lcompile.py` is clean, with no warnings and no `sorry`.
The derivation construction is the one in Stacks Tag 02HP, and the truncated-kernel
calculation is from Tag 02HT, both read online. No definition or statement was changed.

## Proved and sorry left

Closed the sole original hole:
`Algebra.truncated_section_conormal_residue_kernel_comap`
(node `lem-weil-pbc-truncated-section-conormal-residue-kernel-comap`).
`Algebra.truncated_section_conormal_residue_kernel` was already proved from this theorem
and now also has no remaining sorry dependency.

Holes closed: 1. Holes added: 0. Sorries left: none. This is a proof, not a decomposition.
The new private helpers `truncated_factor_ker`, `truncated_factor_ker_sq`, and
`truncated_kernel_to_residue_conormal` are all fully proved.

## No longer needed

The proof does not need node `lem-weil-pbc-kahler-differentials-mod-power-ideal` or module
`Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal`. Its underlying node
`lem-weil-pbc-kahler-differentials-mod-power-ideal-bijective` and module
`Sheaf.RingTheory.KaehlerDifferentialsModPowerIdealCore` are also not needed by this route.
Neither module is imported. There were no proof imports in the starting module to remove;
`Mathlib.LinearAlgebra.Quotient.Basic` and `Mathlib.RingTheory.LocalRing.RingHom.Basic`
were tested during development and removed as redundant.

The two differential power comparisons, the intermediate ring C/J^2, and the tensor
cancellation identifications in the original plan are bypassed below the unit level.
The square-zero-section node is retained: the proof uses Mathlib's derivation construction
underlying its conormal retraction. The Kähler and base-change definition nodes remain used.
No claim is made that the pruned modules are unreachable from other project items.

For completeness, the elementwise node no longer directly cites
`lem-weil-pbc-square-zero-section-conormal-retraction`,
`def-weil-module-base-change`, or `def-weil-pbc-kahler-differentials`:
these three dependencies moved to its structural comap dependency and remain used
transitively. Only the differential-mod-power comparison is pruned from the old
proof-dependency union.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but longer than necessary: the section
provides a detecting derivation directly, so no differential comparison is required.
The bound `2 ≤ N` is not needed for this argument once the explicit containment hAR is
given; its binder is retained unchanged. The edge cases J=0 and N=2 are covered without
case assumptions by the same quotient construction.

The earlier comap reduction transferred the entire remaining assertion into an equivalent
submodule inclusion. This delivery supplies the actual square-zero and Artin–Rees proof.
No interface changes, forced adaptations, or new sorry nodes are needed.


## Second reading by C3

1. Compared the sole delivered Lean module with the repository using `diff`, and
   checked both existing theorem signatures byte for byte through `:= by`.
   Verdict: unchanged statements, visibility, definitions and public imports;
   the added Smooth.Kaehler import is correctly proof-only. No change record is needed.
2. Compiled the delivered module with `lcompile.py`: clean, no warnings.
   Compiled a scratch copy with `#print axioms` for both public theorems and all
   three private helpers: each uses only `propext`, `Classical.choice`, `Quot.sound`.
   There are no sorries, forbidden declarations, hollow definitions, or objects
   chosen from unproved existence. The map l is explicitly built via liftQ and
   the quotient-kernel equivalence; its existence proof is fully proved.
3. No statements were split off and no new public statements or nodes were added.
   Read all three private helpers: the kernel image and square-zero calculations
   are direct quotient-ideal identities; the descent map kills J^2 and the
   Artin–Rees intersection separately. For J=0 the kernel and source vanish;
   N=2 needs no extra case or positive-exponent comparison. Checked Mathlib's
   section derivation definition and searched it through Loogle; the proof uses
   that existing construction. Local searches of Sheaf, upstream geometry and
   Mathlib cotangent declarations found no shorter theorem supplying this residue
   comparison. Verdict: genuine proof, zero decomposition holes.
4. Read the proof from the public comparison downward: the detecting derivation
   and its linear extension directly give the residue projection identity.
   The public imports serve statement types, and the sole new import supplies
   the section derivation. Read `dag/units/sk-thm-p1.json` and its `realized`
   statement and steps: neither item node realizes a fixed unit step, and the
   changed route is below the unit level. Verdict: route preserved and pruning
   justified. Clarified the report's complete old-dependency accounting: the
   three retained concepts moved from the elementwise node to the comap node.
5. Compared both delivered JSON nodes with their originals: only `proof`,
   `proof_deps`, `proof_origin` differ. Read their dependency records and checked
   that each proof-dependency list is the union of its steps' uses. The structural
   node explicitly records using the derivation construction underlying the
   square-zero retraction, rather than claiming to apply its retraction theorem.
   The elementwise node records its unchanged application of the structural
   theorem. Verdict: nodes agree with the Lean; no new-node requirements apply.

Second reading changed only this review report and the dependency-accounting
clarification above. No Lean or DAG repair was necessary.
