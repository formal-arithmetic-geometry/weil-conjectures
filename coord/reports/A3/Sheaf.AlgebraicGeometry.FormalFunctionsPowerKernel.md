## What changed

Proved the unchanged declaration `AlgebraicGeometry.formalFunctions_power_le_ker` by
`Submodule.smul_le`, the existing proved `moduleCohomology_scalar_endomorphism`, and
linearity of the reduction map. The proof applies scalar compatibility to the zero
endomorphism of the quotient, once with the image of a in global functions and once
with zero. These two computations of the same cohomology map show that the image of a
annihilates the reduced class. Restriction of scalars and `map_smul` finish the inclusion.

Added two proof-only imports: `FormalModuleQuotientScalarZero` and
`ModuleCohomologyScalarEndomorphism`. Added the new module
`Sheaf.AlgebraicGeometry.FormalModuleQuotientScalarZero`, which states the remaining
sheaf-section annihilation step. Updated the existing target node's proof and proof
dependencies to match this reduction. No existing signature, docstring, definition,
visibility, or public import was changed. No change record is required.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.formalFunctions_power_le_ker`
(node `lem-weil-pbc-formal-functions-power-kernel`), the only original hole in the item.

Hole added and still open: `AlgebraicGeometry.formalModuleQuotient_scalar_zero`
(node `lem-weil-pbc-formal-module-quotient-scalar-zero`), in the new module.
Its whole proof is `:= by sorry`; its docstring contains the source and complete stalk
argument. No other delivered declaration contains a hole, and no data definition was added.

This is a decomposition, not a completed proof: one original hole closed, one strictly
sheaf-level hole added, net zero holes. The target still depends on `sorryAx` through that
lemma. The first worker's equivalent cohomology restatement
`formalFunctions_scalar_mem_kernel` and its proposed module/node were removed from the
sandbox and are not delivered.

## No longer needed

No original import or module is pruned. Both added proof-only imports are used.
The old direct proof dependency `def-nagata-extended-ideal` is replaced by the new
sheaf-section annihilation node; it remains a statement dependency of the target and
an indirect proof dependency through the new lemma, so its module cannot be pruned.
Every other old proof dependency remains directly used: the coherent formal quotient,
module cohomology, and scalar-endomorphism compatibility.

The rejected new `FormalFunctionsPowerKernelScalar` module and
`lem-weil-pbc-formal-functions-power-kernel-scalar` node never belonged to the repository.
Removing them is a review repair, not a library-pruning count.

## Where the brief, the DAG or earlier work was wrong

The first worker's scalar kernel-membership theorem was mathematically equivalent to
the original inclusion via `Submodule.smul_le`. Its proof merely reformulated the whole
item rather than isolating a proper part of the argument. The earlier report's claim
that this was a strictly simpler intermediate statement was incorrect. Replaced it
with annihilation of quotient-sheaf sections, and explicitly proved the passage to
cohomology and then to the kernel inclusion in the item's own module.

The first worker also failed to deliver the modified existing target node; this
reading adds its corrected proof and proof_deps. The scalar compatibility node is
already proved and is used without modification. Its axiom print has only the three
standard axioms. Neither the old nor the repaired proof changes any unit-level route.

## New nodes

`lem-weil-pbc-formal-module-quotient-scalar-zero` states that every a in I^n kills every
section of F/J^nF, with the same base-to-global-sections ring map as the original item.
It has no cohomological degree or class and isolates only the sheaf-level annihilation
step. The proof passes to stalks, identifies the quotient with F_z/(J_z^n F_z), uses
ideal-power membership, and returns to sections via zero germs. The n=0 case is the
zero quotient. Its node contains the exact Lean signature, the original chapter/unit,
ancestry, proof dependencies, and recorded searches. No change records were added.

Sources checked directly: [Stacks 02OC](https://stacks.math.columbia.edu/tag/02OC),
[Stacks 01AG](https://stacks.math.columbia.edu/tag/01AG), and
[Stacks 01CB](https://stacks.math.columbia.edu/tag/01CB).

## Second reading by A3

1. Compared the item's full file with the repository using `diff -u`. Only its two
   proof-only imports and proof body differ; the existing theorem signature is byte for
   byte unchanged. The other delivered module is new and contains no definitions.
   Verdict: pass after repair; no accidental interface or target change.
2. Compiled both modules in import order with `lcompile.py --all`, without errors or
   warnings. Compiled a scratch copy with `#print axioms` for the target, the new lemma,
   and scalar compatibility. The first two use only `propext`, `Classical.choice`,
   `Quot.sound`, and the permitted `sorryAx` from the open sheaf lemma; scalar
   compatibility uses only the three standard axioms. Scanned the delivered sources:
   one named theorem has `sorry`, no forbidden declarations, no hollow definition.
   Verdict: pass as a decomposition with one reported open lemma.
3. Rejected the equivalent scalar cohomology statement and removed its module/node.
   Checked the replacement at n=0, I=0 (including n=0), I=top, F=0, and empty X.
   The quotient stalk argument proves its stated generality without extra hypotheses.
   Searched using leanfinder, loogle, leansearch and grep with quotient-section and
   annihilation terminology, and searched both library roots. Leansearch was unavailable;
   the other searches found ring-module quotient facts but no existing theorem closing
   the sheaf statement. Read the existing ideal-product-stalk theorem; it supplies the
   quotient identification but not the entire extended-ideal/section argument.
   Verdict: the remaining statement is true, needed, and strictly a part of the proof.
4. Read downward from the target. The real reduction now uses the existing proved
   scalar-compatibility theorem on the quotient; no duplicated scalar endomorphism or
   witness chosen from an unproved existence theorem is introduced. All retained
   imports support the interface, and both new proof imports are needed. Listed the
   only displaced old direct proof dependency above. Read `dag/units/sk-thm-p1.json`:
   the target is below its realized nodes, and no realized statement or step is bypassed.
   Verdict: pass; no original module is pruned.
5. Read both delivered nodes and their Lean declarations. The target's proof steps and
   proof_deps match the two scalar computations and linearity. The new node's signature
   matches its theorem, its proof_deps equal its step uses, and it has its source,
   natural-language proof, three search kinds, provenance, ancestry and Lean record.
   Existing node fields outside stage-3 ownership are unchanged.
   Verdict: pass after repairing the missing target-node update.

Second reading changed: replaced the equivalent cohomology split with the quotient-sheaf
section lemma; wrote the explicit cohomology/linearity reduction; corrected the DAG,
source proof, search records, and report. Existing mathematical interfaces remain unchanged.
