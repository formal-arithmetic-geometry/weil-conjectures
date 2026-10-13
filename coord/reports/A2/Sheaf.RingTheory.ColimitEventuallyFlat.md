## What changed

Replaced the sorry in `RingTheory.exists_flat_stage` in
`Sheaf.RingTheory.ColimitEventuallyFlat` by a complete Lean reduction of Stacks 00R6.
The existing statement and all public imports are unchanged. Added a proof-only import of
`Sheaf.RingTheory.ColimitMaximalKernelDescent`; retained the existing proof-only import of
`Sheaf.RingTheory.FlatOfLocalCriterionBaseChange`.

The proof chooses a fixed stage, obtains eventual maximal-ideal kernel vanishing, installs
both scalar towers using the commuting square, and proves flatness of the residue tensor
module by field instances. It restricts the given tensor base-change equivalence to the
later base ring and tensors its inverse with the extended ideal. The pure-tensor formula
uses the given equivalence evaluated at `1 ⊗ x`, and its composition with the descended map
kills the multiplication kernel. Applying `Module.flat_of_local_criterion_baseChange` and
transporting flatness along the restricted equivalence proves the original conclusion.

The kernel descent is isolated in a new module, with a named public theorem, its full
proof in words and a DAG node. Its assumptions omit localization, locality of the structure
and transition maps, locality of the second rings, and tensor base change. Its conclusion
is only kernel vanishing in the later module, not flatness or a repackaging of flatness.
The existing node now records the actual three-step assembly proof; the original steps
1–6 are retained as the new kernel-descent node's proof. The unit and chapter routes stay.

Validation: both delivered modules compile together in import order without warnings.
Scratch Lean checks (not delivered) verify that the pure-tensor specification uniquely
determines the additive map, that all images vanish for a zero target module, and that
the multiplication kernel is zero in the constant flat-module case for finite ideals.
For a field initial stage the maximal ideal is zero, making the descent assertion
vacuous. For a system where a module element dies later, eventual zero equations,
rather than injective coprojections, are used in the proof in words.

## Proved and sorry left

Closed the one original hole: `RingTheory.exists_flat_stage`
(node `lem-weil-pbc-colimit-eventually-flat`). No sorry remains in the item's module.

Added one hole: `RingTheory.exists_stage_maximal_kernel_vanishes`
(node `lem-weil-pbc-colimit-maximal-kernel-descent`) in the new module
`Sheaf.RingTheory.ColimitMaximalKernelDescent`. Its whole proof is `:= by sorry`.
This is a decomposition, with one original hole closed and one strictly intermediate
hole added, not a net reduction of holes. The existing local-criterion theorem remains
an imported dependency; its proof is not changed by this delivery.

## No longer needed

None of the original item's imports is removed. No original dependency is pruned from
the target closure: the original steps 1–6 and their dependencies are now beneath the
new kernel-descent node. The main node's direct proof dependencies are the new descent
node, `lem-weil-pbc-flat-another-variant-local-criterion`,
`lem-weil-pbc-module-over-field-flat`, and `def-weil-pbc-flat-ring-map`.
The other former direct dependencies moved beneath the new node; they were not discarded.
The second reader removed the redundant newly added proof-only imports
`Mathlib.RingTheory.Ideal.Quotient.Basic` and
`Mathlib.LinearAlgebra.Basis.VectorSpace`; the remaining imports supply their declarations
transitively. No original DAG dependency was pruned by this cleanup.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. Existing source-library subalgebra approximation lemmas
are not a shorter route to this arbitrary varying-ring, finite-module statement.
The local criterion is usable after installing the algebra square and its scalar towers;
its still-unproved status is not an obstacle.

LeanSearch returned an internal-server-error/unavailable result for the new lemma;
LeanFinder, Loogle, direct Mathlib and source-library searches, and the blueprint search
were completed. The new node records the unavailable search without a no-match verdict.
The local checkout lacks `literature/stacks-project/algebra.tex`; the official 00R6
text at https://stacks.math.columbia.edu/tag/00R6 was read for this work. The source path
and precise Stacks tag remain those of the parent node.
WANTED: `literature/stacks-project/algebra.tex`, Tag 00R6 and Remark 00M6, for
`lem-weil-pbc-colimit-maximal-kernel-descent` (restore the referenced local literature).

## New nodes

`lem-weil-pbc-colimit-maximal-kernel-descent`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-colimit-maximal-kernel-descent.json`,
realized by `RingTheory.exists_stage_maximal_kernel_vanishes` in
`lean/Sheaf/RingTheory/ColimitMaximalKernelDescent.lean`. It states steps 1–6 of the
parent's proof: eventual vanishing of the maximal-ideal multiplication kernel, without
the localization and tensor base-change hypotheses needed only for the final local
criterion. No definition, existing statement, visibility, or external interface changed;
no change record or forced adaptation is needed.

## Second reading by A2

1. Compared the complete delivered main module with the repository by `diff`. The
   signature of `RingTheory.exists_flat_stage` is byte-for-byte identical, including
   universes, every typeclass and hypothesis, and the conclusion. Its docstring,
   public imports and visibility are unchanged. The only other module is new; no
   existing definition or statement changed and no change record is needed. Pass.
2. Compiled both delivered modules in import order through `lcompile.py`. The only
   hole is the reported public theorem `RingTheory.exists_stage_maximal_kernel_vanishes`;
   there are no definitions, forbidden declarations or unreported holes. Scratch
   `#print axioms` checks on both declarations report exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The main theorem therefore remains
   dependent on the kernel-descent and local-criterion holes: this is a decomposition,
   not an axiom-free proof or a net hole reduction. Pass.
3. Read official Stacks Tags [00R6](https://stacks.math.columbia.edu/tag/00R6),
   [00MO](https://stacks.math.columbia.edu/tag/00MO), and
   [00M6](https://stacks.math.columbia.edu/tag/00M6). Checked the new theorem against
   its node hypothesis by hypothesis: only Noetherianity and finite generation,
   directedness, compatible scalars and flatness of the limit enter kernel descent.
   Local structure maps, local B stages, localization and module base-change
   isomorphisms are needed only in the final local criterion, so their omission is
   justified. In its docstring argument, descend both the ring-kernel equations and
   the tensor equalities before mapping to the extended ideal; injectivity of colimit
   coprojections is never assumed. Finite B_i-generators kill the whole kernel by
   semilinearity. Checked field stages (zero maximal ideal), zero modules, constant
   flat systems, and noninjective transitions. Recompiled the scratch edge-case
   checks, including uniqueness of the specified additive map. Thus the map has
   determined data; no arbitrary witness is used to define an object. Pass.
   Independent LeanFinder search used “Finite generation lets a tensor multiplication
   kernel vanish at one common index in a filtered colimit of modules over changing
   rings”; Loogle used `Module.Flat, "exists"`; direct `rg` searched stage/eventual
   kernels, Tor and flat colimits in Mathlib, source and landed Lean. Read
   `Submodule.exists_fg_of_baseChange_eq_zero` and upstream
   `Module.exists_finset_lTensor_eq_zero`: they use subalgebras of one fixed ring
   and a fixed tensor module, not these arbitrary varying diagrams and modules.
   No duplicate or short replacement found; closing this hole is not a few-minute
   application. It is a strict intermediate kernel claim, not a renamed flatness
   conclusion. Its source, full argument and matching new node are present.
4. Reviewed the main proof top down: nonemptiness selects i; descent supplies j and
   the canonical kernel map; hcomm establishes the two algebra towers; locality
   and hloc supply precisely the 00MO square. The residue tensor module is flat over
   the field A_i/I. Restricting the given equivalence to A_j and tensoring its inverse
   transports the kernel map; he evaluated at 1 proves its pure-tensor formula.
   00MO yields flatness of the tensor module, and `Module.Flat.equiv_iff` transports
   it to N_j. No shorter applicable route found. The records in
   `dag/units/sk-thm-p1.json` are untouched; neither changed node realizes a unit
   statement or step. Checked every old direct proof dependency: all remain either
   in the main node or beneath the new node. None is discarded. Pass.
5. Compared both node records to the Lean and read the original plan. The existing
   node changes only `proof` and `proof_deps`; its three steps describe the actual
   assembly. The new node retains the six kernel-descent steps and their dependency
   union, and includes source, proof origin, search records, creation, blueprint,
   unit/chapter and matching Lean signature. No existing node statement changes.
   The unchanged document proof origin still describes the Stacks route. Pass.

Changed only the main module's two redundant newly added imports and this report.
Confirmed by compilation that both `Mathlib.RingTheory.Ideal.Quotient.Basic` and
`Mathlib.LinearAlgebra.Basis.VectorSpace` are supplied by the remaining imports.
The mathematical proof and new statement needed no repair.
