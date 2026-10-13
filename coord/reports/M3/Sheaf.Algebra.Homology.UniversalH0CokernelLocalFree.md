## What changed

Replaced the sorry in `CochainComplex.universalH0_cokernel_local_free` by a complete
Lean proof from one new matrix normal-form statement. The original theorem's
signature, universe, visibility and docstring are unchanged. Added proof-only
imports of `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` and
`Sheaf.Algebra.Homology.ResidueKernelUnitMinor`.

The private proved helper `h0_kernel_test` identifies H0 with the kernel after
scalar extension using Mathlib's short-complex cycles and homology isomorphisms.
The private proved helper `kernel_equiv_ring_forces_zero` proves the annihilator
argument in coordinates of a free target. The main proof separately tests H0
over the residue field and over the prime localization, applies the unit-minor
step using only the residue test, then eliminates the residual differential and
transports freeness across the quotient equivalences. Updated the parent node's
proof and dependency list to match this implementation. No definitions or
existing statements were changed; no forced adaptations were needed.

Both modules compile cleanly with the required local wrapper. The preserved
unit record `sk-prop-av-cube` has no realized nodes in this checkout; this proof
follows the parent's existing unit-minor route and changes no unit statement or
step. The source argument was checked against
[Stacks 00O0](https://stacks.math.columbia.edu/tag/00O0) and
[Stacks 00NX](https://stacks.math.columbia.edu/tag/00NX).

## Proved and sorry left

Closed the sole original hole:
`CochainComplex.universalH0_cokernel_local_free`
(node `new-universal-h0-cokernel-local-free`). There is no sorry in the item's
module, including its two private helpers.

Added one named hole in its own module:
`ModuleCat.residue_kernel_unit_minor`
(node `new-residue-kernel-unit-minor`, module
`Sheaf.Algebra.Homology.ResidueKernelUnitMinor`). Its proof is exactly `by sorry`.
This is a decomposition: one upper hole closed and one lower hole added, net
zero holes. The lower statement is strictly the residue-field matrix step: it
assumes no local-ring kernel test, asserts no free cokernel, and allows a
nonzero residual map. The local-ring test, vanishing proof and free-quotient
transport are actual Lean proofs in the parent module.

## No longer needed

None. No existing import was removed. The former direct dependency
`lem-weil-pbc-finite-projective-prime-local-free` is now a planned dependency of
the residual normal-form node; it is still needed there, so neither it nor
`Sheaf.RingTheory.FiniteProjectivePrimeLocalFree` is claimed as pruned.
No node or module is pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cites finite-projective local freeness but does not
state the residue rank-(n-1) normal form or its kernel/cokernel comparisons.
The new node states precisely that missing first part of the argument. Tag
00O0 is used through its unit-minor calculation; its injectivity conclusion
cannot be applied to the whole differential, whose residue kernel has rank one.

Checked edge cases before stating the new lemma: a zero map with rank-one
source uses the empty identity block; a surjective map with source rank one
larger than the target has C=0; rank-zero source is excluded by the residue
kernel isomorphism, and there are no primes of the zero ring. For a nonzero
nonunit t in a discrete valuation ring, multiplication by t has one-dimensional
residue kernel yet has a nonfree cokernel. The new lemma still applies with
g=t and C=A, showing that it genuinely does not assert the parent's conclusion.
The parent's separate local-ring kernel hypothesis rules out this case.

The generic scalar elimination requires a free target: reduction Z -> Z/2 has
kernel isomorphic to Z and is nonzero, so the freeness hypothesis was kept.
No domain, Noetherian, flat-base-change or nontriviality hypothesis was added.

The blueprint ancestor script returned None for this newly split stage-3 item,
while the existing node records `thm-sc-theorem-of-cube`; the new node inherits
that existing provenance and prepends this item to its via list. Blueprint
searches for "unit minor" and "kernel" found no duplicate statement.

## New nodes

`new-residue-kernel-unit-minor` states the residue-field unit-minor normal form
for a finite projective linear map at a prime, preserving the localized kernel
and cokernel. Its complete proof in words gives the explicit block operations,
including the empty-minor case. It follows Stacks 00O0/00NX and the parent's
first proof step. LeanFinder, Loogle and Mathlib/repository grep found generic
basis-lifting and split-injection ingredients but no exact statement;
`FiniteFreeMapResidueLocalizationStrong` treats residue-injective maps instead.
LeanSearch returned HTTP 500 and is recorded as unavailable. All service
queries ran through `msearch.py` and their logged results are in the node.
There are no change records, because no existing interface changed.

## Second reading by M3

1. Compared both delivered modules with the repository versions. The existing theorem signature and all existing declarations are unchanged byte for byte; the only new declaration is the explicitly split-off residue unit-minor theorem.

2. Compiled both modules with `lcompile.py --all`. There are no errors, no forbidden declarations, and no `sorry` in the item module or definitions. The sole remaining `sorry` is the named theorem `ModuleCat.residue_kernel_unit_minor`, with its matching node; its axioms are therefore limited to the documented `sorryAx` until that node is proved.

3. Reviewed the split-off statement against the edge cases in the preceding report and the source argument. It is strictly weaker than the parent conclusion, retaining an arbitrary residual map g and asserting only the kernel and quotient equivalences. No duplicate declaration was found in Mathlib or the repository.

4. Checked the proof route from the target downward. The parent uses the new residue unit-minor result, then proves the local annihilator calculation and free quotient transport directly. The unit `sk-prop-av-cube` route and statement are unchanged. No import can be removed without losing declarations used by the proof; the two added imports are proof-only.

5. Checked that the DAG proof steps and `proof_deps` match the Lean proof, and that the new node has the required source, proof, searches, Lean record, chapter, and unit fields. The report records the one decomposition and no pruned nodes.

Changed only this report section; no Lean statements, definitions, imports, or DAG statements were altered during second reading.

Additional independent checks: an appended `#print axioms` scratch copy compiled
successfully. Both private helpers use exactly `propext`, `Classical.choice`,
and `Quot.sound`; the parent theorem and the split-off theorem additionally
use `sorryAx`, as expected. Independent LeanFinder search for Gaussian
elimination over a local ring returned PID Smith normal form, transvections,
and `Module.Basis.ofSplitExact`, not this statement. Loogle confirmed that
`Module.Basis.ofSplitExact` requires an already split exact sequence and does
not supply the unit-minor reduction. Repository grep for residue kernels and
unit minors found the related universal-H0 callers, with no usable duplicate.
These checks did not require any Lean or node changes.
