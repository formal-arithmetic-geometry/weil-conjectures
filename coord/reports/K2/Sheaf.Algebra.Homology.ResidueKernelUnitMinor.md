## What changed
The existing declaration `ModuleCat.residue_kernel_unit_minor` keeps its signature,
visibility and docstring byte for byte. Its proof now obtains an actual diagonal
normal form, applies a proved computation of that form's kernel and cokernel,
and composes with the localization-of-cokernel comparison.

The draft's kernel-only existence statement was replaced, before delivery, by
`ModuleCat.residue_kernel_unit_minor_normal_form` in
`Sheaf.Algebra.Homology.ResidueKernelUnitMinorKernel`. It records the source and
target equivalences and their commuting equation. The draft's false quotient
statement was replaced by the proved generic theorem
`ModuleCat.residue_kernel_unit_minor_quotient` in
`Sheaf.Algebra.Homology.ResidueKernelUnitMinorQuotient`.
`Sheaf.Algebra.Homology.ResidueKernelLocalizedCokernel` states the remaining
localization/bundled-scalar-extension comparison separately. All three imports
in the existing module are proof-only imports. No existing public import changed.

## Proved and sorry left
Closed one pre-existing hole: `ModuleCat.residue_kernel_unit_minor`.
There is no sorry in the item's module. Its proof depends on these two added holes:

- `ModuleCat.residue_kernel_unit_minor_normal_form`
  (`new-residue-kernel-unit-minor-kernel`): matrix diagonalization only.
- `ModuleCat.residue_kernel_localized_cokernel`
  (`new-residue-kernel-localized-cokernel`): localization of a range quotient and
  conversion to the bundled scalar-extension object only.

The new theorem `ModuleCat.residue_kernel_unit_minor_quotient`
(`new-residue-kernel-unit-minor-quotient`) is proved without sorry and uses only
standard axioms. It proves both the kernel and cokernel computations for an
actual diagonal normal form, with no local-ring or finiteness assumptions.

This is a decomposition: one old hole closed, two new holes added, net -1 in the
item's import closure. It is not claimed as a sorry-free proof or net progress.
The unlanded draft statements that were removed are not counted as closed holes.
Both remaining holes are named public theorems with complete sourced docstring
proofs and matching nodes. No definition or witness-selecting definition is added.

## No longer needed
The old proof dependency `lem-weil-pbc-finite-projective-prime-local-free` is no
longer needed by this route: local freeness can be obtained directly over R_p
from Mathlib's `Module.free_of_flat_of_isLocalRing` after scalar extension.
No existing library import was removed and no whole-library module pruning is
claimed. Removed the unused public import
`Mathlib.Algebra.Module.LocalizedModule.Basic` from the new normal-form module.
The new quotient computation needs only ModuleCat/quotient definitions publicly;
`Mathlib.LinearAlgebra.Isomorphisms` is a proof-only import.

## Where the brief, the DAG or earlier work was wrong
STATEMENT-DISPUTED (withdrawn unlanded draft): the former
`residue_kernel_unit_minor_quotient` inferred a cokernel equivalence from an
arbitrary kernel equivalence. This is false even if C is free. Over a field k,
take X=k, Y=0 and f=0. Its residue kernel is k. Set C=k and g=0. Then both
kernels are k, while the localized cokernel of f is 0 and C/range g is k.
Kernel identification does not constrain the unused target coordinates.
The draft docstring silently assumed that C and g came from the same matrix
normal form; its signature carried no such condition. That statement and its
unsound proof step have been removed, not weakened into an existing interface.
The report's earlier claim that splitting into those two components was required
was unsupported. The repaired split retains the commuting equation needed for
the first-isomorphism argument and actually proves that argument.

Searches found the ordinary Mathlib localization/quotient and range identities,
not an exact declaration for the bundled ModuleCat comparison. An attempted
proof of that comparison reached the conversion between the canonical tensor
scalar instances and the instances on `extendScalars` but did not close that
conversion. Its mathematical proof is recorded in the docstring; it remains a
named hole, not a partial proof with embedded sorry. LeanSearch returned Internal
Server Error; real LeanFinder, Loogle and grep searches are recorded instead.
The normal form is the rank-(n-1) adaptation of the unit-minor argument in
[Stacks 00O0](https://stacks.math.columbia.edu/tag/00O0), with local freeness from
[Stacks 00NX](https://stacks.math.columbia.edu/tag/00NX), not a verbatim statement
of either tag.

## New nodes
`new-residue-kernel-unit-minor-kernel` states only the matrix portion: U,C,g,
free C and two equivalences conjugating f to diag(id,g). Its proof treats the
empty block when the source rank is one. It neither assumes nor concludes the
kernel/cokernel equivalences of the original item.

`new-residue-kernel-unit-minor-quotient` records the fully proved kernel and
cokernel computation for those two equivalences and their commuting equation.
Projection to C/range g is surjective with kernel exactly range f; Mathlib's
`LinearMap.quotKerEquivOfSurjective` finishes it.

`new-residue-kernel-localized-cokernel` records the generic comparison between
localizing Y/range f and quotienting the bundled scalar extension by its range.
It drops all rank, finiteness and projectivity assumptions and uses the actual
Mathlib localization/range/quotient APIs. No change record is needed: only
previously unlanded new statements were replaced and every existing signature
is unchanged.

## Second reading by K2
1. Compared the delivered item with the repository by diff and compared its
   declaration header byte for byte: PASS. No existing signature, visibility,
   definition or docstring changed. Every other delivered module is new.
2. Compiled all four modules locally through lcompile.py in import order: PASS.
   Scanned every source for forbidden declarations and embedded holes: PASS.
   Scratch-copy #print axioms checks show only the standard axioms on the generic
   diagonal computation; the two named holes and the target depending on them
   also show sorryAx, exactly as expected for this decomposition.
3. Tested the new statements on zero maps over fields, zero target, empty U,
   source rank one, and nonzero residual g. The original quotient component
   FAILED by the counterexample above and was replaced by a fully proved
   statement with the necessary diagonal equation. The repaired statements are
   true, needed and strict portions of the original argument. They have complete
   docstrings and nodes. Independent searches with diagonal/conjugation and
   localization/range terminology found usable Mathlib ingredients but no exact
   existing statement for the remaining bundled comparisons.
4. Reviewed the route from the item's original hole downwards. The reduction
   proves the kernel and quotient computations rather than renaming the target.
   Imports are restricted to statement needs and actual proof needs. The old
   principal-open freeness dependency is explicitly listed as no longer needed.
   The theorem-of-cube unit route is unchanged; this is a tool calculation below
   the unit level. The existing unit's empty realized arrays are pre-existing;
   this delivery does not purport to fill that unit's binding or bypass a step.
5. Reviewed all delivered nodes against their Lean signatures and proof bodies:
   PASS after repair. Existing-node proof_deps is exactly the three components
   used by the proof. New nodes have verbatim signatures, full hypotheses,
   sourced stepwise proofs, real search records and the inherited chapter/unit.

Second reading changed the false quotient split into a proved diagonal
kernel/cokernel computation, strengthened the unlanded normal-form component to
carry both conjugating equivalences, isolated the localization comparison as a
strict named component, removed an unused new-module import, corrected all node
statements and proof plans, and replaced the misleading progress report with
explicit hole accounting. No original statement was changed.
