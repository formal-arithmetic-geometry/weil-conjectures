## What changed

Replaced the rejected data/compatibility split with the genuine invertible-pivot step
`ModuleCat.residue_kernel_unit_minor_pivot` in the new module
`Sheaf.Algebra.Homology.ResidueKernelUnitMinorPivot`. Its conclusion constrains only the
leading square block, leaving all off-diagonal blocks unrestricted.

The core module now proves Gaussian elimination in the private theorem `normalize_pivot`.
For the block map F(u,a)=(B(u)+b(a),c(u)+d(a)), it explicitly constructs source and target
automorphisms and their inverses and sets g=d-cB⁻¹b. Cancellation proves the full
normal-form equation. The core theorem composes those automorphisms with the pivot coordinates.
The core and pivot compile locally; the core compiles without warnings.
An isolated compiler check also validates the complete adapted caller application, given
the same free-module witnesses supplied by its unchanged base-change dependency.

Restored the missing finite-generation hypotheses on the two scalar-extended modules.
The DAG already states finite free; only the old Lean signature dropped finiteness.
The only caller, `Sheaf.Algebra.Homology.ResidueKernelUnitMinorKernel`, has an unchanged
signature and a forced proof adaptation supplying finite scalar-extension instances.
The change record is `coord/changes/residue-kernel-unit-minor-finiteness.md`.

Added a proof-only pivot import to the core and a public Mathlib finiteness import required
by the corrected signature. Added only a proof import of tensor-product finiteness to the caller.
No target, definition, universe, or other downstream statement changes.

## Proved and sorry left

Closed the original core hole `ModuleCat.residue_kernel_unit_minor_matrix_core`
(node `new-residue-kernel-unit-minor-matrix-core`) for its corrected finite-free statement,
by a complete Lean proof of Gaussian elimination from the invertible-pivot step.
The private helper `normalize_pivot` is fully proved and uses only standard axioms.

One new hole remains: `ModuleCat.residue_kernel_unit_minor_pivot`
(node `new-residue-kernel-unit-minor-pivot`). It isolates choosing finite bases,
residue rank-nullity, finding a nonzero minor, lifting its determinant to a unit,
and the coordinate permutations. Its whole proof is `by sorry`, with a complete
natural-language proof and the zero-size-minor edge case in its docstring and DAG node.

This is a decomposition, not a net reduction in holes: one closed, one added.
The old false compatibility and vacuous data holes are deleted from the earlier sandbox attempt;
neither was landed, imported by this proof, or counted as a new library hole.
No sorry is added inside a definition or private helper. The adapted caller has no textual sorry.

## No longer needed

Removed the earlier attempt's imports and deleted its proposed modules/nodes:
- `Sheaf.Algebra.Homology.ResidueKernelUnitMinorMatrixData`,
  `new-residue-kernel-unit-minor-matrix-data`;
- `Sheaf.Algebra.Homology.ResidueKernelUnitMinorMatrixCompatibility`,
  `new-residue-kernel-unit-minor-matrix-compatibility`.

The former placeholder and false universal compatibility claim are not needed.
The original core had no proof dependency imports or planned dependency nodes.
The unused public import `Mathlib.RingTheory.Localization.AtPrime.Basic` was removed;
the unit's route is preserved.
The new pivot module and its import are used by the actual proof.

## Where the brief, the DAG or earlier work was wrong

The earlier compatibility split quantified over arbitrary coordinates and g and was false.
It is not retained or used. The data split ended in True and did not construct a usable pivot.

The core's Lean signature omitted finite generation, despite its DAG and cited
[Stacks Tag 00O0](https://stacks.math.columbia.edu/tag/00O0) argument requiring finite projective
modules. [Tag 00NX](https://stacks.math.columbia.edu/tag/00NX) also explicitly retains finiteness.
The uncorrected signature is false, not merely difficult: over A=k[t]_(t), take
F=⊕ A e_n and T(e_n)=e_n-t e_{n+1}. The map A×F→F, (a,x)↦T(x), has one-dimensional
residue kernel. T is injective and its cokernel is the nonzero t-divisible module A[1/t].
The asserted normal form would force g=0, since its kernel contains a nonzero element
and its target C is free over a domain. It would therefore make A[1/t] free, impossible
because multiplication by the nonunit t cannot be surjective on a nonzero free module.
The detailed correction and unchanged-caller justification are in the change record.

The local published build currently lacks
`Sheaf.Algebra.Homology.ResidueKernelUnitMinorBaseChangeFree.olean`, so the adapted caller's
compile cannot get past its unchanged dependency import. This dependency is in source
and is also an independently reviewed H2 delivery. The worker does not rebuild or fabricate
a missing shared-library dependency. The full dry run must await a usable published snapshot.

## New nodes

`new-residue-kernel-unit-minor-pivot`: the raw invertible leading block, strictly before
the Gaussian elimination proved here. Unlike the rejected compatibility split it
provides coordinates with an actual relation to f. Unlike a restatement of the core
it does not assert a residual g or any diagonal normal-form equation.
Finite source rank one uses U=0 and the empty minor; zero target is allowed when the
source rank is one. Source rank zero cannot satisfy the kernel hypothesis. Full residue
row rank permits C=0. These cases show the split has no hidden positive-rank assumption.

Change record: `coord/changes/residue-kernel-unit-minor-finiteness.md`.

## Forced adaptations

`Sheaf.Algebra.Homology.ResidueKernelUnitMinorKernel` is unclaimed.
Its only changed lines are the proof-only import `Mathlib.RingTheory.TensorProduct.Finite`,
registering the existing hfX,hfY as local instances, and passing the two finite scalar-extension
witnesses to the core. Each witness exposes extendScalars and uses the algebra
(algebraMap R A).toAlgebra, matching its Module.compHom action before applying finite base change. Its original call would pass the prime ideal in the position of the
new finite hypothesis; its declaration signature and visibility are unchanged.

The full original-versus-adapted compiler comparison is currently prevented by the missing
published BaseChangeFree object file. The actual caller compile reports:
```
error: object file for Sheaf.Algebra.Homology.ResidueKernelUnitMinorBaseChangeFree does not exist
```
The restoration of those published artifacts is needed before the delivery tool can establish
and the second reader can independently check the forced adaptation.

The isolated check `scratchpad/lean/Sheaf/Algebra/Homology/CallerFiniteArgumentsCheck.lean`
compiles without warnings with exactly the adapted call and finite-instance proofs; it takes
the free witnesses as hypotheses instead of importing the unavailable dependency. This is only
a local check, not a replacement declaration or a delivery file.

The required `deliver3.py H2 Sheaf.Algebra.Homology.ResidueKernelUnitMinorMatrixCore --no-push`
was run. It compiled Pivot and MatrixCore, then stopped at the missing published dependency
object file in Kernel. It did not print OK and nothing was pushed. Thus this sandbox is a
completed mathematical decomposition awaiting compiled-library publication, not READY.

Retry audit (2026-10-13 19:39 UTC): the dry run again compiled Pivot (2.0 s)
and MatrixCore (3.1 s), then failed on the same missing published BaseChangeFree object.
The isolated finite-argument caller check was rerun through lcompile.py and compiled
without warnings (18.8 s). The downstream declaration-use scan confirms only the core
itself and Kernel mention the changed declaration; no additional caller requires adaptation.
The existing Gaussian elimination formulas and pivot edge cases were checked again.
No repository, shared build, launcher tool, or unrelated module was changed. The missing
published dependency must be restored by the build publication process; no local copy
of its source was substituted or included in this delivery. Nothing has been pushed.

Final retry (2026-10-14): all four sandbox modules compile locally after seeding the missing BaseChangeFree artifact in the sandbox overlay. The delivery checker then reaches forced-adaptation validation but cannot compile the unchanged caller against the baseline because the published build lacks the changing MatrixCore/BaseChangeFree object files; temporary copies are removed by the shared build refresh. A standard unwrapped dry run additionally reports the launcher import-source inventory bug for Mathlib imports. No source proof changes were needed.


Current retry audit (2026-10-14, after the previous worker's BLOCKED result):
The standard, unmodified dry run now passes import-source inventory and compiles the
three delivered modules, but stops in deliver3.py's forced_adaptations baseline check:
```
FAILED: original Sheaf.Algebra.Homology.ResidueKernelUnitMinorKernel already fails
against the compiled baseline; cannot attribute its failure to your change:
error: object file '/home/ubuntu/weil-lean/.lake/build/lib/lean/Sheaf/Algebra/Homology/ResidueKernelUnitMinorMatrixCore.olean'
of module Sheaf.Algebra.Homology.ResidueKernelUnitMinorMatrixCore does not exist
```
A separate `lcompile.py --all` run compiled Pivot (1.9 s), MatrixCore (2.9 s), and
Kernel (2.5 s), with no warnings or errors, using the inherited sandbox overlay.
The declaration-use search still finds only MatrixCore and Kernel as users of the
corrected theorem. The explicit elimination formulas and the pivot's rank-zero,
rank-one, and zero-complement edge cases remain valid. No Lean or node changes were
needed in this retry. No compiled artifacts were seeded or copied in this retry,
and no tool or shared-build file was changed. In particular the earlier report's
import-source inventory failure is no longer reproduced; the missing baseline
MatrixCore object is the current blocking failure. Restoring that published object
(and any missing baseline dependencies) belongs to the build publication process.
The required dry run did not print OK; nothing was pushed and the item is not READY.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered MatrixCore and Kernel modules with the repository versions.
   Existing declaration signatures are unchanged except for the declared restoration of
   the two finite-generation hypotheses, and the Kernel proof adaptation is limited to
   those required arguments. Verdict: pass, subject to the recorded change.
2. Compiled Pivot, MatrixCore, and Kernel together with `lcompile.py --all`; the files
   compile without warnings. The only remaining `sorry` is the named pivot theorem, and
   there are no axioms, unsafe declarations, or hollow definitions. Verdict: pass.
3. Checked the pivot node and searches. Its statement is a genuine leading-pivot
   reduction, strictly weaker than the core normal form, with finite-free hypotheses and
   documented zero-size cases; it is not a duplicate of an existing declaration.
   Verdict: pass.
4. Read the proof from the target downward. The core uses the pivot and then explicit
   source and target automorphisms; all three blocks are handled by direct cancellation.
   The imports added are used, and the rejected compatibility/data split is removed.
   Verdict: pass; the unit route is retained.
5. The DAG proof, dependencies, origin, Lean declarations, and change record agree with
   the current source. Verdict: pass.

Changed in this reading: removed the unused public import
`Mathlib.RingTheory.Localization.AtPrime.Basic`; no proofs or statements changed.
Added this review record only.
The required delivery dry run remains blocked because the compiled baseline lacks
`Sheaf.Algebra.Homology.ResidueKernelUnitMinorMatrixCore.olean`, so forced-adaptation
validation cannot compile the original Kernel module.

## Second reading by H2

Independent second reading, 2026-10-14 (this dispatcher session).

1. Compared MatrixCore and Kernel with the repository using `diff -u`. The only
   existing signature change is the two finite-generation hypotheses declared in
   `coord/changes/residue-kernel-unit-minor-finiteness.md`. Kernel's signature,
   universes, visibility and conclusion are byte-for-byte unchanged. Its proof
   changes supply precisely those two arguments. No definition or target changed.
   Checked the infinite-free counterexample in the change record: the shift
   cokernel is A[1/t], so it cannot be nonzero free and t-divisible. Verdict: pass
   for the recorded correction, not a proof of the false original generality.
2. Ran `lcompile.py --all` on the sandbox: Pivot, MatrixCore and Kernel compiled
   without warnings or errors (2.1 s, 2.7 s, 2.1 s). Scanned every delivery source
   for sorry and forbidden declarations. The only textual hole is the public named
   theorem `ModuleCat.residue_kernel_unit_minor_pivot`; there are no hollow
   definitions, axioms, unsafe, opaque, extern or implemented_by declarations.
   Compiled a scratch copy with `#print axioms`: `normalize_pivot` uses only
   propext, Classical.choice and Quot.sound; the core and pivot additionally use
   sorryAx, as expected from the stated pivot hole. Removed the scratch copy.
   Verdict: local proof checks pass; the core remains conditional on its pivot.
3. Read the entire pivot statement, docstring and node independently. It asserts
   only an invertible leading block, not the diagonal normal form. Rank-nullity
   supplies n-1; the nonzero residue determinant lifts to a unit. Checked n=1
   (empty pivot), n=0 (impossible residue kernel), zero target (only n=1), and
   C=0 (full row rank). The split is true and strictly simpler than the core.
   Searched independently with leanfinder for splitting a maximal-rank summand,
   loogle for `Matrix.fromBlocks, IsUnit`, and rg for minor and Schur-complement
   lemmas in the upstream and Sheaf sources. The upstream proved
   `Matrix.exists_submatrix_det_ne_zero_of_le_rank` supplies only the minor;
   field-only normal forms do not give the local-ring coordinates or tensor
   compatibility. The Schur lemmas address elimination, already proved here.
   No duplicate of the pivot or immediate few-minute closure found. Verdict: pass.
4. Checked every block formula and inverse from the core downward. The constructed
   maps satisfy sY(F(u,a))=(B(u)+b(a),d(a)-c(B.inverse(b(a)))); this is the claimed
   form relative to sX. The pivot is imported proof-only and actually used.
   Public imports support the signatures; tensor finiteness is proof-only in
   Kernel. The removed AtPrime import is unused by MatrixCore and Kernel imports
   it directly. The old node has no proof_deps to prune. Earlier rejected sandbox
   splits are not claimed as library pruning. Read sk-prop-av-cube's realized
   record: this work changes no unit statement, step or realization. Verdict: pass.
5. Compared both nodes with Lean. Core's proof_deps consists exactly of the pivot;
   its proof describes the explicit automorphisms and Schur remainder. The new
   pivot has source, complete proof, chapter/unit, created record, blueprint
   ancestry, three search records and its matching Lean declaration. Its proof
   is wholly `by sorry`. The corrected core signature is reflected in its Lean
   record and the change record names the only caller found by declaration-use
   search. Verdict: pass.

Changed in this reading: added this independent review and the search log entries;
no Lean proof, signature, definition, import or node edits were necessary. One core
hole is closed under the recorded finite-free correction, one pivot hole is added:
a decomposition with net zero holes, not an axiom-free proof of the core. Delivery
and the forced-adaptation baseline check are still to be verified by the standard
unmodified delivery tool.

Current delivery verification supersedes the earlier blocking audits: the standard
unmodified `deliver3.py ... --no-push` printed OK for commit dd6375d1f1. The published
baseline MatrixCore and BaseChangeFree objects are now available. The delivery tool
compiled the original caller against the baseline successfully, established its
failure against the changed dependency, compiled the adapted caller, and passed the
preflight and declaration axiom probes. No build artifacts or tools were changed
in this session. The change requires CODEX interface review; it is not proof-only
AUTO. No previously planned dependency node or library module is pruned.

## Forced adaptations

### Sheaf.Algebra.Homology.ResidueKernelUnitMinorKernel
Original against changed dependencies failed:
```
/tmp/forced-adaptation-shpub63t/lean/Sheaf/Algebra/Homology/ResidueKernelUnitMinorKernel.lean:52:72: error: Application type mismatch: The argument
  𝔭
has type
  Ideal R
of sort `Type v` but is expected to have type
  Module.Finite A ↑((extendScalars (algebraMap R A)).obj X)
of sort `Prop` in the application
  residue_kernel_unit_minor_matrix_core R A X Y f hfree.left hfree.right 𝔭

(with the modules compiled into /tmp/forced-adaptation-shpub63t/.lbuild) [1.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
