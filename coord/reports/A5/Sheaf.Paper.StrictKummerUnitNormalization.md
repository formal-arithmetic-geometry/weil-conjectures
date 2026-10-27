## What changed

Replaced the proof hole in `AlgebraicGeometry.ProEtale.strict_kummer_unit_normalization`
by a t-structure construction in the category of strict p-adic systems. The private
proved helper `kummer_target_of_concentration` constructs H and b using Mathlib's
`exists_iso_singleFunctor_obj_of_isGE_of_isLE` and `singleFunctors.shiftIso`.
It then supplies the constructed comparison to the kernel-normalization step.
The original proposition definition, theorem signature, attributes and public imports
are unchanged.

Added `Sheaf.Paper.StrictKummerCohomologyConcentration`, with a complete proof of
`strict_kummer_cohomology_concentration`. It computes arbitrary supplied D on a
regular resolving class using the already proved private machinery of
`DiagonalDerivedReductionExists`, as `DiagonalResidueDerivedFactorization` does.
The long exact homology sequence of the multiplication/quotient short exact
sequence proves vanishing away from degree minus one; Kummer epimorphy is the
only geometric input. Evaluation detects vanishing of homology objects of strict
systems. The source shift gives concentration in degree minus two.

Added `Sheaf.Paper.StrictKummerPureKernelNormalization`. Its real proposition
`KummerPureKernelNormalization` records only roots identification and the evaluated
unit equation for an already supplied H and b. Its theorem is the one residual
proof obligation. Neither this proposition nor any other definition chooses data
from a sorry. Both new modules are proof-only imports of the item.

Validation: all three delivered modules compiled cleanly in import order through
`lcompile.py --all`: concentration 16.2 s, residual statement 41.1 s, and the
item 45.1 s. Local text checks confirmed the existing public definition and
theorem signature are verbatim unchanged, every Lean line is at most 100
characters, and each node's proof dependencies equal the union of its step uses.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.strict_kummer_unit_normalization` by a complete Lean
proof from concentration, Mathlib's reconstruction theorem, and the residual
kernel-normalization theorem. The item now has zero holes.

Proved `AlgebraicGeometry.ProEtale.strict_kummer_cohomology_concentration` in full,
with zero holes. Its private helpers prove counit computation on the resolving
class, quotient exactness outside the kernel degree, and detection of exactness
by evaluation; none has a sorry.

Added exactly one hole:
`AlgebraicGeometry.ProEtale.strict_kummer_pure_kernel_normalization`, node
`lem-sfb-strict-kummer-pure-kernel-normalization`. Its proof is exactly `by sorry`.
It must identify the surviving cohomology, its scalar action and transitions,
and normalize the quotient unit on that kernel. It does not assert existence
of H or b, construct a derived isomorphism, or prove cohomology concentration.

This is a decomposition: one original hole closed, one lower hole added, net
zero holes eliminated. The cohomology-concentration part and reconstruction of
the strict comparison are proved. The complete target is still conditional on
the named residual theorem.

## No longer needed

No existing imports or modules are withdrawn, and no globally prunable module
is claimed. The original direct proof dependencies now occur through the two
new nodes, except standard truncation, which the item uses directly through
Mathlib's t-structure theorem. The new concentration proof does not need any
roots identification, Cartier root-to-line comparison, finite-coefficient
Ext class, or divisible-extension normalization; those remain needed only in
the residual kernel-normalization step. Its public imports are the diagonal
system interface and Mathlib's standard derived t-structure.

## Where the brief, the DAG or earlier work was wrong

No original statement defect was found. The server queue describes this as a
one-hole proof-route item; no current rework or build-error entry was present.
The reconstruction and vanishing can be separated from the kernel normalization
without asserting that independently chosen roots and finite-level maps satisfy
an arbitrary b's unit equation. The residual theorem therefore quantifies over
H and b first, and only then chooses roots and t together.

The existing normalized Kummer target and reduction-unit helpers under
`SpTowerClasses` cannot be imported here: their dependency chain passes through
`DiagonalTowerSystem` and returns to this item. No such cyclic import is added.
The existing source-library tree is unchanged, and no other group module was
adapted.

Edge checks: n=0 means the positive exponent n+1=1; ell remains prime and the
Kummer epimorphism applies. The proof uses neither division by two nor a
nonzero-sheaf assumption. The residual normalization transports roots and t
along b simultaneously, so changing b's sign or an automorphism does not
assert an equation for fixed unrelated choices. All comparisons retain strict
transition maps; evaluation is used only to detect zero homology objects.

## New nodes

`lem-sfb-strict-kummer-cohomology-concentration` records the proved vanishing
step, realized by `Sheaf.Paper.StrictKummerCohomologyConcentration`. Its source
is step (3), the target computation in the current diagonal-tower blueprint.
The implementation uses the existing resolving-class and Kummer declarations.

`lem-sfb-strict-kummer-pure-kernel-normalization` records the remaining kernel,
scalar-action, transition and unit calculation for an existing pure comparison,
realized by `Sheaf.Paper.StrictKummerPureKernelNormalization`. Its source is
steps (3) and (4) of the same blueprint. Each new node includes three kinds of
Mathlib search, a self-contained statement, proof steps and a verbatim Lean
statement. The item's node now follows concentration, strict reconstruction,
and residual kernel normalization. No change record is needed: no existing
statement or definition has changed, and no other existing module is edited.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.StrictKummerCohomologyConcentration": "408da234447db039d5afb592fc018e73b94cb546", "Sheaf.Paper.StrictKummerPureKernelNormalization": "aa59890c46b201b91a25a167ce98f385e4fd9629", "Sheaf.Paper.StrictKummerUnitNormalization": "f8695f7726640a4cf57d98a916c5c859524d88e3"}, "results": {"Sheaf.Paper.KummerStrictAdjunctCompatibility": {"hash": "35ec62ed52498a1f3e32c1242de43501913d5465", "status": "OK"}}, "seconds": 61, "time": "2026-10-28T04:28:20+0800", "transitive": 0, "version": 1}
```

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
