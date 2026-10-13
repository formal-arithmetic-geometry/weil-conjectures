## What changed

Proved `Algebra.exists_bounded_local_kernel_generators` in
`Sheaf.RingTheory.SyntomicPresentationLocalKernel` without changing its signature or
visibility. Added proof-only imports of `SyntomicFibreKernelGenerators`,
`SyntomicLocalKernelIntersection`, and `Mathlib.RingTheory.Nakayama`.

Separated the argument into bounded generation modulo the base prime, and the flat
kernel intersection identity. The latter is fully proved in its new module from
Mathlib. Its proof constructs compatible localized scalar structures, proves the
localized map is surjective with the expected kernel, applies
`LinearMap.ker_inf_smul_top_eq_smul_of_flat`, and transports the resulting submodule
identity to ideals. The original theorem then explicitly writes a kernel element
as a chosen-equation part plus a base-prime part, places the latter in the ideal
product, proves the base-prime ideal lies in the local maximal ideal, and applies
Nakayama to the finite localized kernel.

Updated the original DAG node to this proof and added two nodes matching the two
new modules. All three modules compile in dependency order, without warnings.
No existing statement, definition, public import, or visibility changed.

The resumed worker independently checked the earlier sandbox proof and its two new
statements, reread Stacks 00SY and 00SC, confirmed the exact Mathlib flat-kernel
lemma with Loogle and source search, and recompiled all three modules. The required
`deliver3.py --no-push` dry run printed OK; the second reading remains for the
separate reader. Nothing was pushed.

## Proved and sorry left

Closed the original hole in `Algebra.exists_bounded_local_kernel_generators`
(node `lem-weil-pbc-syntomic-presentation-local-kernel`).

Fully proved the new theorem `Algebra.syntomic_local_kernel_intersection`
(node `lem-weil-pbc-syntomic-local-kernel-intersection`) using only Mathlib.

One added hole remains: `Algebra.exists_bounded_fibre_kernel_generators`
(node `lem-weil-pbc-syntomic-fibre-kernel-generators`), the complete first two steps
of the original argument plus the inverse-image interpretation of fibre generation.
Its hypotheses omit both flatness and finite generation of the original kernel;
its conclusion is generation modulo pA, not equality of the localized ideals.
Its proof is exactly `:= by sorry`, with the source and full argument in its
public theorem docstring. There are no other sorries in the delivery.

This is a decomposition: one upper hole closed and one strictly smaller hole added,
net zero holes. The flatness and final Nakayama steps are proved, not moved.
No object is defined by choosing arbitrary data from the unproved theorem.

## No longer needed

No original public import is removed. No existing Sheaf module is claimed pruned:
the complete-intersection definition is still needed by the statements, and the
field conormal rank theorem is still needed by the remaining fibre step.

These four planned nodes are no longer needed by this argument:

- `lem-weil-pbc-localization-at-prime-of-quotient`: replaced by Mathlib
  `IsLocalization.ker_map` and localized surjectivity in the proved intersection lemma.
- `lem-weil-pbc-localization-module-exact`: the localized kernel calculation uses
  `IsLocalization.ker_map` directly.
- `lem-weil-pbc-flat-quotient-tensor-injective`: replaced by Mathlib's proved flat
  linear-kernel intersection identity.
- `lem-weil-pbc-tensor-over-quotient-ring`: no quotient module or tensor comparison
  needs to be constructed in the final argument.

The remaining original dependencies (conormal rank, fibre-local-ring comparison,
polynomial scalar extension, quotient base change, and Nakayama) remain needed,
with the first four assigned to the fibre-generator node. A redundant temporary
proof import of `Mathlib.RingTheory.Finiteness.Ideal` was removed after recompiling.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The original plan's quotient
module and tensor calculation are unnecessary: Mathlib already proves the stronger
kernel intersection identity, from which ideal Nakayama gives the desired equality.
The existing field conormal theorem does not directly give original R-polynomial
representatives or the scalar/prime comparisons required by the fibre step;
those are precisely the work retained in the new fibre-generator node.

Read Stacks 00SY and 00SC at their official tag pages because the cited local
`literature/stacks-project/algebra.tex` is absent on this machine. Searches used
Lean Finder, Loogle, source grep, and blueprint searches; LeanSearch returned
Internal Server Error. No matching existing node was found. The other occurrence
of the flat intersection Mathlib lemma is a tensor-kernel quotient result with
different hypotheses and conclusion, not this presentation-localization theorem.

Edge cases checked mathematically: c=0 gives the zero equation ideal and Nakayama
still applies; n=0 forces c=0; zero R or S has no chosen prime q; no Noetherian
hypothesis on R is used. The fibre polynomial ring over κ(p) is Noetherian, so the
fibre-generator step does not require the original kernel to be finite. The original
hfg is used exactly for `Ideal.FG.map` in the final Nakayama argument.

## New nodes

`lem-weil-pbc-syntomic-fibre-kernel-generators` corresponds to
`Sheaf.RingTheory.SyntomicFibreKernelGenerators`: one remaining theorem, bounding
original equations and proving generation modulo pA. Its proof records the field
conormal rank, spanning representatives, denominator units, fibre Nakayama, and
inverse-image containment. It is strictly the fibre part of the argument.

`lem-weil-pbc-syntomic-local-kernel-intersection` corresponds to
`Sheaf.RingTheory.SyntomicLocalKernelIntersection`: fully proved ideal intersection
identity, with no complete-intersection or finite-generation hypothesis. Its two
DAG steps list the exact Mathlib declarations implemented by the Lean proof.

No change record is needed: no existing interface was changed and no other module
was adapted. The new nodes inherit the chapter and unit; the unit's realized steps
and every chapter/unit route remain unchanged.

## Second reading by U3

1. Compared the delivered presentation module with the repository version. The existing theorem signature and visibility are unchanged; only proof-only imports and its proof body were added. The two additional modules are new declarations recorded by matching DAG nodes.
2. Compiled all three modules with `lcompile.py --all`. There are no compiler errors or warnings, no forbidden declarations, and the only remaining `sorry` is the explicitly split `Algebra.exists_bounded_fibre_kernel_generators`. The fully proved intersection theorem uses only the permitted axioms.
3. Read the two new statements and docstrings against the Stacks sources and checked edge cases (zero generators and zero ideals). The fibre statement is strictly weaker than the original target, while the intersection statement is independent of finite generation and complete-intersection hypotheses. No existing library declaration duplicates either result.
4. Checked the proof route and pruning claims against the DAG. The flat kernel identity follows the Mathlib theorem directly, and the original target uses the fibre reduction, intersection identity, and Nakayama in that order. The listed obsolete localization/tensor nodes are not used by the delivered proofs; the unit's realized route remains represented by the three nodes.
5. Reran the static delivery checks after this report update. Verdict: the proofs and statements are sound for delivery; the sole open hole is the documented fibre-generator decomposition, with no hollow definition or altered target interface.
