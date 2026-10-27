## What changed

Proved `localization_system_kernel_stabilization` in
`Sheaf.TraceFormula.LocalizationSystemKernelStabilization`, preserving its complete signature
and existing docstrings. The proof kills a finite generating set at a common upper bound,
extends this to the kernel by span induction, and clears one localization denominator for
each later kernel element. No upstream source module or consumer changes.

The cocone tests groups in the independent universe `uR`. To compare its kernel with the
explicit additive direct limit, compose each rational-circle character with the direct-limit
legs, lift the character codomain to `uR`, and apply the assumed cocone property. Mathlib's
`CharacterModule.eq_zero_of_character_apply` then detects zero, and
`AddCommGroup.DirectLimit.of.zero_exact` gives eventual vanishing. Both are proved in Mathlib.
The node records this universe bookkeeping and otherwise retains its four-step source route.

Proof imports now use `Mathlib.Algebra.Colimit.Module` and
`Mathlib.Algebra.Module.CharacterModule`.

## Proved and sorry left

Closed the one existing hole: `localization_system_kernel_stabilization`
(`lem-trf-localization-system-kernel-stabilization`). Holes added: zero. Holes remaining: zero.
No statement was split off.

## No longer needed

Removed proof imports `Mathlib.Algebra.Category.ModuleCat.FilteredColimits` and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures`: the proof uses
Mathlib's explicit additive direct limit instead of constructing a categorical module diagram.
All three recorded proof dependencies remain mathematically used. No DAG node or project
module is pruned, and the unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The original plan's passage from the supplied cocone to the usual module colimit does not
explain its independent target universe. The character calculation fills that technical gap
without strengthening any hypothesis or changing any conclusion. Empty generator sets,
zero modules, non-antisymmetric preorders, and denominators that are zero divisors are
covered: only the specified inverse-denominator equation is used.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
