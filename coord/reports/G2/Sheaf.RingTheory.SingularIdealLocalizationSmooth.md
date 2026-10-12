## What changed
Added a complete reduction of `smooth_localization_of_mem_singularIdeal` to the strictly simpler intermediate theorem `smooth_localization_span_from_radical`. Added supporting module `SmoothOfLocalizationSpanUniverses` for the span-locality statement (currently sorry).

## Proved and sorry left
The target theorem `smooth_localization_of_mem_singularIdeal` is proved from `Ideal.mem_radical_iff` and the intermediate theorem. Sorry remains in `smooth_localization_span_from_radical` and `smooth_of_localization_span_universes`.

## No longer needed
No imports pruned.

## Where the brief, the DAG or earlier work was wrong
The planned proof requires a universe-polymorphic form of `RingHom.Smooth.ofLocalizationSpanTarget`; the Mathlib declaration is universe homogeneous, so the final span-locality step cannot be applied directly when `R : Type u` and `A : Type v`.

## New nodes
`lem-weil-pbc-singular-ideal-localization-smooth-radical-span` and
`lem-weil-pbc-smooth-of-localization-span-universes` are new intermediate statements requiring follow-up proofs.

## Second reading by G2

1. **Unchanged statements.** Compared the delivered item with the repository version. The
signature of `Algebra.smooth_localization_of_mem_singularIdeal` is unchanged byte for byte;
no existing definition or target statement was altered. Verdict: pass.
2. **Proof checks.** Compiled both delivered modules with `lcompile.py --all`. The target
reduction compiles and contains no forbidden declarations; the two deliberately split
intermediate theorems remain the only `sorry`s. Verdict: pass, with those named holes open.
3. **Split statements.** Checked the radical-span and universe-polymorphic span-locality
statements against the singular-ideal definition and Mathlib's localization smoothness
criterion. They are strictly simpler than the target and mathematically appropriate; no
existing Mathlib or Sheaf declaration duplicates them. Verdict: pass.
4. **Pruning and route.** The target proof uses `Ideal.mem_radical_iff` and the split
radical-span theorem. The span-locality module is imported privately for proof use. No
unused imports or unit-route bypass were found. Verdict: pass.
5. **DAG/report consistency.** The target node remains the original item and the report
identifies both split declarations and their source route. The unit's span-locality route
is retained. Verdict: pass.

Changed the second-reading documentation for both split theorems, added their blueprint
references and proof-source summaries, and fixed the leading whitespace before the target
theorem. No mathematical statements were changed.

