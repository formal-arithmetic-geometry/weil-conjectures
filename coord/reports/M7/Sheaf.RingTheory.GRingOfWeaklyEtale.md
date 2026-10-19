## What changed

Proved `RingHom.isGRing_of_weaklyEtale` with its original signature and public
imports unchanged. Six private, fully proved helpers handle absolute-flat
localization, regular and geometrically regular localization, cancellation of
weakly etale fibres, closed-fibre formal smoothness, and completion regularity.
No definitions or other modules were changed.

The proof retains the completion-square argument of Greco Theorem 5.3(i).
Instead of expressing every weakly etale fibre as a finite product of fields,
it proves directly that the map from the fibre to the relevant residue field
is localization at its kernel. Base change of this localization, tensor
cancellation, and separable field ascent prove regularity of the target's
formal fibres. The theorem docstring and the existing DAG node's proof,
proof dependencies and proof origin now describe this argument.

Validation: the required final `deliver3.py ... --no-push` printed
`OK (dry run): commit 774074d9da compiles and passes the preflight`.
Compilation and the axiom probe passed; the review class is CODEX because the
DAG route changed. The first dry run's interface warning was repaired by
qualifying IsLocalRing names and using anonymous universes in private helpers.
The public interface now matches the original, and all Lean lines fit the
100-character limit. No successful global build is claimed; that is the
maintainer's independent verification.

## Proved and sorry left

Closed the original hole `RingHom.isGRing_of_weaklyEtale`
(`lem-exc-weakly-etale-g-ring`): 1 of 1 holes. Zero holes remain in the item,
zero holes were added, and zero statements were split off. All six private
helpers are proved. Existing dependency theorems are used as declared; this
is a proof from those declarations, without a claim that their entire
transitive dependency closure is already sorry-free.

## No longer needed

Removed these proof imports (all public imports are retained):

- `Mathlib.RingTheory.AdicCompletion.Algebra`
- `Mathlib.RingTheory.AdicCompletion.Basic`
- `Mathlib.RingTheory.AdicCompletion.Completeness`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Sheaf.RingTheory.AdicCompletionNoetherian`
- `Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit`
- `Sheaf.RingTheory.Flat.LocalizationPreservesFlatness`
- `Sheaf.RingTheory.FormallySmoothAdic`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.RingTheory.IndEtaleUniverseTransport`
- `Sheaf.RingTheory.WeaklyEtaleField`

The finite-product/filtered-colimit argument is replaced by absolute flatness,
stalk surjectivity and localization. `Sheaf.RingTheory.WeaklyEtaleField` is
replaced by the narrower existing source theorem
`Algebra.WeaklyEtale.isAlgebraic` in
`WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField`. Stability is supplied by
Mathlib's weakly-etale base-change and composition results, and the source's
localization theorem. Completion Noetherianity uses its current source module,
`WeilConjectures.RingTheory.AdicCompletionNoetherian`. The remaining removed
imports are redundant through retained public dependencies or completion-local
ring imports; their declarations introduce no additional direct proof needs.

The original route no longer directly needs these DAG dependencies:

- `lem-pc-affine-flat-module-localization-preserves-flatness`
- `lem-weil-pbc-ind-etale-stability`
- `lem-weil-pbc-weak-etale-field`
- `lem-weil-pbc-henselization-finite-separable-fibres`
- `lem-weil-pbc-adic-complete-jacobson-radical`
- `lem-weil-pbc-geometric-regularity-separable-extension`

The separable-extension equivalence is narrowed to its forward node
`lem-weil-pbc-geometric-regularity-separable-extension-forward`; the full
module remains needed for that theorem. Completion locality and completeness
use Mathlib's completed-local-ring API, including
`AdicCompletion.maximalIdeal_eq_map`, instead of reconstructing them through
the Jacobson radical. Removed obsolete `tool_uses` approvals for the discarded
flat-module localization, ind-etale stability, full weakly-etale-field theorem,
finite separable fibre product and separable-extension equivalence. No claim
is made that these modules are globally unreachable from every other target.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left a private helper unfinished and its report recorded
an unverified proof candidate. The transport goal is now filled using the
existing compatible field/ring-isomorphism theorem. The planned finite-product
calculation is unnecessary: the localization argument handles a single prime
at a time and works with independent ring universes.

Checked the edge cases: a zero target has no primes; closed fibres of the
localized local maps are nontrivial local rings; arbitrary empty fibres are
never required to be fields; separable extensions need not be finite. No
hypothesis, target statement, definition, or unit-level route was changed.
The assigned unit has no realization entries affected by this pruning.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
