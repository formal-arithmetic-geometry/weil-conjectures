# Nested experiments: PR #2122

Case: AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteEtale_integralBoundary.
Snapshot: Lean 4.35.0, master revision 1ef1fddac73e, one thread,
synchronous elaboration.

## Baseline and branch isolation

The old module is 347.37 CPU s, 350.32 wall s, and 16,321,824 KB peak RSS;
the current split module is 29.87 CPU s, 30.69 wall s, and 5,285,748 KB.
The old final theorem value replay costs 172.014 s. The preserved value has
14 theorem binders followed by 12 lets and an Exists.casesOn branch.

The first required step for Batch 4 is the branch-local probe
probes/nd/G4B-ValueFrames.lean. After opening the theorem binders and
substituting the lets, it checks the recursor's real local context:

| Branch component | Kernel.check |
|---|---:|
| motive branch | 16,115 ms |
| stored witness/predicate branch | 18,419 ms (body 2,212 ms) |
| final dependent branch | cannot be checked independently |

The last result is a validity failure, not a timeout: its expected type is
supplied by Exists.casesOn's dependent motive. No branch replacement was
accepted as a type-preserving parent value.

## Experiment A

A is not validly executable yet. The historical PR names concrete versus
abstract category/functor representations, but the branch probe does not
isolate an A/B pair at the same Exists.casesOn cost site. Comparing a raw
branch with the fixed split module would change imports and helper
boundaries, so it is not a representation symmetry control.

## Experiment B: nesting amplification status

The actual consumer is already a deeply nested dependent recursor with 14
binders, 12 lets, and a branch-local witness. The motive and witness branch
checks are measured in the same context, but there is no independent depth
parameter: adding or removing a class layer changes Exists.casesOn's motive
and invalidates the branch type. We therefore record B as an attempted
isolation with no valid depth matrix.

## Experiment C: repeated-field fanout status

The branch has no confirmed repeated same-typed data-bearing fields. The
historical expression contains several category/functor witnesses, but
duplicating or removing one would alter the dependent recursor. The final
branch cannot be checked alone, so no C field-count claim is made.

## Experiment D: provenance audit

LEFT: the old declaration builds concrete DiagonalAb/sheaf-category and
functor-composition data inside the Exists witness and its branch motive.
The stored value includes zeta-bound categories, ring structures, and
derived-category/Quiver.Hom data before the recursor consumes them.

RIGHT: the expected theorem type is the imported/stored Eq proposition and
is not rewritten by local priorities. The first observed divergence is at
the branch boundary, where the recursor supplies a dependent motive; the
historically reported candidates are DiagonalAb versus sheaf categories,
(F ⋙ G).obj versus G.obj (F.obj), and ULift.ring versus CommRing.toRing.
Those candidates remain source-guided until an inner branch pair is
isolated.

## Matched fast control and interpretation

The current split module is a matched statement-level control: it retains
the theorem result but moves common category/proposition helpers into
imports. It confirms a large Kernel/module-context effect, not a single
representation cause.

Outcome: branch-local Kernel cost is confirmed, but A, B, and C do not reach
Level 1 because the final dependent branch cannot be replayed independently.
D records the concrete category/functor producers as hypotheses only. The
case is explicitly inconclusive rather than attributing Exists.casesOn iota
reduction or a guessed leaf mismatch.
