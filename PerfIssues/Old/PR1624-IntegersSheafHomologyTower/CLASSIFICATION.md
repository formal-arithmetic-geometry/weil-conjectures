# PR #1624 classification

Case ID: `AlgebraicGeometry.ProEtale.homologyIntegersTowerIso` in `IntegersSheafHomologyTower`. Lean 4.35.0, master revision `1ef1fddac73e` with built dependencies. [Before.lean](Before.lean) restores only the historical target value on the current prefix; [After.lean](After.lean) is the fixed current form.

## Phase and cost site

Synchronous before/after compilation takes 111.38 versus 11.77 user CPU seconds, with 11,038,208 versus 2,668,464 KB peak RSS. The target's Kernel type check is 102 versus 3.18 seconds; tactic execution in each file is below 1 second. This locates the cost in Kernel checking of the value of `homologyIntegersTowerIso`, not elaboration. The declaration type is the same in both probes.

The old value builds `e2`, `e3`, `e4`, `e5`, and `e24` as local isomorphisms, then assembles the final proof with `Functor.isoWhiskerRight ...` composed with `Functor.isoWhiskerLeft ...`. Its source and target contain long, differently associated `Functor.comp` chains of concrete derived functors. The fixed value passes those pieces to `homologyIntegersTowerIsoAux`, whose source and target functors are variables. The controlled value replacement drops the target Kernel check by about 99 seconds.

## Mechanism

Primary label: **A, Kernel reduction/definitional equality**, with **E, concrete-versus-abstract representation**, contributing. The expensive operation is checking the old final iso composition's dependent source/target functor types. The [PR description](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/1624) reports an isolated `rfl` reassociation of these concrete functors taking about 15 seconds and identifies `Functor.comp` unfolding; that expression-level probe is historical evidence, not a new 4.35.0 measurement. Our same-prefix replacement and 102-to-3.18-second Kernel split confirm that this old composition still carries the cost on 4.35.0.

Confidence is high for phase, declaration, and value-level cost; moderate for the precise inner conversion because this round did not dump the 4.35.0 Kernel expression pair. The historical PR says the statement is unchanged, but the current probes are diagnostic copies, not a proposed library change.
