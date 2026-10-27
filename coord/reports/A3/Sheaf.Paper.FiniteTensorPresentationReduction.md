## What changed

Decompose `WeilConjectures.PurityFiniteSetting.finiteTensorPullbackCoherence` into
its two independent fixed-scalar diagrams and prove the original conjunction from
them. The new private proof imports are `FiniteTensorPullbackTensorReduction` and
`FiniteTensorPullbackCompositionReduction`. The tensor statement concerns a single
map f and two inputs; the composition statement concerns f,g and one input. They
are strict parts of expanded proof Step 7, and neither supplies the original
conjunction by itself.

All existing public signatures, definitions, attributes and public imports are
preserved. No source-library file is changed. Structural coherence and the positive
root-chart reduction retain their existing proofs. The parent node records the
assembly, and each new module has one named theorem, its source, a complete proof
in words and its own node. The unit route is unchanged. All three sandbox modules passed
`lcompile.py --all`; the delivery tool also runs axiom probes and preflight checks.

## Proved and sorry left

One upper hole is closed by decomposition:
`WeilConjectures.PurityFiniteSetting.finiteTensorPullbackCoherence`.
Two holes are added, so this is a decomposition, not a net proof closure.
The complete Lean assembly uses the two new independent families of equations.

Three original holes remain in the item, all attached to
`lem-pur-finite-tensor-presentation-reduction`:

- `WeilConjectures.PurityFiniteSetting.finiteTensorTwistAdditionCoherence`;
- `WeilConjectures.PurityFiniteSetting.finiteTensorTau_reduction`;
- `WeilConjectures.PurityFiniteSetting.finite_tensor_presentation_reduction`.

The two new holes are:

- `WeilConjectures.PurityFiniteSetting.finiteTensorPullbackTensorReduction`, node
  `lem-pur-finite-tensor-pullback-tensor-reduction`;
- `WeilConjectures.PurityFiniteSetting.finiteTensorPullbackCompositionReduction`, node
  `lem-pur-finite-tensor-pullback-composition-reduction`.

No definition contains a hole, and no other hole is changed or added.

## No longer needed

No baseline import is removed and no node or module is withdrawn. The original
proof imports still support structural coherence and the positive root-chart proof.
The parent now uses the two fixed-scalar diagrams for Step 7. The cochain coherence,
K-flat pullback and scalar-adjunction nodes remain needed in the proof plans of
those diagrams; moving that work to the two statements does not prune it globally.
The original plans for twist addition, native tau reduction and purity presentation
remain needed. The experimental tau proof and its private shift-square import are
retained only in the scratchpad and are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

Expanded Step 7 supplies the cochain tensor and composition diagrams, but the
identification with the recorded fixed-coordinate scalar-adjunction mates and their
realization transports is a separate argument. The two new statements expose those
two independent obligations, including their normalization and descent, rather than
postulating the original conjunction under another name.

The earlier dependency-overlay failure no longer blocks compilation. A separate
attempt to prove native tau reduction found that its defining-equation comparison
requires expensive derived-category instance conversion. An admitted diagnostic
isolated the rest of that candidate at 33 seconds; fully checked native comparisons
remained over the limit despite several representation experiments. Those experiments
are not delivered. The original native tau definition and its original hole are
restored verbatim. The present decomposition concerns the distinct pullback assertion.


A read-only dependency audit also found the pre-existing two-node proof cycle
`lem-pc-ring-hom-extension-differential` ↔
`lem-pc-ring-hom-extension-differential-adjacent` in the shared DAG. Neither node
is changed here. Every existing dependency of the two new cuts was already a
direct statement or proof dependency of the original parent. The cycle is reported
for maintainer follow-up; this packet does not attempt an unrelated DAG repair.

## New nodes

`lem-pur-finite-tensor-pullback-tensor-reduction` states the tensor square for the
recorded coefficient pullback mate, for one arbitrary scheme map and two arbitrary
derived inputs. Its proof plan descends the coefficient-extension cochain tensor
square, identifies the adjunction mate by its unit, and cancels realization units
and counits. Module: `Sheaf.Paper.FiniteTensorPullbackTensorReduction`.

`lem-pur-finite-tensor-pullback-composition-reduction` states the independent
compositor square for two scheme maps and one arbitrary derived input. Its proof
plan uses cochain composition, composition of mates, localization and the fixed
realization transports. Module: `Sheaf.Paper.FiniteTensorPullbackCompositionReduction`.

Both include identity maps, empty schemes and equal coefficient levels, impose no
flatness of the quotient, and use the source of the parent's Step 7. There are no
statement or definition change records because existing statements and definitions
are unchanged.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
