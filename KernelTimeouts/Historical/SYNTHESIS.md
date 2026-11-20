# Cross-case synthesis

## Answers to the historical questions

1. **Slow Derived Tensor has a clear same-head/reducibility boundary effect.** The value
   checks in 1 ms, while the original final conversion takes 50 s in the tensor probe and
   122–132 s in the full consumer. Changing only six aliases from `abbrev` to
   `@[reducible] def` removes the minute-scale path. The exact lazy-delta branch is not
   kernel-traced, so the mechanism is strongly supported rather than fully confirmed.

2. **Derived-Completion Cone demonstrates a large final type conversion.** The inline
   `sorry` declaration checks its type and value in 3 ms each but does not finish its final
   conversion after ten minutes. The same real cone term completes in 9.5 s once the diagram
   is named.

3. **The cone cost is an interaction.** The concrete derived `MonoidalCategory` instance is
   causal: an explicit local instance reduces the diagnostic declaration to 18 s. Naming the
   diagram independently reduces it to about 17 s, and the two together reduce the complete
   API to 5.3 s (9.5 s with the real term). The 36 proof-position differences explain why
   proposition types, rather than proof bodies, are compared; the exact internal fan-out is
   still inferred.

4. **The cases share a high-level lesson but are distinct mechanisms.** Both preserve a
   useful early comparison boundary in the successful form. Tensor loses a regular-definition
   same-head opportunity and descends through derived functor implementations. Cone compares
   proof-dependent proposition types whose data-valued instance arguments were reconstructed
   under nested-proof abstraction. They must not be collapsed into one “abbrev is slow” rule.

5. **The dominant work is concentrated in one parent conversion in each historical case.**
   Tensor’s counters show many reductions inside one final `isDefEq`; cone’s 36 proof leaves
   fan out from one final conversion. There is no evidence that independent generated field
   checks add up to the reported times.

## Comparison with the 15 current records

The table uses the labels in the current case records. “Match” means that the recorded
conversion boundary and a controlled response are comparable; it does not transfer the
historical classification automatically.

| Current case | Recorded boundary/control | Historical comparison |
| --- | --- | --- |
| `RealPushforward` | `LinearMap.charpolyRev` unfolds to a small polynomial; fixed form completes in 2.80 s | Negative/simple-unfold control; no large-structure claim |
| `OrderedSpectralRawLattices` | three instance paths (`Semifield.toCommSemiring`, `CommRing.toCommSemiring`, regular henselian/domain) require a bundle alignment | Strong B-style instance-bundle match; same-boundary measurement possible |
| `EtaleHomComparisonReversedExact` | instantiated dependent binder domain differs (`DerivedCategoryModule` versus raw `DerivedCategory`) | B-style dependent-domain match, but current primary label E/A/C |
| `FiniteBaseChangeRestrictionMateTransport` | `Scheme.ProEt` versus `OpenTensorNormalization.Site.ordinary`; `hb` transport is the control | Base-change analogue; whole dependent domain is the comparable boundary |
| `F66Adj` | `Over.left` versus local `X` in a proof proposition; helper changes the accessor path | B-style data-bearing accessor mismatch; current E/A/C |
| `ImageHomCounit` | raw `DerivedCategory` versus `DerivedCategoryModule`; uniform alignment is much faster | Strong interface/boundary match; current E with A/C contribution |
| `IntegralComparisonPullbackRealizationShifts` | two `HasDerivedCategory` paths under `Functor.obj`; first leaf alignment is non-causal | Falsifies a one-leaf instance explanation; deeper composition remains |
| `RealPurity` | `Field.toCommRing` versus algebraic-closure ring under `Polynomial.reverse`; ring alignment does not remove timeout | Falsification control; current mechanism remains unclassified |
| `NativePullTensor` | two expensive `Exists.choose` application-domain conversions (23.050 s and 22.981 s); argument self-checks are cheap | Closest A/H1 comparison by phase, but repeated dependent-domain conversions make it a distinct P3/E case |
| `PR1556-AmbientCounterexampleCoproducts` | final historical closing proof adds 54.9 s Kernel checking; typed `sorry` removes it | Kernel conversion under a concrete component; A plausible, B possible |
| `PR1563-RawModuleScalarPullback` | raw pullback helper versus concrete scalar-pullback functors; target value check drops 68.2 s to 15.2 s | Base-change/interface match; exact inner pair open |
| `PR1624-IntegersSheafHomologyTower` | old final composition checks 102 s versus 3.18 s fixed; `Functor.comp` boundary | Strong A/E composition match |
| `PR1625-TensorSheaf` | component proof under `NatTrans.app`; 87.6 s old versus 2.43 s fixed | Strong nested-accessor match to tensor’s descent, but different local head |
| `PR1627-WeilSheafTransport` | generated nested proof/dependent `id` domain removed by generic helper | Closest B proof/type match; same boundary family, not identical instance |
| `PR2122-DiagonalTraceFiniteEtaleIntegralBoundary` | no STRUCTURE-AUDIT conversion control establishing a historical match | Unclassified relative to both historical cases |

The eight `KernelTimeouts` rows are direct current audit records. The seven `PerfIssues`
rows with structure audits are `NativePullTensor`, PR1556, PR1563, PR1624, PR1625, PR1627,
and PR2122. `PR1559-UpperStarMonoidal` is intentionally omitted from this 15-case set because
its current port is explicitly not a successful benchmark.

## Mechanism classification

| Hypothesis | Historical evidence |
| --- | --- |
| H1 lost high-level comparison boundary | confirmed as a tensor phase effect; strongly supported as the reducibility cause |
| H2 large proposition/type conversion | confirmed for cone phase and concrete instance relevance |
| H3 repeated conversion | secondary in cone (36 proof positions); not the dominant tensor explanation |
| H4 intrinsic reduction | not supported: representation alignment removes both historical costs |

The practical rule for current audits is therefore precise: compare the exact conversion pair,
then test a boundary-preserving alignment. A superficially similar wrapper or instance leaf
is not enough. The current records that most closely match are `NativePullTensor` (same
Kernel-domain phase), `PR1627` (nested proof types), `OrderedSpectralRawLattices` (bundle
instance expressions), and `ImageHomCounit`/`PR1624` (whole representation alignment).

## Round-two status

The fresh historical runs preserve the synthesis while tightening the evidence. For A,
the tensor node's instance argument alone took 52,157 ms in the A0 probe, while the
category and category-instance arguments took 0 and 1 ms; changing the six aliases to
`@[reducible] def` made the full consumer conversion 2 ms in both orientations. The
unannotated ordinary-`def` form failed typeclass synthesis, so it is not a performance
counterexample.

For B, the fresh inline `sorry` declaration timed out at 118.66 s, while the named
diagram and explicit shared-instance controls completed in 2.27 s and 2.35 s. Thus the
round-two phase split directly confirms one final conversion boundary and independently
supports both factors. The proof-leaf dump and conversion tree remain historical notes,
not re-measured round-two numbers.
