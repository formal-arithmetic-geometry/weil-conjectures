# Nested experiments: PR #1563

Case: AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula.
Snapshot: Lean 4.35.0, master revision 1ef1fddac73e, one thread,
synchronous elaboration.

## Baseline and preserved context

The before prefix is 115.92 CPU s, 117.04 wall s, and 8,008,236 KB peak
RSS; the after prefix is 50.00 CPU s, 50.98 wall s, and 5,146,444 KB.
The target Kernel checks are 68.2 and 15.2 s. The exact site is the fourth
Eq.mpr argument-domain conversion under the original twelve binders. Its
right-hand CategoryStruct.comp is the real nested composition consumer.

## Experiment A: representation symmetry status

The outer Eq and CategoryStruct.comp heads are shared, but all seven
composition arguments are structurally different. The corresponding
carrier and left composition compare in 0 ms. No single major-premise
replacement was accepted by Kernel.check while preserving the dependent
composition type, so a valid A/A or B/B symmetry matrix cannot be formed.
This is recorded as a negative A result rather than comparing isolated
leaves. The source run performs instance synthesis; probes/nd/G1A-
EqCompArguments.lean replay explicit stored terms in the Kernel.

## Experiment B: nested composition amplification

The original consumer contains a seven-argument CategoryStruct.comp whose
argument 6 is another CategoryStruct.comp. The outer right composition
costs 31,026 ms; the nested pair costs 21,537 ms. Its independent argument
costs are 18,975, 20,810, 20,603, 11,325, and 15,552 ms for the tested
type-preserving replacements. The outer argument timings are 1, 0, 2,245,
2,079, 2,146, 6,601, and 22,155 ms.

These are a controlled descent through the same consumer and keep the
original leaf representations, but they do not constitute a new synthetic
depth ladder: changing the number of CategoryStruct.comp layers changes
the dependent morphism type. The result supports nested-context
amplification locally, with confidence below a Level-2 causal claim.

## Experiment C: repeated composition fanout

The seven outer arguments and the nested argument-6 composition expose
several occurrences of the same data-bearing functor/morphism vocabulary.
The nested probe replaces one occurrence at a time and preserves the
checked result type; every replacement leaves a substantial conversion.
This rules out the claim that one independent leaf check accounts for all
31 seconds. It does not provide a field-count matrix, because the
CategoryStruct.comp arguments are dependent and cannot be duplicated or
removed while retaining the original theorem obligation. C is therefore
partial fanout evidence, not a controlled C1/C2/C4 result.

## Experiment D: provenance audit

LEFT: the old proof uses Eq.mpr with concrete higherDirectImageRawOverFunctor
and nested raw-module pullback compositions. CategoryStruct.comp is an
abbrev accessor whose body exposes CategoryStruct.2; the concrete functor,
map, and morphism arguments are supplied by the old construction.

RIGHT: the instantiated Eq.mpr domain carries the corresponding concrete
composition from the theorem type. It is imported/stored before the probe
and is not rewritten by local priorities. The first timed divergence is the
right composition, especially nested argument 6; the final proof argument
is Eq.refl, so the proposition-type boundary is real but not a separate
proof search cost. The fixed helper changes the producer to the abstract
pullback interface.

## Matched fast control and interpretation

The shared helper higherDirectImageRawOverPullback_eq_moduleFactors costs
about 32.4 s in both forms and provides a same-context control for the
imports and category hierarchy. The after theorem is a statement-level
control, not a single-leaf alignment.

Outcome: B is supported as local nested-consumer amplification and C has
partial repeated-occurrence evidence. A has no valid alignment control; D
identifies concrete raw pullback/composition construction plus an abbrev
projection as the provenance. The case does not reach Level 2 because a
depth/fanout matrix would alter the dependent morphism type.
