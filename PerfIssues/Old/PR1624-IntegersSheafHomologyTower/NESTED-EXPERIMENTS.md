# Nested experiments: PR #1624

Case: AlgebraicGeometry.ProEtale.homologyIntegersTowerIso.
Snapshot: Lean 4.35.0, master revision 1ef1fddac73e, one thread,
synchronous elaboration.

## Baseline and preserved context

The historical prefix is 111.38 CPU s, 112.48 wall s, and 11,038,208 KB
peak RSS; the fixed prefix is 11.77 CPU s, 12.44 wall s, and 2,668,464 KB.
The target Kernel checks are 102 s and 3.18 s. The preserved consumer is
the final Iso.trans application and its last isoWhiskerLeft dependent
argument domain. The original nine binders and eleven let-bound data values
are substituted before replay.

## Experiment A: representation symmetry

Path A is the concrete Functor.comp endpoint assembled by the inferred
isoWhiskerLeft term; path B is the endpoint in the instantiated expected
domain. Both are retained under the same Iso head and category context.
The endpoint probe reports source/target conversions of 14,706/28,640 ms.
The four dependent endpoint arguments (2, 3, 6, 7) are independently
structurally unequal in 0--8 ms. Every attempt to replace one argument by
the corresponding other argument is rejected by Kernel.check because its
dependent endpoint data changes. Therefore no type-preserving A/A variant
exists at a single argument, and no false alignment speedup is reported.

This is a valid negative A result: the outer consumer is preserved, the
paths are definitionally equal only after reducing the complete concrete
composition, and local priorities cannot rewrite the imported expected
domain.

## Experiment B: nesting amplification

The real consumer already has a multi-layer provider shape: an Iso.trans
argument, two iso whiskerings, and Functor.comp endpoints with nested
Functor data. The measured source/target endpoint costs are 14,706 and
28,640 ms, while instance/category carrier arguments are 0 ms. A new
synthetic Layer0--LayerN chain cannot keep the same dependent endpoint
types, so it would fail section 2.1. We record B as inconclusive rather
than calling the two endpoint measurements a controlled depth trend. The
explicit endpoint probe separates Kernel conversion from source instance
synthesis.

## Experiment C: repeated endpoint fanout

The four endpoint argument positions 2, 3, 6, and 7 are the repeated
manifestations of the concrete provider representation. Their independent
checks are cheap (0--8 ms), but the complete source/target endpoint checks
are expensive. Replacing any one position is ill-typed, so a one-mixed or
alternating field matrix cannot be constructed without changing the
consumer. This is evidence of possible fanout, not a controlled C result.

## Experiment D: provenance audit

LEFT: the old declaration constructs the final iso directly from concrete
derived-functor compositions under the two whiskerings. Its data-bearing
structure is an Iso with Functor.comp endpoints, and the representation is
introduced by concrete composition and derived-category instance fields.

RIGHT: the expected domain comes from the instantiated Iso.trans prefix and
contains the corresponding concrete compositions, including
higherDirectImageQuotPowTower on one endpoint. It is already stored in the
declaration and is not rewritten by local priorities. The first divergence
is in endpoint arguments 2/3/6/7; the common Iso head, carrier, and
category instance compare immediately. Zeta reduction of the eleven lets
does not remove the cost.

The fixed helper changes the producer to abstract functor parameters and
named comparison isomorphisms. That is a provenance change supported by
the measured before/after control, not a single-leaf alignment proof.

## Matched fast control and interpretation

The two earlier declarations in the same prefix cost about 2 s in both
forms and retain the same imports and category hierarchy. They are the
matched fast control for the endpoint consumer. The after helper is a
separate API control.

Outcome: A localizes the representation divergence but has no valid
single-factor fast alignment; B and C remain inconclusive because the
dependent Functor.comp endpoints reject independent substitutions. D
confirms concrete composition under nested Iso whiskering as the producer.
The evidence reaches Level 1 localization, not Level 2 amplification.
