## What changed

Prove `WeilConjectures.PurStrictScalar.systemProperOrdinary_existsUnique` by
constructing the comparison as identity on sections. The limit-lift equations
identify constant restriction followed by a completion projection with the
actual constant quotient map. A private, explicit quotient tower is identified
with `systemRestriction` using its existing sectionwise characterization.
Naturality of the constant quotient map and continuous module pushforward
composition then give the level comparisons. Their horizontal naturality and
naturality in the input module assemble the whole-tower comparison. The generic
construction returns the explicit isomorphism together with its identity-on-
sections normalization; the concrete application only supplies the coefficient
ring square.

Uniqueness is sectionwise extensionality, proved for arbitrary comparisons in
the original types. Generic private helpers avoid unfolding the concrete
coefficient constructions during pushforward composition and extensionality.
The original file-level elaboration settings are retained. The two added
proof imports expose existing private helpers in `VaryingRingOperations` and
`CoefficientRingedSequenceSite`. All existing public signatures, definitions,
attributes and public imports are preserved. The node proof records the ordinary comparison in Step 6.

## Proved and sorry left

Closed: `WeilConjectures.PurStrictScalar.systemProperOrdinary_existsUnique`
(node `def-pur-native-constant-support-model`). One of the original three holes
is proved, with zero holes added and no decomposition.

Remaining, unchanged, both attached to `def-pur-native-constant-support-model`:

- `WeilConjectures.PurStrictScalar.systemPullMap_isIso`.
- `WeilConjectures.PurStrictScalar.systemOpenMap_isIso`.

The construction applies to empty schemes and zero modules. It uses identity
maps on the same section carriers and imposes no flatness assumption on the
horizontal coefficient maps. The existing derived-limit restriction calculation
first proves equality of the ring maps before applying module pushforward. Its cone equation is checked after
the faithful forgetful functor to ring sheaves. These avoid a costly congruence
step and repeated section extensionality without changing the argument. The
derived proper-image proof now passes its resolution-preservation lemma directly
to the private comparison helper. That helper performs the derived-unit argument
with abstract categories, avoiding concrete coefficient normalization there.
The private tower transition is shared by the functor-law proofs. The limit
proof transports its properties through equality of additive functors, avoiding
an unnecessary cochain isomorphism and quasi-isomorphism cancellation.

Validation: the complete assigned module typechecked through `lcompile.py` in
59.7 seconds, within the 60-second limit. The reported line-length warning is
fixed by wrapping the line. No profiling options or diagnostic commands remain.

## No longer needed

None. No original import, module or dependency node is removed. The ordinary
comparison follows the existing planned route. The inverse/open mate obligations
retain their original dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement change. The previous node proof described ordinary
proper comparison as still open; Step 6 now records its construction. No public
definition or target statement is changed. No new nodes or unproved statements
are introduced, and no consumer adaptation is required.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
