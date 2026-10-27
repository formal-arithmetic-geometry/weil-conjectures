## What changed

The original statement and `CommonStageAssembly` interface are unchanged.
`ExceptionalCommonStageFromRational` now constructs the closed operation from explicit
left and right pair functors, their actual descended adjunction, and the shift structures
of the remaining exactness lemma. The inclusion comparisons are the inverse canonical
restriction isomorphisms. Their identity components prove normalization; the descended
counit formula proves the counit comparison. A proved calculation of the pair functor on
inverse transitions proves the original transition law, including equality transport
from the published scalar transitions. Mathlib supplies additivity directly from the
constructed adjunction: the right adjoint preserves binary products and zero morphisms,
and additivity of the left adjoint follows from that of the right adjoint.

`ExceptionalRationalScalarComposition` adapts the existing proved
`NormalizedRationalLeftComposition` argument to `RingStageAssembly` and
`RationalStageAssembly`. It proves the actual rational scalar composition equation using
residue Tor, the integral normalized compact-support cocycle, and localization of the
specified scalar associator. It does not request a completed coefficient record or any
closed operation.

`ExceptionalRationalCommonCoherence` transports that composition equation to the actual
published stage-system associators. Endpoint wrappers retain the supplied data while fixing
the category instances. The tower equality is transported as a natural transformation
before evaluating components. It explicitly constructs both stage-system morphisms.
The right tower equation and compatible unit/counit families are proved by adjunction
transposition. `StageSystem.Morphism.adjunction` then supplies the actual pair adjunction.
All functor and adjunction definitions are constructions from the given data.

`ExceptionalRationalCommonExactness` isolates the remaining shift normalization and
exactness calculation on these fixed constructions. Its existence theorem is eliminated
only inside the proof of the original existence theorem. No definition chooses a functor,
adjunction, or arbitrary witness from that unproved existence theorem.

Validation: all four delivered modules compile through `lcompile.py --all`.
The assigned module compiled in 50.3 seconds with no diagnostics; all files stay
within the 60-second per-file limit.

## Proved and sorry left

Original hole closed: `WeilConjectures.ConstructibleExceptionalCoefficients.exists_common_stage_descent`
(node `lem-sf-common-stage-descent-fixed-rational`). Its body contains no `sorry`.

New hole added: `WeilConjectures.ConstructibleExceptionalCoefficients.exists_rational_common_exact_shifts`
(node `lem-sf-rational-common-exact-shifts`). This is the delivery's only remaining
`sorry`, and it is a whole named theorem with its source and proof in words.
Thus the original one-hole obligation is decomposed into one strictly smaller hole;
this is a decomposition, not a net hole reduction.

The new scalar-composition and common-coherence modules have zero holes. In particular,
`ring_stage_rational_left_composition`, `rational_common_scalar_coherence`, the mate tower
and unit equations, and the explicit adjunction construction are proved. The remaining
lemma cannot supply alternate operations or comparison maps: all of those are fixed
before its statement, and it only supplies shift structures, exactness, and their squares.

## No longer needed

No original import is removed, and no existing module is withdrawn or claimed globally
unreachable. The proof adds only the proof imports it uses and the new modules above.

The original node's separate direct applications of
`lem-pur-mate-unit-compatibility`, `lem-weil-pbc-adjunction-of-natural-bijection`, and
`lem-weil-pbc-mate-pasting` are replaced by explicit finite mate calculations and
`lem-coef-qbar-stage-adjunction-descent`. Its separate direct applications of
`lem-pur-coefficient-scalar-units`, `lem-pur-ringed-coefficient-projection-cocycle`,
`lem-sf-open-tensor-normalization`, and `prop-weil-pbc-scalar-extension` are packaged by
the proved rational composition calculation and the published stage-system interface.
The former direct `lem-coef-integral-residue-tor` application now belongs to the
scalar-composition module. `def-weil-algebraically-closed-coefficients` remains a
statement dependency and supplies the categories used through their stage interface.
These nodes remain needed transitively or in statements; this is not a request to
remove their modules. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan treated shift descent as an elementary step. The supplied rational
operations carry their own shift structures, and the endpoint shifts on their localization
comparisons need not be the canonical ones. Applying the generic canonical shift-descent
lemma directly would silently replace those fixed structures. The remaining lemma states
the endpoint correction calculation explicitly, including independence of compactification.
It is strictly step 4, after steps 1–3 and the transition calculation have been formalized.

The existing `normalized_rational_left_composition` theorem takes a completed ring record,
which already contains closed operations. Its proof only uses ring and rational data.
Adapting that proved argument avoids assuming the output of this item in order to prove it.

The stale quarantine/import error did not describe the current source: the unchanged item
compiled against the published artifacts before editing. The current server queue assigned
a proof item with one hole, rather than a zero-hole repair.

A read-only dependency audit also encountered an existing metadata cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. No delivered or edited node lies
on a dependency cycle. This packet does not change those unrelated nodes.

## New nodes

`lem-sf-ring-stage-rational-left-composition` records the proved rational left scalar tower
law using only the input ring and rational assemblies. Its proof is the specialization of
the existing normalized rational composition argument to those input records.

`lem-sf-rational-common-scalar-coherence` records the proved transport to actual stage
systems, mate calculations, and explicit unshifted pair adjunction. Identity and repeated
stages are included because the coefficient-inclusion equalities and associators used are
the published ones; no strictness assumption replaces them.

`lem-sf-rational-common-exact-shifts` records the sole remaining hole. It asks for shift
and exactness structures on already defined functors and adjunction, with exactly the
original rational shifts in the restriction squares. Its proof in words explains the
endpoint corrections, scalar compatibility, finite-triangle exactness, and unit/counit
squares. Empty schemes and zero objects require no extra nonemptiness assumptions;
negative shifts use the same integer CommShift addition law.

No existing module outside the assigned item is changed; no change record is required.
The generic adjunction and shift/exactness descent results used as tools are already
Lean-closed project declarations. Their geometric normalization hypotheses are retained.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalCommonStageFromRational": "29a9766b30b9457948262ca2451b6bebab4494d2", "Sheaf.Paper.ExceptionalRationalCommonCoherence": "028ec8b2caacc41f04646c735bf1e2d49302f9b8", "Sheaf.Paper.ExceptionalRationalCommonExactness": "458944f065a9b2d00ebb250a46f41b5789d85b42", "Sheaf.Paper.ExceptionalRationalScalarComposition": "ff89553a3c947d583ce84feab64495e603500185"}, "own_failed": ["Sheaf.Paper.ExceptionalRationalCommonCoherence", "Sheaf.Paper.ExceptionalRationalCommonExactness", "Sheaf.Paper.ExceptionalCommonStageFromRational"], "results": {}, "time": "2026-10-28T03:46:39+0800", "transitive": 36, "version": 1}
```

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
