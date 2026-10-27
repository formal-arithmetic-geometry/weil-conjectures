## What changed

The assigned theorem now constructs its comparison by composing three natural maps:
the completed-E reduction cochain counit, the system scalar cochain counit, and
the localization of an ordinary strict tensor-association isomorphism.
The finite evaluation equation is proved by naturality of the exact-localization
factors, A.evaluation and the finite scalar counit. Finite reduction preserves
K-flatness by the existing coefficientTensorModelPreservation theorem, so the
finite scalar counit is invertible. Joint conservativity then proves that the
constructed natural transformation is a natural isomorphism.

Three separate intermediate theorems isolate the remaining construction work.
Reduction has no second coefficient field; scalar evaluation has no completed
reduction or direct model; the association theorem has no derived comparison.
They are strictly separate parts of the original three-step argument. None
restates the original comparison assertion, and the final composition,
evaluation calculation and invertibility argument are Lean proofs in the item.

The item's signature and public imports are unchanged. No existing definition,
statement, source-library declaration or consumer is changed. New imports are
private proof imports. New helper modules use public imports only for their
statements. The scalar helper uses the existing coefficientScalarModelZero
explicitly and publishes the proved lemmas coefficientExtensionSystemEvaluationZero and
coefficientExtensionEvaluationFiniteZero. The helper statements use these
composite instances explicitly so zero-map instance search does not unfold the
system coefficient data. No new global typeclass instance is registered.
The unit-normalization predicate is cached irreducibly. All writes are in the
assigned sandbox.

Validation: lcompile.py --all compiled all four delivered Lean files with exit
code zero and no warnings. The compile service accepted every file under its
per-file Lean time limit.

## Proved and sorry left

Closed the one original hole in
WeilConjectures.coefficientExtensionStrictDerivedComparison
(stage3-pur-extension-strict-derived-comparison).

Added three holes, each the entire proof of one public named theorem:

- WeilConjectures.coefficientReductionNaturalCochainComparison
  (stage3-pur-reduction-natural-cochain-comparison).
- WeilConjectures.coefficientScalarCochainEvaluation
  (stage3-pur-scalar-cochain-evaluation).
- WeilConjectures.coefficientExtensionOrdinaryAssociationChain
  (stage3-pur-extension-ordinary-association-chain).

The item itself has zero remaining holes. This delivery is a decomposition:
one hole closed and three added, not a net reduction in the sorry count.
There are no sorry bodies in definitions or private declarations.

## No longer needed

No existing import was removed: the original module had only its statement
import. No module is withdrawn or globally pruned.

The item's direct proof dependency on lem-pur-kflat-change-of-rings-independent
is replaced by the already proved coefficientTensorModelPreservation, which
provides the exact finite K-flatness assertion needed here. The item does not
construct K-flat resolutions itself. Its former direct dependency on
lem-coef-semilinear-derived-sections is also unnecessary: the coefficient
calculus already supplies isIso_iff_evaluations. The semilinear theorem remains
needed by the smaller scalar-evaluation statement. Resolution work and the
sequence-projection derived adjunction belong to the new reduction and scalar-evaluation lemmas;
they remain needed below those lemmas. The updated item node records its actual
new proof dependencies rather than leaving the earlier unimplemented steps.

## Where the brief, the DAG or earlier work was wrong

The old node marks construction/descent of naturality as elementary, but its
Lean dependencies do not expose a natural cochain comparison for the fixed
reduction calculus. Objectwise CoefficientReductionModels alone does not supply
this: evaluations detect isomorphisms but not equality of arbitrary derived
system morphisms. The new reduction lemma asks for a natural cochain
transformation on all complexes, obtained before evaluation by the normalized
derived adjunction.
The item composes natural transformations; it does not infer naturality from
finite evaluations.

CompletionUnit.derivedAdjunctionComparison_exists is related existing work,
but requires invertibility of l on W and a separate calculus coherence witness,
neither of which the assigned theorem assumes. Its weaker reduction-only
conclusion is isolated here without adding those hypotheses. The ordinary
CompletionUnit model is used as a generic tensor/limit-adjunction tool; it does
not change the unit route. The unit record sk-def-purity-conv has no realized
proof steps, and no unit or chapter record is edited.

The new reduction proof uses
lem-sfb-resolving-derived-adjunction-normalization and
lem-weil-pbc-ringed-topoi-derived-pushforward-composition as general tools for
the normalized derived adjunction, alongside the assigned sequence-projection
and K-flat-resolution dependencies. The ordinary-association proof uses
lem-pur-system-scalar-generators and lem-pur-system-scalar-coherence for
sectionwise scalar tensors, and the proved
lem-pur-system-ringed-sequence-site for the explicit strict-system equivalence.
The scalar-evaluation proof uses the same generator lemma and the assigned semilinear/evaluation calculus. These general results
supply interfaces absent from this unit; they do not replace a realized unit
step. No maintainer tool_uses approval is written by this packet.

Edge cases checked in the mathematical statements: zero complexes; n=0 (the
first positive quotient); arbitrary integer degrees; an empty pro-etale site;
identity field inclusion; and ramified inclusions. No boundedness, flatness of
the quotient ring map, or invertibility of l on W is added.

## New nodes

stage3-pur-reduction-natural-cochain-comparison isolates the natural cochain
counit for completed-E reduction into an arbitrary normalized ordinary quotient
model. It is independent of E-to-L extension, scalar association and direct.

stage3-pur-scalar-cochain-evaluation isolates ordinary evaluation of a system
scalar functor, its actual unit normalization and the corresponding cochain
counit square. It is independent of completed reduction and direct.

stage3-pur-extension-ordinary-association-chain glues finite ordinary tensor
associations to an isomorphism of strict system complexes, using the prescribed
successor transitions. It has no derived functor comparison conclusion.

Each node carries its complete source proof, the performed search records and
the exact Lean attachment. No change record is required because no existing
statement or definition changes.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
