## What changed

Filled `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`
in the assigned source module. The proof recovers H2's reduction argument from the
recorded reverted landing. It also restores that landing's proof-only rewrites
of the finite, upper-star and principal-ideal corollaries, using explicit
reduction/tensor transports. A proved private `principalIdeal_property` helper
prevents repeated unfolding in the principal-ideal kernel check.
The change record is `coord/changes/H4-etale-exchange-scoped-proof.md`.
Two private proof imports supply constant-module generation and the proper-factor
left-adjoint interface. All existing public imports, signatures, docstrings and
all non-theorem bodies remain verbatim.

For the chosen compactification, the existing proper-factor left-adjoint statement
supplies coproduct preservation. The canonical projection transformation, restricted
to derived constant modules, is invertible on the coefficient ring. The existing
module-generation theorem extends this to every module, in particular the quotient.
The open projection comparison then gives the compact-support comparison, and the
explicit reduction/tensor identifications give the requested functor isomorphism.
Derived-functor irreducibility is local to this namespace's elaboration, and the
two instance-search removals are scoped to the general reduction theorem alone.
They do not alter the exported interface.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`.
No holes remain in the item, and no holes or declarations are added elsewhere.
The new private `principalIdeal_property` helper is fully proved.
This is a proof from existing declarations, not a decomposition.

The proof still depends on the pre-existing admitted instance
`AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`.
That source instance is marked STATEMENT-DISPUTED: its arbitrary coefficient
category generality is not covered by the finite-coefficient theorem. This delivery
does not prove or strengthen that premise, and does not claim a sorry-free axiom
closure. The module-generation theorem itself is already proved.

## No longer needed

None. No existing declaration, public import, module, node, unit statement or unit
proof step is removed. The two added private imports are both used. No DAG node has
this module as its current Lean attachment, so there is no attached proof record to
rewrite. The finite-reduction unit's realized statements retain their existing route.

## Where the brief, the DAG or earlier work was wrong

The item is also listed in `coord/repairs.txt`: H2's landing was reverted after seven
reported downstream failures (record d710411a976aee01). Its archived proof and change
record were read and used as the starting point. The current source still has the
original hole. Since the previous attempt, four reported consumers were restored:
ExtensionZeroStratifiedPerfect, ReductionOpenEtaleOrigin, SitePerfectComplex and
WeilTensorProduct. Together with FiniteRingEtaleCompactGenerators and
FdCoefficientComparison, these are the six currently active reported consumers.
FiniteCoefficientDirectImage remains quarantined at its recorded archive path;
its archive and Lean attachment are preserved. No consumer is withdrawn or restored
by this delivery. FiniteRingEtaleCompactGenerators already has the public imports
requested by its recorded diagnostics.
The repair preserves Exchange's entire original public interface and scopes the
instance-search removals to the theorem. Derived-functor irreducibility is local
to elaboration within the file and is not exported.
The general proper-factor adjoint premise's disputed status is stated above rather
than being treated as an established arbitrary-coefficient projection theorem.

Validation: the final file compiles cleanly through lcompile.py in 16.8 seconds,
and again in 19.7 seconds while publishing the verification overlay. It contains
no diagnostic settings or raised limits. Public imports and existing docstrings
match the source exactly; Lean lines are at most 100 characters.

Unchanged consumer copies compile against the final published verification overlay:
FiniteRingEtaleCompactGenerators (24.9 seconds), ExtensionZeroStratifiedPerfect
(7.7 seconds), FdCoefficientComparison (34.9 seconds), ReductionOpenEtaleOrigin
(1.4 seconds) and SitePerfectComplex (1.6 seconds). These verification copies are
outside the delivery's lean directory. The final Exchange artifact was compiled
before these five checks, including the consumers' transitive imports.

WeilTensorProduct reached the 60-second limit without a Lean diagnostic against
both the unmodified published baseline and the earlier minimal repaired overlay.
Its current full-file compilation is not claimed to pass. No interface or proof
in that consumer is changed here. FiniteCoefficientDirectImage remains quarantined.

The earlier minimal proof exceeded the file limit on retries. A diagnostic copy
with a lower heartbeat threshold located an expensive kernel check in the
unchanged principal lower-star theorem. Restoring the explicit proof transports
and the abstract principal-ideal helper resolves Exchange's timeout. Those
diagnostic settings are not in the delivery.

The initial required delivery attempt terminated with exit 143 without diagnostics
or a push. The next attempt compiled and ran the axiom probe, then preflight
refused only this report's missing change-record path; that path is now recorded
above. A subsequent retry also terminated with exit 143 before reporting a push.
No launcher files or budgets changed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
