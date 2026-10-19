## What changed

Proved five original obligations in `Sheaf.Paper.FiniteSystemPullbackCoherence`
by specializing the existing varying-ring operations to the lifted coefficient
rings. Naturality uses the faithful forgetful functor from commutative rings to
rings. Composition existence and uniqueness uses the conjugation equivalence
and the uniquely section-normalized direct-image compositor.

All original signatures, definitions and visibility are unchanged. Removed the
retained diagnostic profiler settings and the unverified private evaluation helper.
The complete file compiles through lcompile.py in 22.5 seconds after the final import pruning.

## Proved and sorry left

Closed five of seven original holes:

- WeilConjectures.finiteSystemBaseChange_continuous
- WeilConjectures.finiteSystemRingComponent_naturality
- WeilConjectures.finiteSystemPushforward_isRightAdjoint
- WeilConjectures.finiteSystemPullback_exact
- WeilConjectures.finiteSystemComposition_existsUnique

Two original holes remain, both attached to
`lem-pod-finite-system-pullback-coherence`:

- WeilConjectures.finiteSystemPullbackEvaluation_existsUnique
- WeilConjectures.finiteSystemPullbackCoherence

No holes added and no split-offs. These proofs use the existing stated,
partly unproved varying-ring interface; this is a reduction to that existing
interface, not a claim that their transitive axioms are sorry-free.

## No longer needed

Removed these redundant direct proof imports, whose relevant interfaces are
already available through the retained imports:

- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
- Sheaf.AlgebraicGeometry.ProEtaleConstantExact
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.CategoryTheory.GeometricModuleTransport
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
- Mathlib.CategoryTheory.Adjunction.CompositionIso
- Mathlib.CategoryTheory.Localization.Predicate

No node or module is declared globally unnecessary. The remaining coherence
hole retains its original planned dependencies. The added proof import is
`Sheaf.AlgebraicGeometry.VaryingRingOperations`, node
`def-sp-varying-ring-operations`: its arbitrary varying-ring operations are an
exact specialization for the lifted ring tower. This generic tool supplies the
specific system-level interfaces needed here and preserves the unit route.

## Where the brief, the DAG or earlier work was wrong

The retained report claimed the evaluation-existence proof was complete, but
its helper did not compile within the file limit. It is retained in scratch
history, and the delivery leaves that original named theorem open. The five
other retained proofs have been verified together in the complete module.
The node copy records the generic varying-ring specialization without claiming
the still-open evaluation or coherence proofs.

Remaining work: the evaluation proof must turn the generic moduleEvalG unit
identity into the sectionwise unit formula, and conversely for uniqueness.
The difficult elaboration compares evaluation and direct-image restriction of
scalars; the retained `change` step and several API-based rewrites exceed the
heartbeat or file budget. The native section-map API experiments are in the
sandbox scratchpad. The fibre-product associativity calculation itself was
proved and compiled there, but is not imported or delivered because the final
coherence theorem still needs the levelwise normalization, its identification
with the published derived comparison, and the localization argument.

Resumed-session verification (2026-10-19): the required current-source dry run
passed with commit b83da8ba89 (nothing pushed). The delivered-source candidate
was retained unchanged. Further evaluation experiments are scratch files only;
they do not close either remaining obligation. Several lcompile.py requests then
returned exit 124 with "no answer from the compile server" after 184--208 seconds.
This is a compile-service failure, distinct from a Lean file exceeding its
60-second limit. The service check of the previously compiled SiteAssoc.lean also failed with
exit 124 and no service response after 192 seconds; its result is recorded in
scratchpad/resume-service-check.log. No delivery push was run in this resumed session.

Further resumed-session verification (2026-10-19): checked the retained module
against current sources; its changes remain the five proofs and proof-import
pruning reported above. The required initial dry run failed with no compile-server
answer after 190 seconds. Retried the dry run: the same service failure after
188 seconds, recorded in dry-run-current-service.log. Independently retried
the previously compiling SiteAssoc.lean through lcompile.py: exit 124 after
182 seconds without a server answer, recorded in
scratchpad/current-service-check.log. These are service failures, with no Lean
compiler diagnostic, rather than single-file Lean timeouts. No launcher files
were changed, no library files were written, and no delivery was pushed. The
candidate proofs and the two original remaining holes are preserved unchanged.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
