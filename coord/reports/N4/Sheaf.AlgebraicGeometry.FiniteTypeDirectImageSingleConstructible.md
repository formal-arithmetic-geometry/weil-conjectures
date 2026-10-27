## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeDirectImage_single_constructible`
from the existing finite-coefficient finiteness and coefficient comparison declarations.
The original theorem signature and public imports are unchanged.

For finite torsion coefficients, the proof uses the exact sectionwise coefficient
encoding, an étale bounded constructible origin, finite-type étale finiteness, and the
bounded-below comparison with actual unbounded direct image. For integer coefficients,
the residue criterion reduces to this finite case; bounded constructible complexes over
the finite residue field have finite Tor amplitude. Direct-image completeness and the
actual reduction mate give the reverse criterion. Integral models and exact scalar
extension handle finite rational fields, and finite-stage descent handles the algebraic
closure. Actual continuous ring isomorphisms handle embedded integers and unit balls.

The returned proof compiled in 45.2 seconds, and its complete delivery set passed
preflight after suppressing an unused-section-variable warning in a private helper.
The helper retains the shared separated finite-type context. The proof checks the
empty and zero-coefficient cases through the existing finite encodings; the torsion
exponent may be zero. The import-cycle repair is checked separately below.

Repair of return bd6e535e9b4: removed the unused BoundedConstructible public import
from TraceBaseChangeFirst. The earlier packet's two unused-import removals are retained.
The returned section-derived-realization path reaches the trace module, so its
high-level import must be removed in this packet. Every existing supporting signature
and global attribute is preserved. To reduce repeated unfolding in the trace file,
its specified tensor core, ordinary monoidal structure and derived unit are constructed
directly using the canonical objects that its existing equality theorems
already identify. Existing compact structure aliases are used locally, and a proved
private helper exposes tensor normalization without expanding a choice term. The
already proved generic source theorem supplies derived braiding compatibility, so
the local K-flat calculation and the heavier étale proof import are unnecessary. The
existing import of the upstream-extra derived-monoidal API becomes public because
the public construction bodies now use its canonical unit and tensor structure.
Change record:
`coord/changes/N4-trace-import-cycle-repair.md`.

The item passes its standalone check in 46.9 seconds and the integral coefficient
square in 24.1 seconds. The final build compiles the trace module and both unchanged
consumers, ProEtaleProjectionExchangeMaps and TraceBaseChangeSecond, without warnings.
It rebuilds their artifacts in dependency order. No held consumer requires adaptation.
The full overlaid import graph has no closing cycle and the import-pruning check passes.
Eighteen elaborated public signatures, including implicit parameters and universes,
match the published originals.

Updated the item's DAG proof and dependencies to follow this route. The trace node's
proof description now records the equal canonical constructions and compact interfaces.
No target, coefficient ring, or adopted source-library declaration is changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeDirectImage_single_constructible`
(the item's one original hole).

Added: none. Split off: none. The item has zero remaining `sorry` declarations.
The three supporting adaptations also have zero `sorry` declarations.
Existing dependency theorems that still contain `sorry` are used as the stage-3
interfaces; their statements are not copied or weakened.

## No longer needed

The following original planned dependencies are unnecessary in this proof. This is a
local dependency reduction, not a claim that their modules can be withdrawn globally.

- `def-sfb-rationalization-equivalence`: Use bounded constructible integral models and exact scalar extension.
- `lem-kun-dimension-finite-type`: No cohomological dimension bound is needed for the single-sheaf constructibility conclusion.
- `lem-sf-integral-direct-image-constructible`: Prove the finite-type integral case from residue finiteness instead of applying this interface.
- `lem-sfb-extend-scalars-bounded-constructible`: Apply constructibility of exact scalar extension to each homology module.
- `lem-sfb-extend-to-qlbar-constructible`: Use the finite-stage cocone and exact homology scalar extension directly.
- `lem-sfb-finite-discrete-constructible-model`: Use the fixed normalized encoding and the existing constructible-origin theorem.
- `lem-sfb-integral-ambient-tower-comparison`: The internal residue criterion and direct-image limits already give the integral comparison.
- `lem-sfb-integral-constructible-completion-bridge`: Use the internal residue criterion directly.
- `lem-sfb-localized-direct-image-comparison`: Use the continuous integral push comparison.
- `lem-sfb-normed-coefficient-realization`: Use actual continuous coefficient ring isomorphisms.
- `lem-weil-pbc-finite-discrete-derived-coefficient-data`: Derive the actual underived encoding/direct-image comparison through exact equivalences.
- `lem-weil-pbc-qcqs-morphism-permanence`: Available morphism instances provide qcqs.
- `lem-weil-pbc-qcqs-over-affine`: Available morphism instances provide qcqs.
- `sk-def-sfb-dc-setting`: The original statement imports already supply the setting; no high-level finiteness proof is imported.
- `sk-def-sfb-rationalization`: No abstract rationalization category is used.
- `sk-thm-sfb-qlbar-two-colimit`: Only the existing essential-surjectivity consequence of the cocone is used.

The original item had no private proof imports to remove. The unused public import of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` is removed
from `Sheaf.Paper.RestrictedCoefficientPullbackData`,
`Sheaf.Paper.IntegralCoefficientSquareNormalization`, and
`Sheaf.Paper.TraceBaseChangeFirst` to break the import cycles. No module is withdrawn.
The trace file no longer needs its private helpers `monoidal_core_roundtrip`, `proof_transport_three`,
`condensedTensorCore_eq`, `generic_derived_delta`, `generic_derived_braid_Qh` and
`canonical_derived_symmetry`: the
ordinary monoidal structure is constructed directly and derived braiding is supplied
by the proved source theorem. The private import of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided` is replaced by
the smaller generic derived-monoidal interface. The direct private import of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit` is also
unused after the unit simplification and is removed; its API remains available
through the existing public monoidal import.
Their proved bodies are removed; no public declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original plan mixed the tower/completion, abstract rationalization and finite-model
interfaces. The residue criterion plus the existing continuous coefficient interfaces
provide a shorter route. The fixed finite-discrete encoding supports the required
bounded-below direct-image comparison; finite residue field coefficients also supply
finite Tor amplitude by dévissage.

The fetched delivery state retains an unused high-level import in
`Sheaf.Paper.RestrictedCoefficientPullbackData`, creating a cycle through integral
direct-image normalization. This delivery removes that one public import; definitions
and signatures are unchanged. The adapted module compiles in 5.9 seconds. A change
record lists its consumers; the import-pruning check verifies their visibility.

The first returned packet missed the residue-criterion path through
IntegralCoefficientSquareNormalization. The second packet passed its source-cycle and
preflight checks but was returned on a newer path through SectionDerivedRealization,
SectionDerivedTensorData and TraceBaseChangeFirst. The previous current-main snapshot
had no path to that trace module; the new packet retains its unused-import removal
rather than relying on that snapshot. No theorem is restated or weakened.
Current main changed ProEtaleSectionModuleFunctors during validation so that it no
longer imports TraceBaseChangeFirst. That obsolete consumer snapshot is neither included nor adapted.
The trace repair is retained independently of this changing parent path. Current
consumer lists were refreshed after the change; no held consumer requires adaptation.
The subsequent dry run rejected the trace file at 75 seconds despite the earlier
standalone pass. Profiling identified failed rewrite searches in the concrete
composition calculation. The repair focuses the tensor-quotient rewrite on the
right-hand side, uses a proved generic tensor cancellation lemma, keeps the module
tensor structure folded through the remaining assembly, and elaborates sequentially.
No new statement or hole is introduced.
Initial scratch consumer checks used the published library and were replaced by the
final combined overlay check. An earlier individual overlay check of TraceBaseChangeSecond
used an older compiled intermediate and failed in the kernel; rebuilding the intermediate
and consumer in dependency order resolves it without source edits. Natural-transformation
composition and the large trace propositions are kept folded, with explicit equations
used where their constructions are needed.

A subsequent dry run reached 61 seconds for the trace file. Its assembly now reuses
the source library's proved DerivedCategory.symmetricCategory rather than reconstructing
that structure, and keeps the canonical derived braiding folded after defining its
public alias. The existing monoidal functor instances and their proof fields are retained.

Profiling then identified repeated searches for tensor colimits on graded module objects.
Eight proved private caches reuse the existing Grothendieck, flat-resolution and tensor
instances, and are activated only in private proof sections. They do not enter public
signatures or definition bodies. The module adjunction stays locally folded during
tensor normalization. This trace version passed its standalone check in 47.2 seconds;
the unused commutativity binder of the Grothendieck cache was subsequently omitted.

After omitting that binder, the final combined build compiled TraceBaseChangeFirst,
ProEtaleProjectionExchangeMaps and TraceBaseChangeSecond without warnings, using fresh
artifacts in dependency order. The unchanged consumer copies have been removed from
the delivery packet. All four production modules contain zero holes.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
