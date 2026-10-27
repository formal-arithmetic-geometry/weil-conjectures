## What changed

Completed `AlgebraicGeometry.ProEtale.CondensedRing.isIso_projectionMate_localizing_finiteExtension`
in `Sheaf.Paper.RationalLocalizingProjectionFormula`, preserving its mathematical statement and
every existing public declaration and definition. Existing tensor proof arguments and canonical derived-category instances are explicit in three
public signatures. Proof irrelevance and the identical instance data make their types
definitionally equal to the originals, with all binders and universes retained. The proved private helper `finite_coefficient_iso` embeds the
arbitrary universe-sized finite normed field into the fixed algebraic closure and constructs the
condensed ring isomorphism by postcomposition on continuous sections. Spectral norm uniqueness
proves continuity in both directions. This is the existing normed-coefficient realization argument
with its source and target coefficient carriers in different universes.

The proof transports the equality of constant-model and adopted bounded constructibility, the
proper-image hypotheses, and the bounded canonical projection formula. Finite Tor amplitude,
pullback preservation, and tensor closure then supply the existing
`projection_localizing_of_interfaces` helper. That helper uses the adopted two-variable
localizing determination theorem and proves membership of both endpoints. The Qbar argument is
retained; both coefficient cases now use the existing direct bounded-constructible pullback
preservation proof. The existing named projection-interface structures and local proof-valued instance
caches avoid repeating derived-pullback and tensor inference. The representative tensor formula
binds its existing tensor-existence proofs locally, preserving the same proposition by proof
irrelevance. After normalization, the ordinary module tensor structures, `Qh`, and `upperStar`
are locally irreducible, following the published monoidal interface; the coefficient isomorphism uses `Mon.mkIso'` to reuse its existing ring compatibility
proof instead of invoking the automated default proof again. Added private proof imports of `NormedCoefficientRealization` and
`ProperBaseChangeRational`; made the `FieldTensor` proof import expose its private transport helper.
Updated the owning DAG node to record the implemented finite-extension case and its coefficient
transport dependencies. The monoidal helper import is public because its proved constants
now occur explicitly in the public signatures. The textual signature and local proof-context changes are recorded in
`coord/changes/U2-rational-projection-explicit-tensor-proofs.md`. The two mate consumers,
`Sheaf.Paper.ProEtaleProjectionExchangeMaps` and `Sheaf.Paper.TateTwistedProjection`, retain the
same morphism types and values; no adaptation is needed.

Validation: the final artifact-producing compile set passed with exit code 0 and no diagnostics:
`Sheaf.Paper.RationalLocalizingProjectionFormula` and unchanged copies of
`Sheaf.Paper.ProEtaleProjectionExchangeMaps` and `Sheaf.Paper.TateTwistedProjection`.
Each passed the enforced 60-second per-file limit. The delivered source is identical to the
source checked in that set; no profiler options remain. The delivery tool also checks the packet.
Edge cases retain the original theorem: identity and empty schemes, zero
complexes, E = Q_ell, ell = 2, and unbounded localizing inputs. No boundedness hypothesis is
introduced on A or B. The actual canonical mate is identified with the published projection map.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_projectionMate_localizing_finiteExtension`
(node `det-thm-sf-pf-field-localizing`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The proof uses the existing stated dependencies; no claim is made that their entire dependency
closures are axiom-free. The already proved Qbar theorem and normalization helpers are retained.

## No longer needed

Removed the direct proof import `Sheaf.Paper.InverseImageModuleFlat`: this module uses
`upperStar_preservesFlat` from the retained monoidal pullback interface, which already imports
the flatness result for its own proof. This is only direct-import pruning; that module is still
needed transitively and is not withdrawn. No DAG nodes or modules are made unnecessary.
The existing finite-Tor, proper-image, pullback, tensor, bounded projection, and two-variable
determination dependencies are all retained; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The open finite-extension plan required one interface detail: its E
is any finite normed extension in the scheme universe, while several existing preservation and
bounded projection results use a Type-0 finite intermediate subfield of the fixed algebraic
closure. An isomorphism of actual condensed ring objects bridges these presentations, without
changing any coefficient definition or adding a hypothesis. The existing normed realization
statement fixes both field carriers in the same universe; the private proof specializes its
embedding, norm-uniqueness, and sectionwise construction across the two universes instead.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
