## What changed

Proved both preservation clauses in `Sheaf.Paper.WeilVerdierPreservationStrata` by
specializing the existing source-library perfect-field Verdier preservation theorem.
The coefficient helper proves the invertible-exponent hypothesis with exponent `ell^n`;
the boundedness helper compares the two existing constructibility predicates and their
cohomological bounds. The qualitative theorem chooses a finite dimension bound and
applies the quantitative theorem. No declaration signature or public definition changes.
The source-library implementation realizes the same node and the same stratum-duality
argument, so no new theorem or new hole is needed. The node proof now describes this
specialization and records only its additional dependencies; its use of an already
implemented version of itself creates no DAG or Lean import edge to itself.

Proof imports added: `WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation`,
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`,
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.

## Proved and sorry left

Closed both original holes (2 of 2):

- `WeilConjectures.verdier_preservation_strata`.
- `WeilConjectures.verdier_preserves_boundedConstructible_finiteTor`.

Added zero holes and split off zero statements. No `sorry` remains in the delivered
module. All four private helpers are proved. The ambient dualizing-complex construction
is byte-for-byte unchanged. This uses the existing named dependencies of the library;
it makes no claim that their entire transitive axiom closure is already finished.

## No longer needed

Removed these direct proof imports, whose separate statement-module realizations are
not needed when specializing the existing source-library theorem:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`.
- `WeilConjectures.SixFunctors.Etale.Derived.Triangulated`.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`.
- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`.
- `Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing`.
- `Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor`.
- `Sheaf.Paper.SfHomTriangulated`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.Paper.PbcActualScalarPullback`.
- `Sheaf.Paper.StratumAmbientHom`.
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`.
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`.
- `Sheaf.Paper.DirectImageTorAmplitude`.
- `Mathlib.CategoryTheory.Adjunction.Basic`.
- `Mathlib.CategoryTheory.Adjunction.Unique`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

Removed one duplicate public import of
`WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`; its exported import
set is unchanged. The old separately expanded proof dependencies below are no longer
additional tasks needed to implement this wrapper. Their mathematical ingredients that
occur in the existing source proof remain dependencies of that implementation; this is
not a claim to remove them from other parents or from the whole library:

- `def-pur-derived-internal-hom`.
- `def-weil-pbc-extension-by-zero`.
- `lem-amb-etale-adjoint-locality`.
- `lem-amb-unbounded-compact-support-comparisons`.
- `lem-cat-right-adjoint-composition`.
- `lem-exc-closed-ambient`.
- `lem-kun-derived-tensor-triangulated`.
- `lem-kun-flat-bounded-tor-amplitude`.
- `lem-kun-tensor-unit`.
- `lem-sf-derived-homology-long-exact`.
- `lem-sf-etale-direct-image-vanishing`.
- `lem-sf-etale-smooth-stratified-ctf`.
- `lem-sf-hom-triangulated`.
- `lem-sfb-finite-type-composition-base-change`.
- `lem-weil-pbc-closed-immersion-proper`.
- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-weil-pbc-locally-noetherian-quasi-separated`.
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`.
- `lem-weil-pbc-open-immersion-etale`.
- `lem-weil-pbc-proper-fp-permanence`.
- `lem-weil-pbc-qc-open-immersion-finite-type`.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-weil-pbc-separated-cancellation`.
- `lem-weil-stratum-ambient-hom`.
- `lemma-constructible-flc-serre`.
- `thm-amb-etale-exceptional-adjoint`.
- `thm-asd-smooth-tensor`.
- `thm-constructible-serre`.
- `thm-nagata-compactification`.
- `thm-sf-direct-image-tor-amplitude`.

The definition of derived internal Hom and the ambient exceptional adjoint remain
statement dependencies, even though they need no separate new proof step here. The
unit statement and its realized steps are not changed.

## Where the brief, the DAG or earlier work was wrong

The planned independent five-step proof duplicates an existing source-library theorem
with exactly the required interval over any perfect field. The needed work is the
coefficient-exponent verification and conversion of the constructibility and Tor
predicates. A broad `simp` when lifting the quotient annihilation equality caused the
initial slow compile; `ULift.down_injective hkill` avoids unfolding quotient arithmetic.
The resumed direct specialization hit the kernel timeout when converting the concrete
lifted coefficient category. Keeping the preservation calculation polymorphic in the
coefficient ring, then specializing through a private ULift helper, avoids that expensive
conversion. Both helpers have complete proofs; no module or unproved statement was split
off. The retained successful profiler run compiled the item in 5.3 seconds. The resumed
2026-10-19 delivery dry run also passed compilation and the axiom probe, then requested
a change record for the local instance-priority command. The delivery now includes
`coord/changes/T4-verdier-preservation-local-ring-priority.md`, documenting that command,
its non-exported scope, the unchanged public signatures and all transitive consumers.
No statement dispute or mathematical change was necessary. Empty schemes and empty
intervals use the existing theorem without a nonemptiness or ordered-endpoint assumption.

Resumption validation (2026-10-19): the earlier dry run printed
`OK (dry run): commit 6f2f70a9c0 compiles and passes the preflight; nothing pushed`.
The subsequent interrupted push had no surviving process and a read-only remote branch
query found no delivery branch. A fresh dry run reached the 60-second compile timeout;
a profiler copy of the unchanged proof subsequently compiled in 44.0 seconds. The
profile reports 0.804 seconds of kernel type checking, 2.70 seconds of tactics and
6.22 seconds of linting. No timeout limit or proof-checking option was changed.

The retained direct-consumer sweep compiled the item, then the original sources of
`Sheaf.SixFunctors.FiniteDualitySiteComparison` (41.5 seconds) and
`Sheaf.Paper.FiniteStageVerdierBiduality` (26.2 seconds).
`Sheaf.SixFunctors.FiniteDualizing` then reached the 60-second limit; the remaining
six direct consumers were not tested by that sweep. This is partial consumer coverage,
and the timeout has not been attributed to this delivery. No consumer source is changed.
The public import set, existing signature texts and dualizing-complex definition remain
unchanged; the local instance priority is not exported.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
