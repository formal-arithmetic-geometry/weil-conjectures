## What changed

Repair of red-build job 4ffeba5b1c06aaa9 / reverted C5 landing fa0cd052fa.
Restored the proved normalized ringed direct-image and final-site regular-unit
mate arguments from the repair archive. Preserved PushNormalized verbatim.
Restored internalPullOplax_eq_canonical with its original monoidal_upperStar
right-hand side, converting explicitly from the efficient condensed structure
by the existing proved equality. The reported failing consumer and the two
other users therefore retain their original proofs and signatures.

The proved new companion is
Sheaf.Algebra.Category.ModuleCat.Sheaf.FinalRingedUnitMate, with theorem
SheafOfModules.normalized_unit_mate_isIso. It compares the specified unit adjunct
with Mathlib's canonical regular-unit map via leftAdjointUniq. Finality supplies
invertibility; no arbitrary witness or unproved construction is selected.

Proof-only imports use the normalized ringed pairing, private tensor-comparison
API, and the existing TraceBaseChangeFirst internal pairing API. The recovered
local elaboration improvements keep the same strong monoidal maps and proof
irrelevant invertibility instances. Profiling exposed repeated kernel conversion
when assembling normalized existence and uniqueness at concrete coefficient types;
a proved abstract conjunction-to-ExistsUnique helper avoids that repeated work.

Change record: coord/changes/C4-section-module-canonical-mate-repair.md.

## Proved and sorry left

Closed two of the three original holes:
- AlgebraicGeometry.ProEtale.ModuleRingedComparison.pushNormalized_existsUnique
  (lem-pd-section-push-normalized-exists-unique).
- AlgebraicGeometry.ProEtale.ModuleRingedComparison.pull_eta_isIso
  (lem-pd-section-pull-eta-isiso).

One original hole remains:
- AlgebraicGeometry.ProEtale.ModuleRingedComparison.pull_delta_isIso
  (lem-pd-section-pull-delta-isiso).

Added holes: zero. Split off: zero. The new general unit-mate theorem is proved.

## No longer needed

Removed direct proof imports
WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
and Sheaf.Paper.InverseImageModuleFlat. Existing TraceBaseChangeFirst declarations
supply the internal pairing and flatness API instead. These modules may remain
transitive dependencies elsewhere, so no global module withdrawal is claimed.

The section-unit proof no longer uses the tensor-mate construction or canonical
scalar-insertion formula: Mathlib PullbackFree plus adjunction uniqueness is
sufficient. Removed its dependencies on lem-pod-canonical-module-adjunction-unit
and lem-pd-ringed-tensor-adjunction-mate from that node. The tensor obligation
still retains its own dependencies. No unit-level route is bypassed and no
source-library declaration is removed. Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The reverted delivery claimed consumer adaptations were unnecessary, but changed
the private canonical comparison's right-hand side. The global build correctly
reported a rewrite failure in CompositeModuleOplaxMate at the new condensed
structure. This packet keeps that private theorem's original statement, rather
than relying on definitional equality of propositionally equal strong structures.
CompositeModuleOplaxMate compiled successfully against the repair.
RestrictedCoefficientMateProjection also type-checked, but its unchanged proof
reported unused/unreachable tactic warnings at lines 319–320 and exceeded the
60-second limit (63 seconds). It is not modified or included in the delivery.
SectionDerivedTensorNormalization also type-checked without errors or warnings,
but its unchanged source took 91 seconds and failed the timing gate. Neither
optional consumer is included in the packet; the required failing consumer
CompositeModuleOplaxMate compiled successfully. The independent global build
remains authoritative for downstream timing.

## New nodes

lem-pd-final-ringed-unit-mate-isiso records the fully proved final-site regular-unit
adjunct theorem recovered from the reverted delivery. It is a general unit-map
argument, strictly separate from the unresolved tensor-map invertibility theorem.
No new sorry is introduced. The zero-ring and empty-scheme cases satisfy the same
argument whenever the declared site hypotheses hold.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
