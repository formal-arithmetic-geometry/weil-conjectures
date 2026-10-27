## What changed

Restored the V6 scalar-extension packet from the red-build repair archive, preserving
its three module names, DAG node identifiers, concrete constructions and mathematical
route. The assigned theorem CategoryTheory.ringFamilySheafModel_cech is proved by
composing the augmented scalar-Cech comparison with the derived image of the explicit
scalar-extension quasi-isomorphism. Its statement and existing public imports are
unchanged. No adopted source-library declaration is edited.

GlobalSectionScalarExtension constructs the global section ring, evaluation maps,
generated ideal and its images, constant module presheaf, scalar-extension functor,
regular-module map and augmented complex. Every data definition has a complete body.
The adjoint constructions are uniquely determined by their adjunctions, not arbitrary
witnesses of an unproved existence theorem. GlobalSectionRingFamilyBaseChange constructs
the restricted chain map, its naturality, and its sheafified adjoint transpose. It proves
ringFamilyGlobalSectionComparison_quasiIso using the existing ring base-change theorem
and its pure-tensor formula.

The archived build failure names Sheaf.Paper.WeilTensorProduct; its compilation against
the restored packet is checked separately as part of this repair.

## Proved and sorry left

The assigned module has zero holes: CategoryTheory.ringFamilySheafModel_cech closes its
one original hole by complete Lean assembly. The restored packet leaves exactly two
holes, both genuine smaller parts of the argument:

- CategoryTheory.ringFamilyGlobalExtension_to_family in
  Sheaf.Paper.GlobalSectionRingFamilyBaseChange: sheafification preserves the explicit
  sectionwise quasi-isomorphism and its augmentation square (node
  lem-weil-pbc-global-section-ring-family-base-change).
- CategoryTheory.ringFamilyGlobalExtension_cech in
  Sheaf.Paper.GlobalSectionScalarCechModel: identify scalar extension of an arbitrary
  K-flat ordered localization model with the tensor Cech model, with augmentation
  (node lem-weil-pbc-global-section-scalar-cech-model).

GlobalSectionScalarExtension has zero holes. The sectionwise comparison theorem is
proved. Relative to the reverted baseline this closes one hole and restores two smaller
holes (net minus one); it is a decomposition, not a net hole reduction. Relative to the
archived V6 packet the hole count is unchanged. Neither remaining statement is the
assigned theorem with renamed or repackaged hypotheses.

## No longer needed

No mathematical dependency or module is withdrawn. The explicit parent imports of
RingComplexCechBaseChange, RingComplexSemilinearExtension and RingedExtendedCech are
replaced by the scalar-model modules that use these dependencies. Ring-level base change
is used in GlobalSectionRingFamilyBaseChange; the ordered tensor model remains needed
in GlobalSectionScalarCechModel. The parent still directly uses GodementCech and the
independent-coefficients K-flat resolution. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

This is the repair of the reverted V6 packet, not an opportunity to invent a second copy
of its obligations. The archive supplies its original modules and node identities;
those are restored. Its recorded global-build failure is a universe-inference error in
wfTensorRepresentative_exists of Sheaf.Paper.WeilTensorProduct. The repair must check
that importer as well as the assigned file.

The original plan needs both a sheafification bridge and a tensor-coordinate bridge.
The restored declarations separate them: the former applies to arbitrary functorial
families, the latter to arbitrary K-flat ordered models without family or Godement data.
The constructions and proof descriptions include the empty site, empty list, zero and
repeated generators, and zero section rings. No extra nonvanishing or flat-map assumption
has been introduced.

## New nodes

Restored from the archived V6 packet, preserving their identifiers:

- def-weil-pbc-global-section-scalar-extension, implemented without holes.
- lem-weil-pbc-global-section-ring-family-base-change, with a proved sectionwise
  comparison and the remaining sheafification theorem.
- lem-weil-pbc-global-section-scalar-cech-model, the augmented tensor-coordinate step.

Their search records have been refreshed using this session's actual searches. The
parent proof, proof dependencies and origin now describe the restored assembly.

Change record: coord/changes/X7-functorial-ring-cech-red-build-repair.md.

## Forced adaptations

Sheaf.Paper.ExtendedCechCompletionModel is unclaimed. Its unchanged source exceeded the
60-second file limit at 62.2 seconds. A proved private generic compose_three_squares
lemma replaces six concrete rewrite/simp lines in completion_unit_natural. It uses the
existing hη', ha' and hc equations and preserves every public statement and definition;
the adapted consumer compiles in 42.9 seconds.

Sheaf.Paper.WeilTensorProduct remains unchanged in this delivery. Its archived universe
error no longer reproduces, but its unchanged source still exceeds the 60-second limit
under the current elaborator. No unverified consumer edit is included.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
