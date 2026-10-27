## What changed

Repair of returned head `c8524035f12`: removed `set_option warn.sorry false` from the four delivered modules. The current hole ledger treats the field name `warn.sorry` as a hole token, so that option caused the completed-restriction theorem hole to be reported as unattributed. The theorem remains a named public theorem with its original `:= by sorry` body.

Replaced the hole in `WeilConjectures.compactSupportSystemEvaluationCoherence`
with the composition of three strictly smaller supporting results. The theorem's
signature, all thirteen existing definitions, their visibility and public imports
are unchanged. No other existing Lean module is edited.

The parent proves the scalar-adjunction mate-transpose calculation in
`restriction_mate_transpose`: the unit mate equation, coefficient-square naturality
and the inverse Hom-equivalence identify the transposed extension-form arrow with
the restriction-form arrow. It also proves `evaluated_tower_square`, which pastes
the completed-restriction and direct-image evaluation squares and cancels the open
evaluation with its inverse inside the specified target transition. This constructs
the actual canonical `theta`, rather than postulating a tower comparison.

The general semilinear calculus does not identify its abstract geometric-operation
fields definitionally with the separately constructed functors in the diagram.
`compactSupportSystemNormalizedPresentation` isolates that specialization and its
section/K-injective normalizations and four adjunction equations. It makes no
assertion about tower transitions. `compactSupportDirectImageRestrictionTransition`
is a restriction-form square for arbitrary systems on Z; it uses neither j nor
completed scalar restriction in its conclusion. `compactSupportCompletedRestrictionTransition`
is a transition equation for arbitrary coefficient systems on one scheme and uses
neither p nor j. Their ordinary/derived sources and complete proof plans are in
the new docstrings and nodes.

Validation: all four modules compiled remotely. A profiler run of the parent
completed in 7.0 seconds, with no slow declaration; the profiler options were removed.
Long-line warnings in two docstrings were corrected. Edge cases checked on paper:
zero systems and zero transitions; j=id and p=id; m=n; empty schemes; unbounded systems;
and nonflat coefficient quotients. The transition arguments require no preservation
of K-injectives by coefficient evaluation and no cartesianness hypothesis.

## Proved and sorry left

Closed the original body hole by decomposition:
`WeilConjectures.compactSupportSystemEvaluationCoherence`
(node `lem-trf-compact-support-system-evaluation-coherence`). The parent module
has zero remaining holes. The two private categorical helpers have complete proofs.

Added three named theorem holes, each in its own module:

- `WeilConjectures.compactSupportSystemNormalizedPresentation`
  (`lem-trf-compact-support-normalized-presentation`).
- `WeilConjectures.compactSupportDirectImageRestrictionTransition`
  (`lem-trf-direct-image-restriction-transition`).
- `WeilConjectures.compactSupportCompletedRestrictionTransition`
  (`lem-trf-completed-restriction-transition`).

This is one original hole decomposed into three supporting holes, not an
unconditional proof or a positive net hole reduction. No axiom or hollow definition
is added, and no existing theorem is weakened.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`.
- `Sheaf.Paper.SemilinearDerivedSections`.

The first four and the semilinear calculus remain dependencies of the normalized
presentation lemma; coefficient-sequence localization remains a dependency of the
two transition-square lemmas. Thus none of these mathematical nodes or modules is
claimed globally unnecessary. No module is withdrawn. The parent node now records
the three supporting lemmas and the existing diagram in its proof dependencies;
the new nodes retain the relevant original dependencies. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG accurately describes the intended mathematical argument, but its stated
semilinear theorem has abstract geometric fields, while this item uses separate
canonical pro-etale functors. Specializing those fields requires actual transport
and normalized derived comparisons; applying the abstract existence theorem alone
does not fill this item's hole. The supporting presentation theorem records that
missing specialization explicitly.

The blueprint path `prop-trf-rational-frobenius-integral-model.proof.md` in the old
item docstring is absent from `literature/blueprint/latest`. The available current
trace-transport unit and Zheng Construction 4.1 / Lemma 4.10 were read; the new nodes
cite the obtained literature and the existing coherence proof's precise steps.
No old snapshot was used and no unit statement or proof route was changed.

## New nodes

`lem-trf-compact-support-normalized-presentation` supplies the actual normalized
operation presentations, before proving any transition comparison.

`lem-trf-direct-image-restriction-transition` supplies the restriction-form direct-image
square on arbitrary systems; the parent's proved mate lemma converts it into the
specified scalar-adjunction transpose.

`lem-trf-completed-restriction-transition` supplies the exact coefficient-restriction
transition square on arbitrary systems on one scheme. The parent composes it with
the preceding square and the open evaluations using a proved categorical calculation.

No shared definition/interface repair and no change record or forced adaptation
is needed.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
