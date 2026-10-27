## What changed

Proved `restrictedAffineDiagonalVectorIntegration` from the compact-support trace
normalization step `affineVectorTracePresentation`, in a new module. The original
statement and both public imports are preserved. All added imports are private proof
imports. No existing module other than the item is changed.

The implementation supplies proved private lemmas for adjunction transposition,
restriction of an orientation square, and the identity Tate pullback. The latter is
derived from coefficient composition, the derived pullback unit law and cancellation.
It then restricts the transposed trace equation, pastes the two section exchanges,
applies the ordinary/pro-etale comparison and cancels sourceComparison. Private
`import all` access to the existing limit and universe-shrink constructions permits
the required definitional identifications without changing global transparency options.
Local reducibility attributes affect only elaboration in this proof file.

Validation: `lcompile.py --all` compiled both delivered modules without warnings
(exit code 0). The existing theorem signature was compared byte for byte with the
shared source and is unchanged; both Lean files satisfy the 100-character line limit.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalVectorIntegration`
(node `lem-pur-restricted-affine-diagonal-vector-integration`).

Added one hole:
`WeilConjectures.PurityFiniteSetting.affineVectorTracePresentation`
(node `lem-pur-affine-vector-trace-presentation`). This is the compact-support trace
normalization step, before taking any adjunction mate, section restriction, DNC map or
site comparison. It is not the original conclusion under a new name: the delivery
proves the categorical transposition, coefficient, section-pasting and site-comparison
parts of the argument. In particular, the new statement contains no section, DNC
comparison, orientation adjunct or pro-etale comparison. This is a decomposition: one original hole closed, one added,
net zero. The item module has zero remaining holes. The proved private helpers are
`integration_mate_square`, `restrict_orientation_square`, `coefficient_id` and
`affine_section_presentation`.

## No longer needed

No existing public import is removed and no module is withdrawn. No whole-library
pruning is claimed.

The original proof's direct use of
`lem-pur-vector-zero-section-integration-base-change`
(`Sheaf.Paper.VectorZeroSectionIntegrationBaseChange`) is unnecessary: the proof
transposes the trace equation itself, including its coefficient factors.
`restrictedAffineDiagonalDncVectorCoordinates`, the geometric existence theorem in
`Sheaf.Paper.RestrictedAffineDiagonalDncVectorCoordinates`, is not used. Its module
stays a public import because it also defines `vectorModelSectionComparison`, which
occurs in the unchanged statement.

Affine translation invariance, vector frame normalization and the Cartesian normalized
vector trace remain needed below the new trace lemma. They are not claimed as pruned.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy or counterexample was found. The identity coefficient
comparison is not assumed to be definitionally the identity: `coefficient_id` derives
its equality with the canonical pullback unit from ordered coefficient composition
and the derived pullback unit law.

The plan omitted the Lean
trace equation joining the existing normalization and translation declarations to an
arbitrary affine scheme presentation of the vector bundle. The new node isolates
that first step. Existing frame theorems concern linear charts, whereas the assigned
statement quantifies over arbitrary scheme isomorphisms preserving projection and
section. The proof documents how to translate the section and compare with the canonical
free vector bundle in its standard frame, using the existing nonlinear
zero-preserving Cartesian vector trace compatibility.

The new statement was checked mathematically at rank zero, on the empty base and for
the zero coefficient ring; its proof uses the same unit identities there.

A read-only traversal of the current shared DAG also found the pre-existing cycle
`lem-pc-ring-hom-extension-differential` →
`lem-pc-ring-hom-extension-differential-adjacent` →
`lem-pc-ring-hom-extension-differential`. This delivery changes neither node. A separate
reachability check verified that none of the 15 added dependency edges lies on a cycle.

## New nodes

`lem-pur-affine-vector-trace-presentation`, in
`Sheaf.Paper.AffineVectorTracePresentation`, records the compact-support trace
normalization for an arbitrary affine vector presentation. Its docstring gives the
translation, standard free frame, normalized vector trace and exchange-pasting proof.
The parent node's proof and proof dependencies follow the implemented reduction.
There are no change records because no existing interface changes.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
