## What changed

Restored the assigned quarantined module and preserved the exact statement of
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_structural_transport`.
Its proof now derives the point-map equation from `Over.w`, forms the adjunction
between the two actual point pullbacks using the inverse-composition comparisons of
`isomorphismFieldTransport`, composes the displayed ordinary adjunctions, and applies
`Adjunction.rightAdjointUniq`. The specified `Family.unit_spec` identifies the pulled-back
unit; applying the structural right functor and `rho.mapIso` finishes the original claim.
No native adjunction is assumed. Only proof imports are added to the item.

The remaining geometric left comparison is isolated in
`Sheaf.Paper.ConstructibleCompactSupportTargetIso`. It concerns the compact-support left
functors under an isomorphism of targets. It has no native category, realization, exceptional
image of a unit, or normalized point-unit conclusion. This is the compact-support part of
Step 2 of the original plan, not the original statement under another name.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_structural_transport`
(node `lem-sf-native-exceptional-structural-transport`): one of one item holes.
The private point-pullback adjunction is proved, with no admitted steps.

Added one hole in the new public theorem
`WeilConjectures.ConstructibleExceptionalCoefficients.constructible_compact_support_target_iso`
(node `lem-sf-constructible-compact-support-target-iso`). Its module contains exactly this
one theorem and one `sorry`, with a source and full proof in words. No item holes remain.
This delivery is a decomposition: one hole closed, one strictly geometric left-comparison
hole added, net zero. It does not claim that the underlying geometry is now sorry-free.

Validation: both delivered modules compiled successfully one file at a time in import
order. The compact-support statement took 9.9 seconds and the completed item proof
16.9 seconds. Profiling options used to diagnose elaboration have been removed from
the final packet; deliver3 performs its final compilation and preflight. No existing
public signature, visibility, definition body, instance or import has changed.

## No longer needed

No public imports, existing declarations, or unit steps are removed. No modules are withdrawn.
The item no longer needs a separate proof about right adjoints or point-unit transport:
those steps are now real Lean using existing interfaces and Mathlib.
`lem-sf-constructible-exceptional-adjunction-coefficients` and
`prop-compactification-coherence-detailed` are needed below the new compact-support lemma;
they are not pruned from the mathematical route. The new proof dependency is that lemma,
plus the existing isomorphism-field-transport and normalized-realization interfaces.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was found. The archive was checked before restoration;
the current server queue assigns stage-3 proof work, and no item-specific build-error file
exists. Its rework row records quarantine through CommonStagePullbackRepresentativeLinearity.
A compile of the restored unchanged source succeeded, but that alone was not treated as
completion. The original DAG's ordinary compact-support factorization was a prose step,
not an existing theorem that directly compares these two arbitrary normalized systems.
The new node makes precisely that remaining left-functor step explicit.

Edge checks: the target-isomorphism lemma has the correct variance (F_f ≅ F_g ⋙ e*).
For e=id it reduces to compactification/system independence. For empty X both functors
are zero. The item composes G_f ≅ (e⁻¹)* ⋙ G_g, so its unit comparison is supplied by
R.unit_spec for e.symm, in the required direction. There is no assumption that finite
reductions are faithful on derived morphisms and no object is chosen from an arbitrary
unproved existence theorem. The unit record has no realized steps changed by this delivery.

## New nodes

`lem-sf-constructible-compact-support-target-iso` records compact-support covariance under
a target isomorphism on the actual common-stage categories. Its proof passes through
finite etale-origin compactifications, the full normalized integral tower, rationalization,
and coherent common-field descent. The original item proves the separate right-adjoint,
unit, and realization steps from it. No existing interface changes or change records.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
