## What changed

Proved `AlgebraicGeometry.Etale.tensorProjectionAdjunct` with its existing signature.
The private categorical calculation expands the projection-map mate, uses compatibility
of the canonical pullback comparison with symmetry, applies naturality, cancels the
opposite symmetries, and combines the two tensor maps. A general coefficient-category
specialization keeps these categorical operations explicit before passing to modules.

The compatibility is the already proved
`AlgebraicGeometry.Etale.derivedPullback_tensorSymmetry`, now present in the current
repository. Import its module privately. No existing definition or public interface
is changed, and no existing consumer needs adaptation.

Completed `Sheaf.SixFunctors.DerivedTensorSymmetryInvolutive` without any sorry.
Its proof checks the two Koszul swaps on each cochain tensor summand, descends the
identity to the homotopy category, and uses uniqueness of derived bifunctor lifts
to cancel the fixed canonical derived symmetries.

Validation: the two production modules compile together through `lcompile.py --all`
without errors or warnings (11.2 seconds for the cancellation helper and 16.6 seconds
for the item). No heartbeat or recursion limits are changed. The helper uses a private
predicate on the entire natural isomorphism so specialization does not repeatedly
unfold the component tensor instances; the predicate is an explicit definition,
and every theorem establishing it is proved.

The required `deliver3.py --no-push` check passes: temporary commit `014bed85d9`
compiled and passed server preflight, with review class CODEX for the new proved
helper, node updates and documented declaration-local attributes. The successful
log is `scratch/dry-run-resume-checkout.log`. Earlier launcher checkout timeouts
were transient; no delivery was pushed by those failed attempts or by the dry run.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Etale.tensorProjectionAdjunct`
(node `lem-amb-tensor-projection-adjunct`).
Also proved the retained helper `AlgebraicGeometry.Etale.derivedTensorSymmetry_involutive`
(node `lem-amb-derived-tensor-symmetry-involutive`). All private helpers are proved.
There are zero remaining sorry declarations in the two delivered modules and zero
holes added. The new helper is fully proved, with no split-off proof obligation.

## No longer needed

Removed the proof imports
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients` and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`. Their nodes
`lem-weil-pbc-site-derived-tensor-descent` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are no longer direct dependencies
of this proof: the existing pullback-symmetry theorem and bifunctor API provide the
needed consequences. Their obsolete top-level tool approvals are withdrawn.

Removed redundant proof imports `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
and `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
the retained public imports supply their declarations. Added proof imports of
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorSymmetry` and the proved cancellation
module. No unit statement or realized proof step is bypassed. These dependency
removals do not assert that other target branches stop using them.

The retained attempt to alter `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`
is unnecessary: W4's already-landed interface and compatibility theorem suffice.
No symmetry-definition change or component-equation addition is part of this delivery.
The proof-elaboration change record is described below. Removed the private compatibility calculation that used the
upstream braided-pullback theorem directly.

## Where the brief, the DAG or earlier work was wrong

The retained report claimed successful compilation for a different revision and was
out of date. The required initial dry run completed without pushing and exposed an
unavailable `SymmetricCategory (DerivedCategoryModule Λ X)` instance in the retained
short cancellation proof. Restored its full signed cochain and derived-lift proof.

The current source contains the exact compatibility theorem
`derivedPullback_tensorSymmetry`, absent from the initial proof plan. This makes the
attempted symmetry-packaging changes unnecessary. The sandbox keeps those attempts
in scratch; they are excluded from the delivery. The diagnostic print-only Probe.lean
was also moved out of the delivery source tree.

## New nodes

`lem-amb-derived-tensor-symmetry-involutive` is retained from the earlier attempt and
is delivered fully proved. On each cochain tensor summand the coefficient symmetry
cancels and the two signs multiply to one. Quotient functoriality gives the homotopy
identity, and uniqueness of derived lifts gives the canonical derived identity.
It applies to the empty scheme, zero objects and the zero coefficient ring, with
no boundedness or characteristic restriction. Its DAG proof describes the Lean proof.

The conservative attribute-command interface diagnostic is documented in
`coord/changes/X3-tensor-projection-proof-elaboration.md`. The instance settings are
scoped to individual declarations with `in`, so consumers retain the same instance
environment. No forced adaptations are needed.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
