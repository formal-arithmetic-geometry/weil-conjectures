## What changed

Restored the assigned Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
from its exact quarantine path. Repaired
AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison:
the source-library tensor counits restored by synchronization are only propositionally
equal to the retained generic constructions. Private helpers prove equality of the
complex tensor comparison, the homotopy counit, and both derived counits. Derived
uniqueness then identifies the original lift with the generic canonical comparison.
All existing public declaration signatures, construction bodies and imports are preserved.
Four generic definitions are now irreducible: tensorCounitOfNatTrans,
homotopyTensorCounit, homotopyTensorLeftDerivedCounit and leftDerivedTensorUnitIso.
Their existing component/compatibility lemmas provide the equations used in proofs;
the proofs explicitly unfold the constructions where required. This controls expensive
incidental reduction without changing any constructed mathematical object. The two
tensor-counit presentations are identified by a generic private theorem, avoiding
repeated elaboration of the concrete module tensor. A private
lift-congruence lemma transports the derivability instance together with its counit,
so no dependent rewrite assumes definitional equality. The representative calculation
is proved generically, then applied to arbitrary concrete homotopy objects by congruence;
the concrete derived-property witnesses are supplied explicitly to avoid repeated inference.
The generic lift lemma now follows directly from the component formula for the canonical
comparison: postcompose with the inverse homotopy tensorator, cancel it, and apply the
derived universal property. Its former general-purpose transport chain is unnecessary. No upstream
file is changed. The node's primary Lean attachment now names the retained compatibility
lemma rather than the monoidal instance that synchronization moved back upstream.
The node retains all three declared dependencies and its unit route.

Change record: coord/changes/H1-restore-derived-module-monoidal.md.

Validation: the final repaired module compiles cleanly in 44.9 seconds through
lcompile.py. Before the transparency adjustment, an import-order run compiled the module in
58.1 seconds and its unchanged archived consumer Sheaf.Paper.OpenPullbackGenerators
in 4.4 seconds. After the transparency adjustment, the unchanged consumer compiled
against the final module in 3.0 seconds. The consumer was included
temporarily for that check and is not part of the delivery. A prior version passed
delivery preflight but a subsequent required compile timed out at 60 seconds; the
representative calculation and counit transports were refactored, the generic transport
chain was pruned, and reducibility was controlled to reduce checking cost. No limit or required check was changed.

## Proved and sorry left

This is a zero-hole restoration repair: 0 original textual sorries, 0 closed, 0 added,
0 split off, 0 left. Repaired the complete proof of
AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison.
Every new private helper is proved. No existing upstream proof obligation is counted as
closed. The imported upstream module still has its independently assigned proof holes.

## No longer needed

No import, DAG node, dependency or module is withdrawn. Removed the unused private
helpers mapCochainComplexDesc_comm and isIso_leftDerivedBifunctorLift, plus the private
isIso_tensorCounit_app_app, isLeftDerivedFunctor₂_tensorCounit,
isIso_homotopyTensorCounit and isLeftDerivedFunctor₂_homotopyTensorLeftDerivedCounit
chain. Also removed leftDerivedLift_eq_of_inverse,
homotopyTensorLeftDerivedCounit_eq and homotopyTensorComparison_hom_inv: the generic
lift is identified directly by the canonical comparison's component formula and derived
uniqueness. The repair transports the existing upstream derived universal-property instance
through the proved counit equality, so rebuilding that instance from flat resolutions
would duplicate work. These removals affect no public declaration or DAG dependency.
The summand formula helper remains needed by the new explicit comparison proof.
Three repeated synthInstance.maxHeartbeats wrappers before an old heading were obsolete
and removed. No public declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The module was absent because it was quarantined, not because it was mathematically
unneeded. coord/rework.tsv records its actual compile failure. The archived proof
assumed that the concrete right counit was definitionally the generic right counit;
this is false after the upstream sync. Equality must be proved through the tensor
comparison on complexes and the homotopy quotient. The node's old primary declaration
was also stale: monoidal_leftDerivedUpperStar is declared upstream, rather than in the
archived extra module. The attachment is corrected without deleting any dependency.

Searches: LeanFinder on left-derived tensor comparison/counit uniqueness returned Day
convolution and external-product tools, with no specialized match. Loogle did not know
the project-specific leftDerived₂_ext name. Launcher grep gave no match; direct source
search found the already-proved leftDerived₂_ext, leftDerived₂_fac,
homotopyTensorLeftDerivedLift_eq and mapCochainComplexμIso summand formula, which are used.
The argument is uniform in all schemes and coefficients, including empty schemes and
the zero coefficient ring; no new hypothesis is imposed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
