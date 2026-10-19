## What changed

Proved AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_constructible with its existing
signature and ClosedSupportConstructibleAssertions definition unchanged. Four fully proved
private helpers install conditional Serre triangulatedness, transport constructibility through
the exact formal pullback, combine the normalized localization triangle with direct-image
preservation, and specialize the direct-image application over the field with a generic
coefficient parameter. The existing formal support theorem already gives the actual derived counit and
the fiber isomorphism. Both specified coefficient choices use their canonical ring structures.
No new public declaration, definition, statement, or public import is introduced.
The local attribute commands are documented in
coord/changes/A7-closed-support-constructible-elaboration.md; preflight requested this
record because its static command check treats local attributes as interface changes.

The node proof and dependencies now follow this proof. The unit's localization, open-image,
and closed-pullback steps are preserved. The final module compiled without warnings in 16.8 seconds
through lcompile.py. Private irreducibility attributes prevent expansion of large structural
instances during elaboration; there is no increased timeout or heartbeat limit.

## Proved and sorry left

Closed 1 existing hole: AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_constructible
(node det-prop-closed-adjoint-constructible-support). Added 0 holes; 0 holes remain in the
item module. All four private helpers have complete proofs. The proof uses existing named
inputs, including formal_closed_support_adjunction and
boundedConstructible_rightDerivedLowerStar_obj, whose remaining proofs are separate work.
This is a proof from existing declarations, not a decomposition into new holes.

## No longer needed

Removed these private proof imports from the original module:

- Mathlib.RingTheory.Noetherian.Defs
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
- Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit
- Mathlib.CategoryTheory.Functor.Derived.Adjunction
- Mathlib.CategoryTheory.Adjunction.FullyFaithful
- Sheaf.CategoryTheory.OrthogonalTriangleCounitNormalization
- Sheaf.Paper.CoefficientHeartTriangulated
- Sheaf.Paper.CondensedModuleDerivedPushpull
- Sheaf.Paper.FormalClosedSupportDerived
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

The original public imports remain as the module's existing interface. New private imports
are CondensedConstructibleSerre, ProEtaleModuleConstructiblePullback,
ProEtaleModule.IsoClosed and Triangulated.Subcategory. No dependency is asserted globally
unreachable; the following original proof dependencies are unnecessary for this item:

- sk-def-sfb-dc-setting
- def-weil-pbc-noetherian-ring
- pqf-def-locnoeth
- lem-weil-pbc-noetherian-open-subscheme-noetherian
- lem-weil-pbc-proetale-immersion-limit-preservation
- det-lem-formal-closed-support-derived
- lem-weil-pbc-proetale-ringed-open-closed
- lem-weil-pbc-proetale-ringed-closed-counit
- lem-sc-derived-adjunction-from-underived
- sk-def-sfb-module-derived-pushpull
- lem-weil-pbc-adjunction-counit-iso-right-fully-faithful
- lem-sfb-orthogonal-triangle-counit-normalization
- lem-sfb-dc-upper-star-preserves
- det-cor-coefficient-heart-ii-triangulated

The separate orthogonality/counit normalization and ringed-site cancellation argument is
already packaged in formal_closed_support_adjunction. Its output also contains the fiber
formula, so the separate FormalClosedSupportDerived interface is unnecessary. Pullback is
handled directly on cohomology by the proved module-pullback theorem, rather than through
an additional left-derived comparison. The constant-model triangulation theorem concerns
a different predicate; the conditional Serre theorem gives precisely the predicate needed.
Noetherianity of Z and U is unnecessary in this proof because pullback and isomorphism
closure do not require it. Removed obsolete tool_uses entries that are no longer proof
inputs; retained their original order for the surviving entries.

## Where the brief, the DAG or earlier work was wrong

The old plan cited constantModelBoundedConstructible_field_triangulated for the internal
stratified-local-finite-presentation boundedConstructible predicate. These are different
predicates. The finite-field and algebraic-closure constructible Serre declarations plus
isTriangulated_boundedConstructible_of_serre supply the required closure without changing
any statement. These are generic tools; they do not replace the unit's localization route.

As in the landed RationalClosedSupportConstructible proof, the existing
formal_closed_support_adjunction declaration realizes the recorded closed-support
adjunction/triangle node at the formalSupportPullback/formalClosedSupport constructions
used by this item. The node's primary Lean attachment currently lists the parallel
supportPullback/closedSupport interface. This delivery uses the existing formal realization,
without copying or changing either support construction.

Earlier diagnostic runs encountered 60-second elaboration timeouts. Explicit coefficient,
base-field, and scheme-over-field structural instances resolved them; all final code
compiles with the default resource limits. Interrupted provider calls started no delivery.

On provider-error resumptions, launcher metadata changed the reference clock: the first
observed .budget.start was 1792426014.239195 and the latest was 1792438007.8772078.
No attempt identifiers were supplied in those continuation messages. The worker did not
edit .budget or restart its deadline; the original sandbox and item were retained.

The first preflight required the local-attribute change record, now supplied. A later
dry run encountered a compile timeout before preflight. Factoring the existing direct-image
application into a fully proved private helper with a generic coefficient parameter removed
concrete-coefficient inference from this application. The final module compiled cleanly
in 16.8 seconds. No mathematical statement or definition changed.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
