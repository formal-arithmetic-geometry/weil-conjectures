## What changed

Proved AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_constructible with its
signature unchanged. The proof uses the kernel-normalized support adjunction and its
counit-unit distinguished triangle, exact-pullback comparison by adjoint uniqueness,
open direct-image finiteness, weak Serre triangulated closure, and the closed fiber
comparison. The same private argument applies to both finite E and algebraic-closure
coefficients. All private helpers are proved, and no data is selected from an arbitrary
existence theorem.

The repair removes the returned dependency adaptation entirely. Current main already contains
C1's landed universe-polymorphic `formal_closed_support_adjunction.{u, w}`. The proof now
specializes that existing theorem explicitly at `w = u + 1`. The delivery contains only
the assigned Lean module and its updated proof-plan node, with this report. No signatures,
public imports, definitions, dependency modules, or dependency nodes are changed.

Updated the item's DAG proof and proof_deps to the actual argument. No new modules or
nodes were introduced.

## Proved and sorry left

Closed the sole assigned hole:
AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_constructible
(node det-prop-closed-adjoint-constructible-support). Proved 1 of 1 assigned sorries;
0 split off; 0 added. No sorry remains in ClosedSupportConstructible.

The proof is from existing stated dependencies, some of which still depend on sorry;
it does not establish an axiom-free proof of the whole import closure.

## No longer needed

Removed proof imports (15):
Mathlib.RingTheory.Noetherian.Defs;
Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated;
Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation;
Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation;
Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions;
Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed;
Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit;
Mathlib.CategoryTheory.Functor.Derived.Adjunction;
Mathlib.CategoryTheory.Adjunction.FullyFaithful;
Sheaf.CategoryTheory.OrthogonalTriangleCounitNormalization;
Sheaf.Paper.CoefficientHeartTriangulated;
Sheaf.Paper.CondensedModuleDerivedPushpull;
Sheaf.Paper.FormalClosedSupportDerived;
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic;
WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs.
Added the proof import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre.
All public imports were preserved to keep the public interface identical.

The item's proof no longer uses these old proof-plan nodes:
def-weil-pbc-noetherian-ring, pqf-def-locnoeth,
lem-weil-pbc-noetherian-open-subscheme-noetherian,
lem-weil-pbc-locally-noetherian-quasi-separated,
lem-weil-pbc-qcqs-morphism-permanence,
lem-weil-pbc-proetale-immersion-limit-preservation,
sk-def-sfb-derived-categories, det-lem-formal-closed-support-derived,
lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-proetale-ringed-closed-counit,
lem-sc-derived-adjunction-from-underived,
lem-weil-pbc-adjunction-counit-iso-right-fully-faithful,
lem-sfb-orthogonal-triangle-counit-normalization,
det-cor-coefficient-heart-ii-triangulated.
The first geometry step uses finite-type permanence directly for U as well as X;
NoetherianSpace makes j quasi-compact. The general formal support theorem already
supplies the actual normalized triangle and the fiber comparison, so no separate
orthogonality normalization is required. Triangulated closure is obtained from the
Serre theorem for the exact constructibility predicate in this signature.
Removed obsolete top-level tool_uses entries, retaining their original order otherwise;
no approval entry was added. Public imports can keep some modules reachable globally,
so these are proof-dependency prunings, not a claim that all leave the target closure.

## Where the brief, the DAG or earlier work was wrong

The cited CoefficientHeartTriangulated theorem is for constantModelBoundedConstructible,
whereas the item states upstream boundedConstructible (stratified local finite
presentation). The proved condensed-constructible Serre theorem fits the actual predicate.

The returned attempt narrowed the support theorem's derived-category universe and
incorrectly called its module unclaimed. Current main has C1's generalization to an
independent universe `w`, used by `RationalClosedSupportConstructible`. This repair uses
that generalization without altering it. R3's ownership and the rational consumer's
interface are therefore preserved. The stale support module, its node copy, and the
N4 universe change record were removed from the sandbox delivery set, resolving all
returned adaptation and consumer-audit objections by withdrawing that adaptation.
These removals affect only delivery copies; no library module is withdrawn or deleted.

The unit's route is preserved: localization, open finiteness, triangulated closure,
and closed pullback. Edge cases require no extra hypotheses: the proof works for zero
complexes, empty open/closed pieces, and rank-zero presentations; all objects and maps
come from the existing support theorem and exact functors.

The prior consumer audit became stale when the rational consumer landed. This delivery
makes no dependency interface change and requires no consumer adaptation or new change
record. Compilation is checked against the published library after clearing the retained
sandbox artifacts from the withdrawn dependency adaptation.

Validation: deliver3.py --no-push compiled the assigned module against the published
library and passed the preflight (dry-run commit a97e2d9115). Review class is CODEX
because the proof-plan node changes and this repairs a returned delivery.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
