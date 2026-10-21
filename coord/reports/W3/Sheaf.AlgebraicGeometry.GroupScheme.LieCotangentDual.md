## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual.
The adopted source library already provides identityResidueEquiv and
lieCotangentDualEquiv with exactly the required scalar structures and hypotheses.
Compiled the original existential signature with the proof
`exact ⟨identityResidueEquiv G, ⟨lieCotangentDualEquiv G⟩⟩`, then withdrew the
redundant module through deleted.txt. The private scalar-transport implementation
is also already available upstream. No source-library file changes.

Retargeted lem-ag-lie-identity-cotangent-dual to the upstream construction, retaining
its three proof dependencies. Updated its DAG parent's proof text to name the
same constructions its existing Lean proof already uses. The unit and target
statements are unchanged. Change record:
coord/changes/W3-lie-cotangent-dual-retirement.md.

Validation: lcompile.py checked the reconstruction and printed only propext,
Classical.choice and Quot.sound for both the original existential statement and
the upstream construction. The existing upstream LieLocalDimension consumer was
checked separately with the same axiom result.

## Proved and sorry left

Actual initial hole count: zero. Holes closed: zero. Holes added: zero.
No sorry remains in the delivered packet, and no new statements are split off.
The already proved exists_lie_identity_cotangent_dual_equiv is retired as a
duplicate of the existing explicit construction lieCotangentDualEquiv, not counted
as a newly closed hole. Its exact statement was reconstructed and compiled before
withdrawal; the probe stays outside the delivered Lean tree.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual, including its
private cotangentDualScalarEquiv and the unused existential wrapper. All six
imports disappear with this duplicate module: WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring,
Mathlib.RingTheory.Ideal.Cotangent, Mathlib.LinearAlgebra.Dual.Defs,
WeilConjectures.AlgebraicGeometry.RationalPointTangentDerivationIdentification,
WeilConjectures.AlgebraicGeometry.GroupScheme.LieCotangentDualResidue and
WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv.
These imported modules and the three mathematical dependency nodes remain needed
by the upstream construction; none is claimed pruned. No DAG nodes are deleted.

## Where the brief, the DAG or earlier work was wrong

This is an explicit retirement repair with zero holes, rather than an unfinished
proof. The retirement inventory's DIFFERENT note reflects an absent theorem name,
not missing mathematics: upstream supplies the equivalence itself. The listed
Sheaf LieLocalDimension consumer has already been retired, and the current
upstream parent already uses lieCotangentDualEquiv directly. The DAG attachment
was stale; the mathematical statement and dependency route were correct.

Checked current returns and rework records: no return or quarantine row applies
to this item. tools/downstream.py reports zero importers. Lean and quarantine
searches find no callers outside the retiring file. The actual DAG parent is
lem-ag-smooth-lie-local-dimension; its dependency remains and is reconciled with
the upstream replacement in this delivery. No source declaration is removed.

Mathlib searches ran through msearch.py: LeanFinder found manifold group Lie
algebras rather than scheme cotangent duality; Loogle found ring cotangent-space
API; grep found no Lie/cotangent identification. The exact usable result was
found in the adopted WeilConjectures source library.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
