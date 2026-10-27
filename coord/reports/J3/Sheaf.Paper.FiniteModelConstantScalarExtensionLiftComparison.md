## What changed

Withdraw the assigned false ordinary-tensor intermediate
Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison and the unclaimed
Sheaf.Paper.FiniteModelConstantScalarExtensionCore. Their DAG nodes remain, with
lean = null. Replace their parent's proof in
Sheaf.Paper.FiniteModelDerivedScalarComparison without changing its statement,
public imports, binder universes, or any target.

The replacement proves the algebraic universe/representative comparison in real
Lean: choose a flat-term K-flat resolution, lift it, use the two K-flat representative
isomorphisms and the universal small counit, compare pure tensors naturally, transport
along rho inverse and the augmentation, and identify the chosen representative.
Then use left-adjoint uniqueness for the sheaf scalar functors and the existing
proved generic constant-realization comparison.

Add the proved module Sheaf.Algebra.Homology.CoefficientLiftKFlatResolution.
It uses existing flat-resolution and flat-term K-flat preservation theorems; it
requires no new existence assumption and introduces no data choice in a definition.
The new parent helpers are private and proved. Imports used only for proofs are private.

Change record: coord/changes/finite-model-derived-scalar-false-ordinary-route.md.
Both withdrawn modules' actual Lean importers, their DAG parents, the unit's realized
nodes, and the quarantined source import search were checked before withdrawal.
The only direct importer of the adapted parent, FiniteQuotientModelResidueComparison,
compiled unchanged in 29.8 seconds. The new resolution compiled in 6.0 seconds;
the replacement parent compiled in 10.6 seconds, below the per-file limit.

## Proved and sorry left

The assigned item originally has 1 sorry, in
AlgebraicGeometry.Scheme.finiteModel_constantScalarExtension_liftComparison.
It is false as stated and is withdrawn, not claimed as proved. Thus 0 of its 1
original holes are proved; that hole is pruned by replacing the parent argument.
No new sorry is introduced or split off. No sorry remains in either delivered
nonempty Lean module.

New proved theorem: CochainComplex.exists_coefficientLift_kFlat_resolution
(lem-weil-pbc-coefficient-lift-kflat-resolution).
The existing AlgebraicGeometry.Scheme.finiteModel_derivedScalarComparison is now
proved using genuine derived tensor comparisons, with its original signature.
Its former proof depended on the assigned false hole and on the separate false
ordinary coefficient-transport hole; the replacement uses neither.

The unclaimed Core has no direct sorry and is withdrawn because its conclusion
is false too. The unchanged Bridge (held by J1) and CoefficientTransport (held by K1)
still have their own holes in the source library; this delivery adds no holes there
and makes this parent independent of them. The axiom check of the parent theorem and the new resolution lemma reports only
propext, Classical.choice and Quot.sound: the replacement parent has no transitive
sorry dependency either.

## No longer needed

Removed proof imports from the parent:
Sheaf.Paper.FiniteModelConstantScalarExtensionCore and
Sheaf.Paper.FiniteModelCoefficientTransport.

Withdrawn files and declaration attachments:
Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison
(lem-weil-pbc-finite-model-lift-comparison) and
Sheaf.Paper.FiniteModelConstantScalarExtensionCore
(lem-weil-pbc-finite-model-derived-scalar-comparison-core).

The parent route no longer needs
Sheaf.Paper.FiniteModelConstantScalarExtensionDerivedChangeBridge
(lem-weil-pbc-finite-model-derived-change-bridge), whose comparison follows directly
from the existing scalar adjunctions, or
Sheaf.Paper.FiniteModelCoefficientTransport
(lem-weil-pbc-finite-model-derived-scalar-comparison-transport), whose ordinary-tensor
intermediate is false. Those held modules are left untouched; the queue may prune
them if no other target route needs them. Generic derived constant realization,
K-flat resolution and scalar-counit nodes remain needed and are explicitly used.
No blueprint unit statement or realized unit step is bypassed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: both the assigned lift comparison and Core omit K-flatness
while concluding an ordinary termwise scalar-extension computation for arbitrary P.
For Z→Z/2 and P=(Z/2)[0], derived tensor has a nonzero degree -1 Tor term and ordinary
tensor does not. The DAG's step saying to apply the generic derived constant
comparison loses this derived-versus-ordinary distinction. The adjacent transport
module already reports the same counterexample. Adding another statement of the
same false ordinary comparison would only repeat the failed split.

The correct parent already states a derived comparison using the representative of
L(Q(P)); it does not need a stronger hypothesis. We prove that statement unchanged
using a K-flat resolution before doing ordinary tensor. This is a node-level route
repair, with the actual replacement parent proof and dependency changes delivered
in the same packet. No signature or source-tree exception is needed.

## New nodes

lem-weil-pbc-coefficient-lift-kflat-resolution: a proved, reusable module theorem
asserting existence of a small K-flat resolution whose coefficient-universe lift is
also K-flat. It is strictly a resolution lemma: it contains no scheme, scalar ring
map, constant realization, comparison functor or derived-extension conclusion.
Its proof applies the existing generic flat-term K-flat preservation theorem after
checking flatness and preservation of integer-indexed colimits for coefficient lift.
Its cross-unit citations are proved generic tools, consistent with the unit route.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Algebra.Homology.CoefficientLiftKFlatResolution": "0578f0b32f3ca2bffb80d3bfcfed64700d9f11e7", "Sheaf.Paper.FiniteModelConstantScalarExtensionCore": "fdd6fd89e33daef28207b2d920705ea5b4231ed8", "Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison": "fdd6fd89e33daef28207b2d920705ea5b4231ed8", "Sheaf.Paper.FiniteModelDerivedScalarComparison": "40cdbf7b41ac1758e1ef7f066ebb60da868c9c3e"}, "results": {"Sheaf.Paper.FiniteQuotientModelResidueComparison": {"hash": "d82775769280c5f15ac59387288c0027da6a0ae7", "status": "OK"}}, "seconds": 45, "time": "2026-10-28T06:32:11+0800", "transitive": 0, "version": 1}
```

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
