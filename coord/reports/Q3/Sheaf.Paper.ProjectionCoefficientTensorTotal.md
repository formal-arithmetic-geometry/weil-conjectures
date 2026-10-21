## What changed

Restored lean/Sheaf/Paper/ProjectionCoefficientTensorTotal.lean from its exact
quarantine source, as assigned by coord/rework.tsv. Repaired total by fixing the
source and target module categories and the existing additive instance at its
tensorPullbackTotal call. Its direct-sum formula and differential are unchanged.
All nine public signatures and all existing declaration docstrings are unchanged.

Proved ordinary existence from the existing ringIso_tensor_transport theorem,
using an explicit commutative-ring lift of the recorded coefficient isomorphism.
Proved uniqueness by sheafification and tensor extensionality. Naturality is the
selected witness's first clause, with tensorHom definitionally the same map.
Proved total invertibility from tensorPullbackTotal_isIso and the coefficient
restriction equivalence's adjunction. Both added helpers are private and proved.
The two existing backward transparency settings are false to permit the concrete
module/abelian instance identifications. No upstream source file is changed.

Updated def-sf-projection-coefficient-tensor-total's proof and proof dependencies
to describe this argument. Its statement, statement dependencies, Lean attachment,
and unit route are preserved. The change record is
coord/changes/Q3-projection-coefficient-tensor-total.md.

The restored module compiles without warnings (34.5 seconds after import pruning).
The delivery tool additionally checks declarations, axioms and the complete packet.
Public signature comparison against the archive reports all nine unchanged.
The unchanged quarantined direct consumer
Sheaf.Paper.ProjectionTensorCoefficientComparison also compiles without warnings
against the sibling restored module using lcompile.py --all: item 38.5 seconds,
consumer 31.6 seconds. Its temporary test copy was removed from this packet; no
consumer adaptation is needed. A source-level dependency traversal also confirms
that none of the added proof dependencies creates a DAG cycle.

## Proved and sorry left

Closed all four archived holes in namespace
WeilConjectures.ProjectionTensorCoefficient:

- module_existsUnique (def-sf-projection-coefficient-tensor-total).
- module_naturality (the same node).
- module_tensorHom_naturality (the same node).
- total_isIso (the same node).

Zero sorry remain in the item; zero holes were added elsewhere; zero results were
split off. This proves the item from existing declared dependencies; the imported
SheafOfModules.ringIso_tensor_transport remains an existing unfinished dependency,
not a new theorem or hole of this delivery. No axiom-free closure claim is made.

## No longer needed

Removed the unused public imports Sheaf.Paper.RationalCoefficientCategoryComparison,
Sheaf.Paper.WfTensorCompletionFrobenius, and Sheaf.SixFunctors.OpenFactorTensorModel.
The first is replaced by its narrower coefficient-definition dependency
Sheaf.Paper.FdCoefficientComparison. Neither rational realization, Frobenius tensor
completion, nor an open-factor tensor model enters this ordinary comparison.

These removals do not withdraw those modules or their nodes: the quarantined parent
ProjectionTensorCoefficientComparison independently imports all three and uses their
interfaces. No DAG statement dependency or unit step is pruned. The only proof
import added is Sheaf.Algebra.Homology.RingIsomorphismTensorTransport.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it was quarantined, not because it was
withdrawn. Its archive has four holes and an elaboration failure at total's
implicit module category. Adding explicit category/functor instances repairs the
construction without changing its mathematics or any public signature.

The definition node had an empty proof plan despite its four associated proof
obligations. Its updated proof records the specialization of the existing general
transport theorem, the independent uniqueness argument, and the actual total-map
invertibility proof. The parent nodes and the unit remain needed and unchanged.

Edge cases: the argument has no nonzero-module, nonempty-scheme, boundedness,
constructibility or invertibility-of-l-on-X premise. Zero modules, the empty
scheme, arbitrary integer bidegrees and the zero complex are covered by the same
sheaf tensor and coproduct universal properties. Coefficient restriction is along
an isomorphism, so no flatness hypothesis is added.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
