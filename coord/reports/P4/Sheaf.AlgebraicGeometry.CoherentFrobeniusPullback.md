## What changed

Restored Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback with its original theorem
signature and docstring. Its proof follows the three-step DAG plan: coefficient transport
through the fixed resolution edge, the structural ring map's power square under adjunction,
and compatibility of Ext universe transport with coefficient postcomposition. The final
square cancels the injective fixed comparison. The pullback lemmas are generic in their
coefficient modules, and all intermediate groups use the same concrete cached types.

Repaired the canonical comparison's duplicate resolution import, and redirected its
field-linear import after the shared Sheaf implementation was withdrawn during this session.
The canonical module constructs the two Ext presentations together, with their concrete maps
and a proved naturality field. It retains the same fixed comparison and additive action.
All existing signatures are unchanged. See
coord/changes/P4-coherent-pullback-resolution-implementation.md for old/new bodies, consumers,
and the required semantic review. CanonicalCoherentEtaleComparison is unclaimed in the
current claim records. No source-library file is modified.

## Proved and sorry left

Closed one original hole: AlgebraicGeometry.Scheme.Modules.coherentFrobenius_pullback
(new-coherent-frobenius-pullback). Added zero holes; split off zero statements. Neither
delivered module contains sorry. The new public coherentExtUniverse_postcomp and
coherentCohomologyHasExt theorems are proved, as are the private comparison_conjugate,
action_small, cancel_square, resolution_pullback, extPullback_naturality, and
structural_power_square helpers. This is a proof and a concrete definition/interface
repair, not a decomposition.

Verification: the canonical module compiled in 28.2 seconds and the complete item in
16.1 seconds at the normal project limits. #print axioms for coherentFrobenius_pullback
reports exactly propext, Classical.choice, and Quot.sound.

## No longer needed

The canonical comparison no longer imports the retained Sheaf resolution naturality
implementation; it uses the upstream implementation required by the edge theorem. The
retained module, its declarations and its attachment are preserved because other consumers
still use it. The field-linear import similarly uses the upstream replacement of the already
withdrawn Sheaf module; that withdrawal is not this delivery's pruning.

All mathematical dependencies in the assigned node remain needed: coefficient transport,
resolution naturality and edge compatibility, exact-functor Ext naturality, and the fixed
canonical comparison. No nodes or modules are withdrawn. New caches introduce no new
mathematical premise or unfinished obligation.

## Where the brief, the DAG or earlier work was wrong

The item source was quarantined, not withdrawn. Its recorded failure came from importing
both implementations of the same resolution declarations. The original mathematical plan
is sufficient. The proof step now explicitly records that it uses the upstream incarnation
re-exported by the edge module. The naturality dependency's retained Sheaf attachment is
preserved: this packet does not retire or reassociate that independently used module.

The current live graph has no external importer of the canonical comparison. Its eight
other direct archived consumers remain under their separate rework assignments. None uses
the removed resolution import's extra cache names through the canonical module. Its two
private auxiliary proof modules remain unchanged. The canonical node records the new
concrete presentation declarations. No target statement or mathematical hypothesis changes.

## Forced adaptations

Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison is unclaimed; the delivery changes
it as a dependency definition repair under the unclaimed-module rule. No module held by
another group is edited. The recorded item failure was:

```text
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality failed,
environment already contains ...ExtEdgeResolution.moduleComparisonEquiv
from Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
```

The two public imports at lines 10 and 13 now use the upstream implementations.
The second is needed by the upstream edge theorem. The first is also needed because the
shared Sheaf field-linear module was withdrawn during this session; the compiler then
reported `Unknown identifier scalarCohomology` in the canonical comparison.

The remaining changes preserve data and signatures while making the complete item compile
within the standard file limit. The earlier uncached presentation made the kernel repeatedly
expand derived additive structures and timed out after 60 seconds. coherentModuleGroup
(line 124) now uses the existing forgetful functor. The explicit presentation record,
constructor, postcomposition proof and small-group cache start at lines 152, 179, 192,
205, 212, 225, and 235. moduleAbelianCohomologyLarge (line 245) and
coherentAdditiveEndomorphism (line 266) use those same concrete fields. The repaired
canonical module compiles in 28.2 seconds and the full item in 16.1 seconds; its axiom check
contains only the three permitted axioms. The source library remains untouched.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
