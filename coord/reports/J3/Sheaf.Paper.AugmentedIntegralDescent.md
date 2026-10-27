## What changed

Proved `WeilConjectures.PurityFiniteSetting.augmentedIntegralMembershipBounds` without
changing its statement. Completeness is assembled from the existing Roos connecting-map
bijection and distinguishedness criterion, then transported through the proved
`sfDerivedComplete_iff_legacy`. Fixed support and Tor intervals are detected at each
positive quotient. Finite minima and maxima give common bounds independent of the quotient
exponent; interval enlargement is proved directly. Empty components and the empty
partition are included, with explicit zero derived objects and the interval [0,0].

Added `Sheaf.Paper.IntegralReductionFiniteClopenBounds`, proved from
`finite_clopen_constructibility_bounds` at exponent n+1, invariant cohomology and Tor tests,
and the one-quotient comparison below. Its bounded-support converse uses a finite union of
component supports, so it also handles an empty index type.

Added `Sheaf.Paper.IntegralReductionClopenComparison` for the remaining ordinary
restriction / derived quotient coefficient comparison at one exponent. Its docstring
records the complete local tensor and localization argument. It does not assert any
augmentation, transition, tower, completeness, integral membership or uniform-bound result.

The item's proof imports now include these finite-level bounds, the intrinsic/legacy
completeness comparison and finite extrema. The given purity setting supplies the
characteristic and its recorded different-characteristic proof. A universe-zero datum
over the prime field in that characteristic meets the legacy existential universe.
`HasDerivedCategory.standard` is locally irreducible to avoid unfolding the standard
localization while comparing instances. The existing item now uses the current
public definition import, Sheaf.Paper.ClopenIntegralRestriction; the two new modules
use that definition import as well. Existing declaration signatures follow the current
main branch, including its clopenIntegralModuleRestriction rename. After the Roos calculation,
the completed restriction and scalar-extension functors are also locally irreducible to
keep the membership assembly from unfolding those constructions.

## Proved and sorry left

Closed the existing hole
`WeilConjectures.PurityFiniteSetting.augmentedIntegralMembershipBounds`.
Also proved the new theorem
`WeilConjectures.PurityFiniteSetting.integralReductionFiniteClopenBounds`.

One of the two original holes remains:
`WeilConjectures.PurityFiniteSetting.augmentedIntegralReductionComparison`
(node `lem-pur-clopen-augmented-integral-descent`). Its statement and proof hole are untouched.

Added one hole:
`WeilConjectures.PurityFiniteSetting.integralReductionClopenComparison`
(node `lem-pur-integral-reduction-clopen-comparison`). It is strictly the one-exponent
coefficient comparison needed before finite-level detection, not the membership theorem
under another name. Thus one of two original holes is closed with one split-off hole;
this is a decomposition, with zero net holes closed. Both prior proved assertions
`augmentedFiniteRestriction_exact` and `augmentedIntegralRoosDescent` remain proved.

## No longer needed

Removed the item's direct proof import of
`Sheaf.Paper.FiniteClopenConstructibilityBounds`: it is used inside the new proved
finite-level bounds module. Its node remains needed through that module, so no existing
module or node is withdrawn. The stale public import of ClopenRoosIntegralDescent is
replaced in all three
modules by ClopenIntegralRestriction. The consumer theorem module is no longer reached
from this item. No existing DAG dependency is
pruned, since the original augmented comparison still has its unchanged proof plan.

The parent `finiteClopen_integral_membership` is not used as a shortcut: its own DAG
proof depends on this item, and using it would give a circular planned proof.

## Where the brief, the DAG or earlier work was wrong

Repair of returned head fc1319e61ec: the original delivery imported the consumer
ClopenRoosIntegralDescent from both new modules (and retained its stale import in the
item). Current main imports AugmentedIntegralDescent from that consumer, so this created
the reported import cycle. Rebased all three modules onto the existing definition-only
ClopenIntegralRestriction module and the current clopenIntegralModuleRestriction name.
The existing node was refreshed from current main before reapplying only our proof route.
The new nodes explicitly cite def-pur-clopen-integral-restriction. No consumer theorem
is used, and no change to the consumer is needed. A traversal of the 12,186-module
import closure with the sandbox overlaid found no cycles and no path to
ClopenRoosIntegralDescent. Every existing declaration signature matches current main.


No target or existing statement is changed or disputed. The original step 5 did not
provide an immediately usable comparison from ordinary completed restriction to the
published constant-ring inverse image at a single quotient. That interface is now stated
separately, and all subsequent finite-level and uniform-bound assembly is Lean code.
The existing node is updated to show that interface and the proved intrinsic/legacy
completeness comparison explicitly. The original module already has proof-only
`backward.isDefEq.respectTransparency` settings; the new modules introduce no such settings.

Edge cases read against the statements and proof: empty I (no minimum is taken), empty
components, singleton partitions, zero objects, distinct component intervals, exponent one,
and ramified coefficients. Neither quotient flatness nor boundedness of the initial K
is assumed. No arbitrary data definition is chosen from an existence theorem: the new
comparison is used only inside theorem proofs.

## New nodes

`lem-pur-integral-reduction-clopen-comparison` records the ordinary restriction /
derived scalar extension comparison at a single positive quotient, with its coefficient,
pure-tensor and localization proof. Module:
`Sheaf.Paper.IntegralReductionClopenComparison`. This is the only new unproved statement.

`lem-pur-integral-reduction-finite-clopen-bounds` records the proved finite-level
constructibility, fixed support and fixed Tor detection theorem. Module:
`Sheaf.Paper.IntegralReductionFiniteClopenBounds`. It uses the comparison node and the
existing finite-clopen constructibility theorem. Both new nodes remain in the original
`sk-def-purity-conv` unit and `sec-smooth-purity` chapter. No change record is needed:
no existing definition or statement meaning changes. The item preserves the current
main branch's extracted definition import and renamed module restriction.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
