## What changed

Proved AlgebraicGeometry.Etale.isIso_exchange_stalk_iff_strictLocalCohomology from
the existing strict-henselization stalk localization and strict-local total exchange
comparison theorems. Constructed the residue maps using ResidueField.lift, checked
compatibility by quotient extensionality, transported the small/full colimit models
through smallStrictHenselizationColimitIso_toBase (with a proved private equality-transport
helper for the identity reparametrizations), constructed the cartesian square
by pullback cancellation, and composed the additive equivalences.

Corrected the false arbitrary-arrow signature by adding hα, requiring α to equal
the canonical degree-q exchange. Adapted both calls in ExchangeStrictLocalCohomology
by adding rfl; its statement stays verbatim unchanged. Updated the item's node proof
and Lean record. Change record: coord/changes/M1-exchange-stalk-canonical-arrow.md.

## Proved and sorry left

The original declaration was false as written, so this is a statement repair with
a complete proof of the corrected canonical-exchange criterion, not a claim to have
proved the arbitrary-arrow assertion. The original single sorry is removed from
AlgebraicGeometry.Etale.isIso_exchange_stalk_iff_strictLocalCohomology. There are
zero remaining sorry holes in either delivered Lean module, and zero new holes.
No split-off statements or new data definitions are introduced. The corrected item
compiled cleanly through lcompile.py in 12.7 seconds, without warnings.

## No longer needed

Removed the direct proof import Sheaf.Paper.StrictHenselizationFunctoriality;
the required pointed factorization is obtained via the existing
Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift interface. Functoriality remains
a needed dependency through that module; it is not withdrawn. The original two
exchange comparison dependencies are both used. No node or module is withdrawn.
Added private proof imports for StrictHenselizationClosedLift and
StrictHenselizationClosedFiberComparison to use their proved model-transport APIs.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old Lean statement omitted the condition that α be exchange.
The node and Stacks 0EZU state only the canonical-exchange criterion. Identity base
change in degree zero with the constant integer sheaf and α = 0 is a counterexample
to the old Lean quantifier. See the change record for the exact old/new signatures
and complete consumer audit. Neither Challenge.lean nor any target is changed.

The existing localization theorem uses the full affine-neighbourhood strict
localization, while the item uses the small representative colimit. Their structural
maps must be related by the existing canonical comparison theorem; definitional
identification alone is insufficient. No new lemma is needed.

Searches used leansearch (ordinary scheme-stalk results), leanfinder (only etale-ring results), loogle (point sheaf-fiber
isomorphism instances), and grep plus rg over both library roots and Mathlib. The
existing two declared comparison theorems give the direct route; no shorter exact
library theorem was found. Checked the source at Tag 0EZU and the current blueprint
unit. The existing small/full-model compatibility node is used only as a transport tool;
it does not bypass the proper-base-change unit. The proof makes no change to the
unit's route and adds no assumptions about
properness, torsion, finite type or coefficient cardinality.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
