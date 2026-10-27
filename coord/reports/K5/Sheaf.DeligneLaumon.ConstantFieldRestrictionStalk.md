## What changed

Replaced the proof hole of
`AlgebraicGeometry.WeilSheaf.hasPointwisePowerTransport_constantFieldRestrictionOfSquare`
with an explicit residue-degree and stalk-transport argument. Its signature and public import
are unchanged. Added private proof imports of
`WeilConjectures.WeilSheaf.StalkUpperStar` and
`Sheaf.DeligneLaumon.ConstantFieldTransportStructure`.

For a finite point z, the proof constructs x=c(z) and the positive degree
`e = finrank κ(x) κ(z)`. The finite-field cardinality formula proves the required residue-card
identity and `r * degreeOver(z) = e * degreeOver(x)`. It constructs a compatible old geometric
lift from the new lift, the algebraic-closure isomorphism and the inverse geometric-fiber
isomorphism. A proved general square lemma for global-sections transport turns the
structure-map square into Frobenius conjugacy. The existing source lemmas
`nonempty_equiv_stalkAt` and `frobeniusEnd_stalkAt_mul` then compare with the fixed stalk at x
and identify its e-th Frobenius power.

The only remaining obligation is the sheaf-level iterated structure-map square. It is stated
in the new module `Sheaf.DeligneLaumon.ConstantFieldTransportStructure`, with its source and
an induction proof in words. It also constructs the canonical carrier comparison as
`constantFieldRestrictionCarrierIso`, with an explicit target carrier, and marks this new
definition irreducible. This prevents clients from repeatedly unfolding the full restriction
functor when checking stalk comparisons. The comparison contains actual canonical data and
no proof holes. No source-library module, definition or existing interface was changed. The unit's
constant-field route is retained.

The complete item compiled with profiling in 10.3 seconds; its total kernel checking was
0.290 seconds. All temporary diagnostic files and profiling options were removed.
Clean `lcompile.py --all` validation then passed for both delivery modules.

## Proved and sorry left

Closed the original syntactic hole of
`AlgebraicGeometry.WeilSheaf.hasPointwisePowerTransport_constantFieldRestrictionOfSquare`
(node `lem-zl-source-constant-field-restriction-stalk`) by a complete Lean proof conditional
on the new structure-map lemma. There are zero holes in the item module.

Added exactly one hole:
`AlgebraicGeometry.WeilSheaf.frobeniusPowStr_constantFieldRestriction`, node
`lem-zl-source-constant-field-transport-structure`, in
`Sheaf.DeligneLaumon.ConstantFieldTransportStructure`.

This is a decomposition: one upper hole closed, one strictly smaller hole added, net zero
holes closed. The residue-field arithmetic, compatible-lift construction, general transport
square, lift-change comparison and Frobenius-power comparison are proved. The remaining
statement asserts an equality of sheaf morphisms and has no finite points, residue-degree
arithmetic, stalks, existence of lifts or Frobenius-module equivalences. It is not the original
statement renamed or repackaged. No data is chosen from a new unproved existence theorem.

## No longer needed

None. No existing public import, node or module is withdrawn. The original constant-field
and local-Frobenius definition dependencies are retained. The proof uses the proved source
stalk APIs rather than importing additional common-stage statement modules. There are no
unused intermediate nodes in this delivery and no pruning claim.

## Where the brief, the DAG or earlier work was wrong

No false statement or required signature repair was found. The source transport uses a
pushforward carrier, while the proof needs pullback along the inverse isomorphism. The new
canonical carrier interface states their comparison with the actual constructed target
carrier. The proved stalk comparison handles arbitrary Weil sheaves, and the pointwise
proof takes an arbitrary functor with the stated carrier square before specializing it to
the constructed functor. Field, scheme and sheaf types are explicit at the endpoint
comparisons, avoiding inference through the full concrete category construction.
The fixed-stalk comparison has an API with explicit point and index equalities.
The final power comparison also separates a generic Frobenius-module power calculation
from its application to concrete stalks. This avoids expensive conversion between bundles
with different return indices; profiling reduced kernel checking of that helper from about
95 seconds to 0.012 seconds. All proved helpers stay in the item file, subject to the same
60-second limit. A controlled diagnostic also isolated a costly conversion through a local
index alias `n := r * m`. Keeping `r * m` explicitly in the return comparison reduced its
kernel check from a timeout beyond 120 seconds to 0.178 seconds (9 seconds for the diagnostic
file). This changes no mathematical definition. The original plan's instruction
to regroup the iterated structure maps leaves a substantial coherence calculation: the source
library provides the first structure map (`transport_obj_str`), the addition formula for
iterates, and a same-field pushforward comparison, but no theorem for this arbitrary
constant-field transport square. The new node isolates precisely that calculation.

Checked the zero iterate and zero r cases: the displayed square is unit coherence in those
cases. For positive r its induction uses the ordered addition formula and does not commute
any structure-map factors. The arithmetic proof requires neither r positive nor any lissity,
simplicity or semisimplicity. Empty schemes have no finite points to check.

## New nodes

`lem-zl-source-constant-field-transport-structure`: the canonical identification of pullback
along the inverse geometric-fiber isomorphism with pushforward intertwines the iterated
source Weil structure maps. It isolates the structure-map portion of the original node's
second step. The current blueprint's first constant-extension paragraph is its source.
LeanSearch, LeanFinder and grep searches found no matching source or Mathlib declaration;
`BaseChangeField.Comparison.lowerStar_obj_frobeniusPowIso` is a useful same-field analogue,
not this statement. The new module's two public imports supply its signature. No change
record is needed because existing statements and definitions are unchanged.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
