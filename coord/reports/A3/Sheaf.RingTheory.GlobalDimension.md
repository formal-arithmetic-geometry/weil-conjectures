## What changed

Completed the queued retire-first repair of Sheaf.RingTheory.GlobalDimension (zero
holes). Withdraw its duplicate definitions, reattach def-weil-pbc-finite-global-dimension
to WeilConjectures.RingTheory.GlobalDimension, and redirect its only consumer,
Sheaf.Algebra.ProjectiveDimensionWellDefined. That consumer keeps its full theorem
signature and padding/minimality argument; its global-bound step now converts through
the existing proved bounded-resolution/Ext equivalence. Reattach that equivalence's
node lem-weil-pbc-projective-resolution-ext-degree to its adopted upstream module.
Update the consumer node's final proof step and dependency accordingly.

The adapted consumer compiled with no errors or warnings through lcompile.py.
An import-only adaptation was first compiled and failed precisely at the old final
padding call (Ext bound supplied where a bounded resolution is required).
The delivery's axiom probe checks the retained theorem independently.

Change record: coord/changes/global-dimension-retire-upstream.md.

## Proved and sorry left

The assigned item has zero sorries before and after the repair: closed 0 of 0;
added 0; split off 0. No sorry remains in any delivered module.
ModuleCat.projective_and_global_dimension_well_defined retains its complete proof,
adapted to the upstream definition using the already proved equivalence. This is a
definition retirement repair, not a newly closed proof hole.

## No longer needed

Withdraw lean/Sheaf/RingTheory/GlobalDimension.lean (listed in deleted.txt).
Remove public import Sheaf.RingTheory.GlobalDimension from the sole consumer and
replace it with public import WeilConjectures.RingTheory.GlobalDimension. Its two
Mathlib public imports remain available from the upstream module. The six local
definitions are removed; five names are provided upstream. The unused natural-valued
ModuleCat.projectiveDimension is pruned, and its node attachment is removed. It is
not equated with Mathlib's extended-valued dimension (whose value at zero is bottom).
No DAG node is deleted and no unit statement or realized step is bypassed.
The explicit-resolution/Ext bridge is still needed; its upstream proof is unchanged.

## Where the brief, the DAG or earlier work was wrong

This is the retire-first queue's zero-hole repair, not an outstanding theorem proof.
Upstream changed HasFiniteProjectiveDimension and HasGlobalDimensionLE to Ext-based
bounds, so blindly retiring the duplicate would break the padding proof. Stacks
065R (lemma-projective-dimension-ext) and the existing proved Lean bridge identify
the bounds on ModuleCat.{max u v}; the consumer explicitly uses that bridge.
The source definitions 00O4/00O6 and 065R were read in literature/stacks-project/algebra.tex.
The definition node's old attachment also included the now-unused natural-number pd
function; the new attachment does not claim Mathlib's different function realizes it.

Searches via msearch.py: LeanFinder returned Ext dimension criteria; Loogle returned
CategoryTheory.hasProjectiveDimensionLT_of_ge; grep returned no hit. Direct rg of the
active source tree found the existing proved upstream bounded-resolution equivalence
and the sole consumer. tools/downstream.py confirms one direct and transitive
consumer. No active Challenge signature mentions any of the retired names.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
