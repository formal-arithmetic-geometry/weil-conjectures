## What changed

Proved `AlgebraicGeometry.leray_edge_isIso_of_vanishing` with its original signature. Direct image preserves finite limits by the existing tensor-pullback adjunction. The existing direct-image injective-acyclicity theorem at the whole space supplies the Grothendieck composability witness. The existing `CategoryTheory.grothendieck_left_edge_cocycle` supplies canonical-edge invertibility under positive-column vanishing. The proof then maps this isomorphism to abelian groups, composes it with the resolution comparison isomorphism, and rewrites the comparison equality.

Added `Sheaf.AlgebraicGeometry.LerayEdgeGrothendieckComparison`, with one strictly intermediate statement: for a given acyclicity witness, the supplied cocycle edge agrees with the canonical Grothendieck edge after natural resolution comparison isomorphisms. This statement has no vanishing hypothesis and asserts no invertibility. Its statement and full natural-language proof are recorded in its new DAG node and docstring. Updated the original node's proof, proof dependencies, and proof origin to follow the Lean argument.

Added proof imports of the comparison module, `TensorPullback`, and the source's `ModuleCat.AB` instance module. Retained the original public statement import and the proof imports actually used by the argument. Relative to the repository version at second reading, removed the redundant proof imports `Sheaf.CategoryTheory.GrothendieckSpectralSequence`, `Sheaf.Paper.PQFCohomology`, and `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`; their required interfaces are already available through the retained dependencies. Only the target module and the new comparison module are delivered; an unchanged local copy of `LerayEdgeCocycleData` used while its compiled artifact was unavailable has been removed.

## Proved and sorry left

Closed the item's only original hole by decomposition (one upper hole closed, one strictly intermediate hole added; net zero holes closed): `AlgebraicGeometry.leray_edge_isIso_of_vanishing` (node `lem-pc-leray-edge-vanishing-iso`).

The delivery leaves exactly one new sorry: `AlgebraicGeometry.leray_edge_grothendieck_comparison` (node `lem-pc-leray-edge-grothendieck-comparison`). This is the resolution and cocycle identification step, strictly smaller than the target. The existing generic edge-cocycle theorem remains an imported open dependency; this delivery does not claim the target's entire transitive axiom closure is closed.

Both delivery modules compile without warnings through `lcompile.py --all`. The dry run checks the modules locally, with the axiom probe, and on the server. Edge cases of the new statement were checked against its construction: degree zero uses the ordinary sections identification; identity morphisms reduce to that identification; zero coefficients give maps between zero objects. No nonemptiness, geometric, or coefficient-vanishing hypothesis is introduced. The unit's realized statement and steps are unchanged.

## No longer needed

Removed redundant proof imports `Sheaf.CategoryTheory.GrothendieckSpectralSequence`, `Sheaf.Paper.PQFCohomology`, and `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck` relative to the current repository. No module is claimed globally pruned. The target does not separately instantiate `Sheaf.CategoryTheory.GrothendieckSpectralSequence` or rebuild its filtration: the existing generic edge-cocycle theorem packages these steps. The original node's direct proof dependencies on `thm-sp-grothendieck` and `lem-sp-grothendieck-edge-maps` are subsumed by the generic edge theorem and the comparison lemma; both remain transitive dependencies. These are every removed member of the original `proof_deps`. The source Grothendieck edge API remains needed by the comparison statement. No blueprint unit statement or realized proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly describes collapse and identification, but does not provide a Lean declaration for the specialized comparison between an arbitrary `LerayEdgeCocycle` edge and the canonical Grothendieck edge. That missing comparison is now a named, independently provable item. Direct image's finite-limit preservation is not registered as an instance on `RingedSpace.moduleDirectImage`; the proof obtains it from the existing tensor-pullback adjunction rather than assuming it or adding an open lemma.

The local `LerayEdgeCocycleData` object file was initially absent, then became available during this session. No interface or source change to that module is delivered. LeanSearch returned an internal server error; this is recorded as unavailable, with LeanFinder and source searches providing the remaining search evidence.

## New nodes

`lem-pc-leray-edge-grothendieck-comparison`, in `dag/nodes/sec-picard-framework/`, records `AlgebraicGeometry.leray_edge_grothendieck_comparison` in `lean/Sheaf/AlgebraicGeometry/LerayEdgeGrothendieckComparison.lean`. It belongs to the original chapter and unit, records three kinds of search, and gives the resolution-comparison and cocycle-uniqueness argument from Stacks Tags 01F2 and 01F4. No change record is needed: every existing statement and definition is unchanged.


## Second reading by K1

1. **Visible interface: pass.** Compared both delivered modules against the current
repository. `leray_edge_isIso_of_vanishing` has a byte-identical declaration signature,
including arbitrary schemes, arbitrary `f`, the supplied edge and cocycle hypothesis,
and vanishing for all positive `p` and all `q`. Its public import is unchanged; all
other target-module imports are private proof imports. The comparison is the only new
declaration. No existing definition or statement changes, so no change record is needed.

2. **Proof and trust: pass as a decomposition.** Read every line of both modules and
compiled them in import order using `lcompile.py --all`. The target constructs the
left-exactness instance from `nonempty_tensorPullbackAdjunction`, obtains acyclicity
from the second clause of `module_pushforward_injective_acyclic` at `⊤`, changes a
positive integer to a successor using `omega`, and swaps the vanishing indices for
`grothendieck_left_edge_cocycle`. Rewriting the comparison equation then uses only
preservation of isomorphisms and composition with the natural isomorphism `e`.
There is exactly one literal `sorry`, the named comparison theorem, and no forbidden
trust mechanism or definition. Scratch copies with explicit `#print axioms` for both
declarations compile and show exactly `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx`. The latter is expected from the comparison and imported open theorems;
this is not a closed transitive proof. One original hole is closed and one lower hole
is added, hence net zero and a decomposition, not a completed mathematical proof.

3. **Split statement: pass.** Read the actual `LerayEdgeCocycle` quantifiers and the
generic edge theorem, not merely their names. In the comparison, `hFG` is arbitrary
but no vanishing or invertibility is assumed or asserted. The missing part is the
natural identification of derived sections after forgetting scalars and uniqueness
of the edge determined on cycles. The quotient used for surjectivity is homology of
the complex of global sections in modules; this does not assume that global sections
preserves arbitrary epimorphisms of sheaves. The lift is unique because the cycle
inclusion remains monic under the left-exact sections functor. This gives equality
on representatives and then on all classes. Degree zero gives restriction along
`Opens.map_top` followed by the usual degree-zero identifications. For identity
morphisms this is the resolution comparison; for zero coefficients (also on an empty
scheme) both sides are maps between zero groups. These cases require no extra
hypothesis. The docstring and node describe this full argument. It is strictly a part
of the target argument, since collapse and acyclicity remain separately proved or
supplied by existing nodes.

The local Stacks source is absent on this machine, so read the primary source online:
[01F4](https://stacks.math.columbia.edu/tag/01F4),
[01F2](https://stacks.math.columbia.edu/tag/01F2), and
[01EX](https://stacks.math.columbia.edu/tag/01EX). Respectively these give the precise
vanishing case, the composite-sections Grothendieck construction, and direct-image
acyclicity for injectives. The resolution/cocycle identification is an explicit
intermediate argument from that construction, not a verbatim theorem in 01F4.
Repeated searches with different wording: LeanFinder for natural derived-composite
sections identification and edge uniqueness; Loogle for `Functor.rightDerived`;
`rg` in Mathlib, upstream algebraic geometry, and `lean/Sheaf` for edge and sections
comparison names. No duplicate was found. Loogle's degree-zero isomorphism is only
the degree-zero case. The existing `exists_lerayEdge_isIso_of_vanishing` uses this
item and cannot replace it. The full comparison is not a few-minute consequence of
the present API, so its named hole is retained.

4. **Route and pruning: pass after report correction.** The target uses the existing
acyclicity and generic collapse declarations rather than rebuilding a spectral
sequence. No shorter existing specialization was found. The comparison's public
Grothendieck and sheaf-abelian imports provide symbols and instances in its statement;
its generic-edge proof import records the remaining proof plan. The target's retained
private imports provide the comparison, collapse, adjunction, acyclicity and the
module-category Grothendieck instance. Removed direct dependencies are exactly
`thm-sp-grothendieck` and `lem-sp-grothendieck-edge-maps`; they remain transitively
used. Corrected the earlier report to name both and all three redundant private
imports removed relative to the current repository. No global module pruning is
claimed. Inspected `dag/units/sk-thm-picard-rr.json`: its `realized.statement` and
single `realized.steps` entry are empty and this delivery alters neither. The
Leray collapse/identification argument remains intact; no realized unit node is
bypassed.

5. **DAG: pass.** The original node changes only `proof`, `proof_deps`, and
`proof_origin`. Its first step records the adjunction and whole-space acyclicity;
its second records comparison, collapse, resolution choice and the index reorder.
The new node names exactly its Lean declaration and statement, the original chapter
and unit, source, natural-language proof, proof-dependency union, searches, creation
record and blueprint parent. Every remaining hole is named in the report. No target,
unit, or unrelated node was edited.

**Second-reader changes:** corrected the report's import/pruning inventory and made
its net-zero decomposition status explicit; added this independent review and axiom
checks. No repair to the Lean proof or node records was needed.
