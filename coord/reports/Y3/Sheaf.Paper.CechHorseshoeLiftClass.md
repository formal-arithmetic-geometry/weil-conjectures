## What changed

Proved `cech_horseshoe_lift_class` without changing its signature or public imports.
Added a proof-only import of `Sheaf.Paper.CechHorseshoeCorrectionCochain` and a new
proved theorem `cech_horseshoe_correction_cochain`. This theorem constructs the
correction Cech zero cochain and proves both its differential equations. The item
then expands the total differential on the (0,0) summand and proves the homology
identity directly. Both node records now follow these Lean proofs.

The new module uses proved private helpers for Cech product projections, monicity
on Cech cochains, and naturality and vanishing of the restriction zero cochain.
Its only additional proof import is `WeilConjectures.Topology.Sheaves.CechComparison`.
The local theorem has a scoped heartbeat allowance because its three sectionwise
and cochain calculations repeatedly compare categorical product module types.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.cech_horseshoe_lift_class`
(node `lem-sc-cech-horseshoe-lift-class`).

Also proved the new intermediate theorem:
`AlgebraicGeometry.Scheme.Modules.cech_horseshoe_correction_cochain`
(node `lem-sc-cech-horseshoe-correction-cochain`).

Both delivered modules compile without errors or warnings. `#print axioms` for
both public theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
No sorry remains in either module. Holes closed: one. Holes added: zero.
No axiom or data definition was added. Kernel lifts are obtained inside the proof
from the proved sectionwise exactness of the supplied row, not from an unproved
existence theorem. The total-complex proof uses `cyclesMap_i`, injectivity of
`iCycles`, `toCycles_comp_homologyπ`, and `homologyπ_naturality`.

## No longer needed

No baseline imports, nodes, or modules are pruned. The unpublished previous-attempt
`cech_horseshoe_zero_component` helper and its sandbox module/node are omitted:
the final proof does not use them. Trial direct imports of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` were removed because
ModuleCechComparison already exports them transitively. No filtration module
is imported; the existing Mathlib total-complex identities suffice.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's degreewise zero-composite helper did not reduce the target.
The missing sectionwise calculation can be formalized using evaluation preserving
kernels, `ShortComplex.moduleCat_exact_iff`, and the existing Cech product formulas.
It did not require abandonment or a new unproved theory.

The new theorem was checked on an empty indexing type, empty opens, and the zero
short complex. Its proof works uniformly on categorical intersections and uses
no cover assumption or nonempty-index assumption. In particular, the empty-family
case is handled by empty products, which are zero modules.

## New nodes

`lem-sc-cech-horseshoe-correction-cochain`, in
`dag/nodes/sec-curve-estimates/lem-sc-cech-horseshoe-correction-cochain.json`, realizes
original proof steps 1 and 2 and is fully proved. Its module is
`lean/Sheaf/Paper/CechHorseshoeCorrectionCochain.lean`. The source is Stacks 01EQ
(the double-complex augmentations) and 0B8S (local lifts). The unchanged target
retains the curve-estimate unit route; no realized unit statement or step is bypassed.

## Second reading by Y3

1. **Interfaces: pass.** Read both delivered modules and diffed the item against
   the repository. The sole existing theorem's signature is byte-for-byte equal;
   its docstring and existing public import are unchanged. The only item import
   added is proof-only. No existing definition, instance or statement changes,
   and no change record is needed. Both node `lean.statement` fields exactly
   match the declarations, checked independently by extracting their signatures.
2. **Proof and trust: pass.** Independently compiled both modules in import order
   with `lcompile.py --all`: no errors or warnings (41.5 s and 10.0 s).
   Inspected every proof, including the five private helpers. There is no `sorry`,
   forbidden declaration or hollow definition. The `choose c hc` step uses the
   proved `ShortComplex.moduleCat_exact_iff` applied to sectionwise exactness;
   it chooses inside a proposition proof, and monicity uniquely determines each
   preimage. It does not define data from an unproved existence assertion.
   Scratch copies with `#print axioms` compiled cleanly and reported only
   `propext`, `Classical.choice`, `Quot.sound` for both public theorems (39.6 s
   and 10.8 s). The delivery tool additionally probes every declaration.
3. **New intermediate: pass.** The correction theorem proves two cochain equations,
   strictly preceding the item's total-homology conclusion; it is fully proved,
   so there are zero split-off holes. Read its full docstring and node. Checked
   empty index types (empty products), empty opens (zero section modules), and
   zero rows (the correction is zero). No cover hypothesis is needed: neither
   sectionwise kernel preservation nor either cochain identity uses one.
   Repeated searches with different wording through `msearch.py`: LeanFinder for
   unique kernel preimages returned section-extensionality and sheaf generators,
   not this correction; Loogle did not know the short name
   `ShortComplex.moduleCat_exact_iff`; local Mathlib source search confirmed that
   exactness lemma and `Exact.map_of_mono_of_preservesKernel` and their hypotheses.
   The grep search and direct searches of `lean/Sheaf` and upstream
   `Topology/Sheaves/CechComparison.lean` found no public correction theorem.
   The two restriction identities do occur as private theorems in
   `ModuleCechComparison`, hence are unavailable to importers; their local proofs
   legitimately repeat the small naturality and cancellation arguments.
4. **Route and pruning: pass.** Read the definitions of `moduleCechDouble`,
   `moduleCechZero`, alpha and beta, and the entire target proof. The correction
   proof uses `hιB`, `hx`, `hb` to establish its kernel condition, `hrows 0` to
   lift it, `hrows 1` and `ha` for the negative resolution differential, and
   `hιA`, `hz` for the Cech differential. In the target, `total_d`, `ι_D₁`,
   `ι_D₂`, `d₁_eq`, `d₂_eq` give both positive outgoing signs at (0,0).
   `cyclesMap_i`, `toCycles_i`, injectivity of `iCycles`, and
   `toCycles_comp_homologyπ` then prove the homology equality directly.
   No shorter public declaration was found. Read the unit
   `sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`; this local calculation bypasses no unit step.
   All four original proof dependencies remain used, two directly and two
   through the new correction theorem. Consequently none is pruned.
   Read [Stacks 01EQ](https://stacks.math.columbia.edu/tag/01EQ), proof of
   Lemma 20.11.2, for the two augmentations, and
   [Stacks 0B8S](https://stacks.math.columbia.edu/tag/0B8S), proof of Lemma 20.25.5,
   for the local-difference boundary computation. These provide the source
   construction, not a verbatim theorem with this arbitrary-family signature.
   The Lean difference convention is explicitly x(i1)-x(i0), and the proof's
   signs are checked against that hypothesis rather than silently importing the
   opposite order printed in 0B8S.
5. **DAG: pass.** The existing node changes only proof-owned fields; its new
   dependency is the proved correction theorem. The new node's degree-zero
   kernel construction and the two monic cancellations agree with the Lean.
   Its source, statement dependencies, proof-origin, recorded searches, created
   record, blueprint ancestry, chapter, unit and Lean record are present.
   The target's dependency union is exactly its proof steps' `uses`; the new
   node's union likewise agrees. The original sectionwise dependency nodes
   remain dependencies of the correction, not discarded mathematics.

Second reading changed only this report: added the independent checks, the
private-helper explanation and the source/sign-convention qualification.
No Lean or node repair was necessary. Net holes closed: one; holes added: zero.
