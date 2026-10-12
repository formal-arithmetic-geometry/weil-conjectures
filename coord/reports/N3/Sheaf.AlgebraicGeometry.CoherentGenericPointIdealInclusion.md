## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion`
with a compiled proof from descent and an integral ideal-sum construction. The final map
is `(pushforward i).map χ ≫ β`. A proved private helper transports an invertible source
stalk through closed pushforward using the natural bijective stalk comparisons. The
pushforward preserves monomorphisms because it is a right adjoint. Finite pushforward
preserves coherence, so the existing coherent local-isomorphism criterion supplies the
ambient neighbourhood directly. This avoids transporting and intersecting two opens.

Added `Sheaf.AlgebraicGeometry.CoherentGenericPointClosedDescent`, with a complete proof.
It constructs the descended module as the tensor pullback of the annihilator submodule,
uses the invertible adjunction unit from the existing closed-immersion annihilation
criterion, and proves the inclusion has a bijective generic stalk. Ideal germs map to
zero under the local-ring map and hence are nonunits, so lie in the ambient maximal ideal;
the stronger equality between the defining-ideal stalk and the maximal ideal is unnecessary.

Added `Sheaf.AlgebraicGeometry.CoherentIntegralGenericIdealMap`, with the remaining integral
construction as one public theorem. Both new statements have source, complete proof in
words, edge-case discussion, and new nodes. Updated the parent node's proof and dependency
list. Existing signatures and public imports are unchanged. All three modules compiled
in import order through lcompile.py; the item also compiled separately.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.coherent_generic_point_ideal_inclusion`.

Also proved:
`AlgebraicGeometry.Scheme.Modules.coherent_generic_point_closed_descent`
(new node `lem-weil-pbc-coherent-generic-point-closed-descent`), and the private helper
`AlgebraicGeometry.Scheme.Modules.pushforward_stalk_isIso`.

One new hole remains:
`AlgebraicGeometry.Scheme.Modules.coherent_integral_generic_ideal_map`
(node `lem-weil-pbc-coherent-integral-generic-ideal-map`), in its own new module. Its whole
proof is exactly `:= by sorry`. It packages only the integral lattice construction
(parent steps 4--6): it has no ambient scheme, closed immersion, maximal-ideal hypothesis,
or ambient-neighbourhood conclusion. The caller constructs and checks the composite and
obtains the neighbourhood itself. The delivery closes one original hole and adds one
strictly smaller hole; this is a decomposition, not a claim of a complete axiom-free proof.
The existing dependency theorems that still use sorry are not claimed as newly proved.
No sorry remains in the item or descent module. No data definition was added.

Edge cases: a zero generic stalk permits rank zero; the zero-fold coproduct is zero.
The ideal extension exponent may be zero, giving the unit ideal. In descent the target
local ring is nontrivial even when the module stalk vanishes. No positivity or nonzero
module hypotheses are introduced.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Algebra.Homology.ModuleStalkExact`
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentStalkMapExtends`
- `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`
- `Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.AlgebraicGeometry.SectionsAnnihilatedByIdeal`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Topology.PresheafModuleStalkFunctor`

Most remain reachable through the two new modules or existing dependencies. The following
seven Sheaf modules actually leave this item's import closure (computed from source imports
before and after the sandbox overlay); this does not assert that other targets no longer
need them:

- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerImage`
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardCokernel`
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful`
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers`
- `Sheaf.AlgebraicGeometry.ModulePullbackIdealProductImage`
- `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`

Their attached nodes no longer needed by this item:

- `lem-weil-pbc-closed-immersion-coherent-equivalence` (`Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`)
- `lem-weil-pbc-closed-immersion-ideal-power-image` (`Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerImage`)
- `lem-weil-pbc-closed-immersion-pushforward-cokernel` (`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardCokernel`)
- `lem-weil-pbc-closed-immersion-pushforward-fully-faithful` (`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful`)
- `lem-weil-pbc-closed-immersion-pushforward-ideal-powers` (`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers`)
- `lem-weil-pbc-module-pullback-ideal-product-image` (`Sheaf.AlgebraicGeometry.ModulePullbackIdealProductImage`)
- `lem-weil-pbc-module-pullback-ideal-quotient` (`Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`)

The Mathlib module `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` also leaves
this item's import closure. The new proof no longer uses the coherent-equivalence step
`lem-weil-pbc-closed-immersion-coherent-equivalence` or its adic-system infrastructure;
it uses `lem-weil-pbc-closed-immersion-pushforward-annihilated` instead. The unit and
chapter route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error or tool failure was found. The original descent step asked for more
than necessary: membership of defining-ideal germs in the maximal ideal suffices, without
computing equality of ideals. The final neighbourhood can be obtained from the composite's
invertible generic stalk and coherence, rather than explicitly transporting an open of Z.
The local literature mirror lacks coherent.tex; the proof was checked against the public
Stacks Tag 01YE page at https://stacks.math.columbia.edu/tag/01YE. LeanSearch returned an
Internal Server Error for both new-statement queries; that unavailability is recorded,
without inventing a search verdict. LeanFinder and Mathlib source grep completed and gave
no matching statement. No forced adaptations or statement changes were needed.

## New nodes

`lem-weil-pbc-coherent-generic-point-closed-descent` records the now-proved descent step,
with its actual annihilator/pullback proof and dependency list. Its module contains one
public theorem, already proved. It realizes parent steps 1--3 with the simpler generic
stalk membership calculation.

`lem-weil-pbc-coherent-integral-generic-ideal-map` records the remaining integral
ideal-sum lattice construction and injectivity argument, parent steps 4--6. It asserts
coherence of the coproduct as needed by finite pushforward. Its source is the final
paragraph of Tag 01YE, and its node and docstring supply the detailed construction and
kernel-coordinate argument. This is the only new sorry. No change record is required.

## Second reading by N3

1. **Diff and interfaces.** Compared the delivered item module with the repository version. The existing declaration signature is byte-for-byte unchanged; the new modules only add the split-off declarations recorded by their nodes. Verdict: pass.

2. **Compilation and proof hygiene.** Compiled all three modules in import order with `lcompile.py`. There are no forbidden commands, hollow definitions, or anonymous sorries; the sole remaining `sorry` is the named integral construction theorem listed above. The proved declarations use only the permitted foundational axioms apart from that imported open theorem. Verdict: pass.

3. **Statements and split nodes.** Checked both new statements against the parent proof and the Stacks Tag 01YE argument. Closed descent is a strict first-step reduction; the integral ideal-map theorem is a strict construction-only remainder and has a complete natural-language proof plan, source, edge cases, and matching DAG node. No existing library theorem duplicates either statement. Verdict: pass.

4. **Pruning and route.** Verified the removed imports are proof-only and that the remaining imports compile. The parent route still uses the unit's descent, integral-map, pushforward, and local-isomorphism steps; the listed obsolete nodes and modules are no longer in this item's import closure. Verdict: pass.

5. **DAG agreement.** Checked each node's Lean module, declaration, proof dependencies, proof origin, chapter, unit, and `realized` route against the source. The parent node now names exactly the two new dependencies and the private stalk helper used in its proof. Verdict: pass.

Changed only the proof imports and proof of the item, added the two matching modules and nodes, and added this second-reading record. No statement or definition was changed.
