## What changed

In `Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups`, replaced the sole remaining
`sorry` in `CategoryTheory.derivedLimitRoosAbelianGroups` with a complete Lean proof
from the functorial acyclic finite-prefix resolution and the existing horseshoe
delta-functor theorem. Every existing declaration retains its signature and visibility.
The original docstrings are unchanged.

The kernel isomorphism, its inverse, and its naturality are constructed directly from
product and limit projections. The proof obtains a cohomological delta-functor from
`exists_horseshoe_rightDerived_deltaFunctor`, identifies degree zero with inverse limit,
transports the exact segment to the Roos differential, proves the boundary epi by
acyclicity, and constructs the cokernel isomorphism by the cokernel universal property.
Naturality follows by cancellation of the epi boundary; the higher vanishing follows
from exactness between two zero objects. All these combining steps are proved Lean.

Added a proof-only import of `Sheaf.CategoryTheory.RoosAcyclicResolution`. This new
module constructs the product functor and its natural `1 - shift` differential, and
states the remaining finite-prefix acyclic-resolution construction as one named theorem.
The existential resolution is used only locally in a theorem proof: no definition
selects data from the unproved existence theorem. No existing definition was changed.
Updated the parent node's proof and dependencies to match the Lean reduction.

Both delivered modules compile with `lcompile.py --all`, with no errors or warnings.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.derivedLimitRoosAbelianGroups`
(`lem-pc-derived-limit-roos-abelian-groups`). There are no sorries left in the item's module.
The existing `CategoryTheory.roosTowerEnoughInjectives` and
`CategoryTheory.roosLimitAdditive` remain proved and unchanged.

Added exactly one hole:
`CategoryTheory.exists_roos_acyclic_resolution` in
`Sheaf.CategoryTheory.RoosAcyclicResolution`
(`lem-pc-roos-functorial-acyclic-resolution`). Its complete proof in words is in its
Lean docstring and new node. It asserts a functorial short exact resolution with two
acyclic terms and identifies their ordinary limits; it does not assert the final
kernel/cokernel isomorphisms or higher vanishing for the original tower.

This is a decomposition: one original hole closed and one strictly intermediate hole
added, net zero direct holes. The kernel computation and the long-exact-sequence
combination, including both naturality equations and higher vanishing, are now checked
by Lean. The new product-functor and differential definitions contain no holes.

## No longer needed

Removed the proof-only import
`Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact`. The proof of additivity was
already direct, and `PreservesFiniteLimits lim` is supplied by Mathlib's limit-preservation
instance. Consequently `lem-pc-tower-limit-left-exact` is no longer a proof dependency
of the parent node. No public import was changed.

`lem-pc-tower-surjective-lim-acyclic` is no longer a direct parent dependency: its use
is confined to the new finite-prefix-resolution node. It remains needed there and is
not claimed as globally pruned. The horseshoe delta-functor, injective embedding and
injective split-tower imports are all used and retained. No other module is claimed
unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The plan cannot be followed by directly importing
`Sheaf.CategoryTheory.SurjectiveTowerLimitAcyclic`: that module publicly imports the
item's module, creating an import cycle. The new resolution theorem has independent
statements, with enough-injectives and additivity as typeclass parameters, and therefore
introduces no cycle in this delivery. Its eventual proof will need the existing
surjective-tower acyclicity result with its structural-instance dependency separated
from the upper Roos theorem, or a direct acyclicity argument. No unrelated held module
was adapted here.

The local checkout has no `literature/stacks-project/more-algebra.tex`; I read the
canonical source at https://stacks.math.columbia.edu/tag/07KW. Its finite-prefix
construction and acyclicity argument agree with the node's steps. LeanSearch returned
Internal Server Error; semantic searches and local Mathlib/source searches found no
existing theorem supplying the finite-prefix resolution.

Edge cases of the new statement were checked before stating it: at n=0 the second
prefix is the zero group and the first embedding is the identity; for the zero tower
all objects are zero; for constant identity-transition towers the difference map is
surjective by downward recursion at each finite prefix. For arbitrary towers, including
non-surjective ones, prefix transitions are still split projections. The resolution
therefore imposes no extra hypothesis on the input tower. The unit record has no realized
statement/step attached to this node, and the existing Stacks resolution route is kept.

## New nodes

`lem-pc-roos-functorial-acyclic-resolution`, at
`dag/nodes/sec-picard-framework/lem-pc-roos-functorial-acyclic-resolution.json`, records
`CategoryTheory.exists_roos_acyclic_resolution` in the new module
`lean/Sheaf/CategoryTheory/RoosAcyclicResolution.lean`. It extracts the finite-prefix
short exact resolution and the acyclicity of its two terms, leaving the actual derived
calculation to the proved parent theorem. Its source is Stacks 07KW, and all three
required search kinds are recorded, including the unavailable LeanSearch service.
There are no change records, since no existing public interface or statement changed.

## Second reading by C1

1. **Visible declarations and statements.** I diffed the delivered parent module against the repository version. Existing declaration signatures and visibility are unchanged; the only parent change is a proof-only import and replacement of the target proof. The new module contains the explicitly documented split theorem and its two supporting definitions.

2. **Compilation and proof audit.** Both modules compile with `lcompile.py --all` without errors or warnings. The parent target has no remaining `sorry`; the sole remaining `sorry` is the named theorem `CategoryTheory.exists_roos_acyclic_resolution`, with a matching node and complete proof sketch in its docstring. No forbidden `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition was found. The parent proof uses only the allowed kernel axioms together with the open split theorem.

3. **Truth and strength of the split statement.** The new resolution statement is a strict intermediate result: it asserts functorial finite-prefix short exactness, the two product limit identifications, and acyclicity of the two auxiliary towers, while leaving the Roos kernel/cokernel calculation to the parent. Its edge cases include the empty prefix at index zero and zero or identity towers, and the statement introduces no hypotheses on the input tower beyond the structural instances needed to define the derived functors. No duplicate Mathlib or library theorem was found by the recorded searches.

4. **Pruning and route.** The parent proof follows the unit route through the horseshoe delta-functor and the finite-prefix acyclic resolution. The proof-only import of `Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact` was removed because Mathlib supplies the needed finite-limit preservation instance; the corresponding parent dependency is removed from the node. Surjective-tower acyclicity remains a dependency of the split resolution theorem. No other unused imports or unreachable modules were identified.

5. **DAG and unit agreement.** The parent node's proof and `proof_deps` match the Lean proof, and the new node records its source, proof steps, searches, Lean declaration, and split status. Existing target and unit statements are unchanged, and the finite-prefix/acyclicity route from Stacks Tag 07KW is retained.

Changed during this second reading: added this review record only. No Lean declaration, statement, definition, or DAG content required repair.
