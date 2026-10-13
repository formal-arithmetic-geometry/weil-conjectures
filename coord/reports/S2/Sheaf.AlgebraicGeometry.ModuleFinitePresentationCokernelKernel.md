## What changed

Proved `AlgebraicGeometry.RingedSpace.kernel_composite_cokernel_isFiniteType`
in `Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernelKernel` with its signature
and visibility unchanged. The finite relation family makes the presentation kernel
finite type. The restricted cokernel sequence makes its kernel an epi image of the
restricted finite-type source. Mathlib's kernel/cokernel composition sequence gives a
short exact sequence with those two kernels as endpoints; the existing finite-type
extension theorem proves the middle kernel finite type.

Private, completely proved generator-transport helpers adapt the existing private
helpers of `CoherentKernelConditionRestriction` to arbitrary ringed spaces. They
identify the slice-site statement with the restriction to the topological open, where
`finiteType_image_extension` applies, and transfer the conclusion back. They introduce
no public interface. The scoped heartbeat limits accommodate these nested functors;
the single-file compile remains below the 60-second limit.

Added proof-only imports `Mathlib.Topology.Sheaves.Module` and
`Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp`.
Updated the item's DAG proof, proof dependencies, and proof origin to describe this
categorical realization of the source argument. The unit `sk-thm-p1` and all its
realized statements and proof steps are preserved; this item is below the unit level.
Read the original source proof at https://stacks.math.columbia.edu/tag/0H96.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.RingedSpace.kernel_composite_cokernel_isFiniteType`
(node `lem-weil-pbc-module-finite-presentation-cokernel-kernel`).
No `sorry` remains in the item's module. No holes were added or split off.
All private helpers are fully proved. No definitions or existing statements changed.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting` and the direct DAG
dependency `lem-weil-pbc-ringed-space-module-exactness-local-lifting`.
The sectionwise construction of the induced map onto the image and its local lifting
proof are replaced by Mathlib's composition sequence and exact kernel lift.
The local-lifting module remains a transitive dependency of
`ModuleFiniteTypeImageExtension`, so this delivery does not assert it is globally
unreachable. No other dependency imports or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The statement and source argument are correct. The finite-type extension theorem is
stated for modules on a ringed space, whereas the presentation in this item is on the
slice site `Over U`. A direct application therefore needs the open-site equivalence
and preservation of finite type in both directions; these are supplied by proved
private helpers. No scheme or Noetherian hypothesis is needed. Empty generator and
relation families and the empty open are handled by the same finite-family and
cover constructions, without any nonemptiness assumption.

## Second reading by S2

1. **Existing interface: pass.** Diffed the sole delivered module against the
repository. The existing theorem signature is byte-for-byte identical, including
all hypotheses and its conclusion. Its docstring and visibility are unchanged.
There are no changed definitions, additional public statements, forced adaptations,
or change records. Both public imports are needed by the signature: `moduleRings`
and the finite presentation structure. The two new imports serve proofs only and
are plain imports.

2. **Proof and construction: pass.** Read every private helper and the theorem
from its conclusion downward. Local generators are explicitly transported through
colimit-preserving module functors; no data is obtained from an unproved existence
theorem. The finite relation family generates the presentation kernel. Restriction
preserves the cokernel sequence's exactness, giving the epi onto its kernel. The
composition sequence gives the stated short exact sequence because the first
presentation map is epi and its cokernel projection vanishes. Kernel preservation
and the equivalence unit transfer the result back. Local compilation of the module
succeeded without errors or warnings (55.2 seconds). No `sorry` or forbidden
declaration or attribute occurs in the delivered source. `#print axioms` in a scratch copy
compiled cleanly (49.2 seconds) and reported exactly `propext`, `Classical.choice`,
and `Quot.sound` for the public theorem, with no `sorryAx`; this also covers all
private helpers used by its proof.

3. **Split-off statements: pass, none.** No new holes or public lemmas were added.
The private transport helpers are fully proved and adapt existing private helpers
which cannot be imported as public declarations. Checked the empty open, zero
generator or relation families, and zero morphism: neither the cover construction
nor the exact-sequence argument assumes nonemptiness. Independent Lean Finder
search for finite-type invariance under site equivalences and open restriction,
Loogle search for `SheafOfModules.IsFiniteType`, and source searches found no
public replacement for the ringed-space transport argument or the composite-kernel
result. The generic epi-image theorem alone does not provide closure under
extensions on the slice site.

4. **Route and pruning: pass.** Compared the argument with
[Stacks 0H96](https://stacks.math.columbia.edu/tag/0H96): the middle kernel is the
preimage of the image, with finite-type endpoints. Mathlib's proved composition
sequence implements this step. The retained proof imports are used. The report's
`No longer needed` section contains exactly the removed old dependency and its
direct import; the module remains transitively reachable, as the report explains.
Read `dag/units/sk-thm-p1.json`: this helper is not a realized unit statement or
step, and no realized route is bypassed or changed.

5. **DAG: pass.** Only `proof`, `proof_deps`, and `proof_origin` differ. The
proof dependencies are exactly the union of the step dependencies and describe
the Lean argument: finite presentation, epi kernel lift, finite-type images and
extensions, exact sequences, and Mathlib's snake lemma composition sequence.
No new node needs checking.

Second reading changed only this report: added the independent review. No Lean
proof or DAG repair was necessary. Closed one existing hole; added zero holes.
