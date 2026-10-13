## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.exists_etaleAdditiveCech_normalized`
to the explicitly specified augmentation homology comparison. Its signature,
visibility, and normalization predicate are unchanged.

Added `EtaleAdditiveCechResolutionTransfer.lean`, with a complete proof of
`exists_additiveCech_resolution_transfer`. An identity lift between resolutions
induces the evaluated global map and the termwise Čech total map. The proof checks
both augmentation squares on actual components and proves compatibility with every
supplied canonical Ext comparison by representing a homology class by a cocycle.
The validated canonical helper from the previous attempt is incorporated here.

Added `EtaleAdditiveCechAugmentationHomology.lean`, stating the remaining comparison
of the two augmentations on one resolution, with cycle lifts and representative
formulas. These formulas and the surjective homology quotients uniquely determine
the maps; no arbitrary equivalence or hollow definition is introduced.

The main proof fixes an injective resolution J, uses its canonical comparison,
and composes its inverse with the global augmentation homology equivalence and the
inverse coefficient augmentation equivalence. For each resolution I in the
normalization predicate, it transfers the given cycles to J, applies the two
augmentation formulas there, and cancels the coefficient equivalence. The total
transfer need not be invertible. The node copies describe this actual argument.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_etaleAdditiveCech_normalized`
(lem-pbc-etale-additive-cech-normalized-existence).

Fully proved the new theorem
`AlgebraicGeometry.Scheme.Modules.exists_additiveCech_resolution_transfer`
(lem-pbc-etale-additive-cech-resolution-transfer), including its three private
lemmas and the actual total-transfer construction.

One new hole remains:
`AlgebraicGeometry.Scheme.Modules.exists_additiveCech_augmentation_homology`
(lem-pbc-etale-additive-cech-augmentation-homology).
It compares actual augmentation maps on one fixed resolution, without Ext
normalization or resolution independence. This delivery is a decomposition:
one original hole closed, one strictly smaller hole added, net zero holes closed.
The original module has no remaining sorry. No definitions contain sorry.

Resumed-worker verification: all three delivery modules compile against the current
baseline via `lcompile.py --all`. The fixed-resolution augmentation statement
and the transfer proof were read against the normalization predicate; the
combining proof transfers cycle representatives and their equal homology classes
and uses the supplied canonical comparison equation. Existing signatures and
visibility are unchanged. The unit realization route is retained.

Edge cases checked mathematically: degree zero uses sheaf gluing; empty tuple
intersections have zero section groups; an empty cover forces the scheme empty.
The transfer theorem requires no covering or affineness assumption. The cycle
lift clauses ensure the remaining lemma determines its equivalences on every
homology class, rather than imposing formulas on an empty set of representatives.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural` and
`Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison` from the assigned
module; their nodes are now used only in the augmentation lemma's proof plan.
They are not pruned from the full dependency closure.

No original proof-dependency node is globally pruned. No other module is asserted
unreachable. The unvalidated transfer draft's proposed total-homology invertibility
step and cancellation are unnecessary: the proof only maps an equality forward.
An experimental `WeilConjectures.Topology.Sheaves.CechComparison` import was removed
from the new transfer module because product-map naturality suffices.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's missing EtaleAdditiveCechNormalization.olean is now available
in the refreshed baseline. The deliverable uses that baseline module unchanged.
The sandbox has no copied dependency source in the delivery.

The original proof dependencies give an unnormalized finite Čech equivalence and a
canonical resolution comparison, but do not state the equations for the actual
alpha/beta components. The new augmentation lemma states precisely that remaining
step. The original plan's cancellation of an invertible total transfer is stronger
than needed; transferring both cycle classes into the fixed resolution suffices.

## New nodes

`lem-pbc-etale-additive-cech-augmentation-homology`, in
`lean/Sheaf/AlgebraicGeometry/Curve/EtaleAdditiveCechAugmentationHomology.lean`:
the actual global and coefficient augmentation homology equivalences on one
resolution, including cycle lifts and the representative formulas. Source:
Stacks Project [03P2](https://stacks.math.columbia.edu/tag/03P2), separated affine-cover
argument, and [01FD](https://stacks.math.columbia.edu/tag/01FD), augmented total-complex
diagram. The proof plan uses the existing injective-row augmentation criterion,
first-quadrant total comparison, unit tensor coordinates, and affine finite Čech
acyclicity. Searches found unnormalized comparisons but no exact replacement.

`lem-pbc-etale-additive-cech-resolution-transfer`, in
`lean/Sheaf/AlgebraicGeometry/Curve/EtaleAdditiveCechResolutionTransfer.lean`:
identity-resolution transfer commuting with alpha, beta and all supplied canonical
global comparisons. This theorem is proved using Mathlib's resolution lift,
product and total-map naturality, the Hom-to-sections adjunction, surjectivity of
homologyπ and extMk postcomposition. Source: the identity case of the augmentation
diagram in Stacks Project Tag 01FD. No change record is needed: no existing
statement, definition or public import changed.

## Second reading by W2

1. Compared the delivered normalized-existence module with the repository version. The
   theorem signature and existing declaration visibility are unchanged; only proof imports
   and proof text changed. Verdict: pass.
2. Compiled all three delivery modules with `lcompile.py --all`; the normalized target and
   transfer proof compile without errors. The only remaining `sorry` is the named public
   augmentation-homology theorem, with its matching DAG node; no definitions contain
   `sorry`, and no forbidden declarations occur. Verdict: pass.
3. Read the split-off augmentation-homology statement and transfer theorem. Both are
   concrete, strictly smaller than the original target, preserve the actual augmentation
   maps, and include representative formulas that determine the homology maps. Their
   source, proof plan, and Lean declarations agree with the new DAG nodes. Verdict: pass.
4. Checked the proof route and imports. The target uses the fixed-resolution augmentation
   comparison and the identity-resolution transfer; removed direct imports are no longer
   needed by the target proof, while the new modules retain the imports used by their
   statements and proofs. Verdict: pass.
5. Checked unit and node bookkeeping. The normalized target's proof follows the realized
   route through canonical comparison, augmentation homology, and transfer; proof_deps and
   proof text match the Lean proof, and the unit realization is retained. Verdict: pass.

No repair was needed in the delivered Lean code. The only outstanding hole is the explicitly
named augmentation-homology comparison, which is a valid decomposition recorded in its node.

Second-reading evidence: scratch copies with `#print axioms` compiled successfully.
The transfer theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`;
the augmentation lemma and normalized existence theorem additionally use `sorryAx`,
as expected from the remaining named hole and upstream open proofs. Independent
Lean Finder search for "homology equivalences induced by two augmentations of an
etale resolution double complex" returned resolution homotopy equivalences and
unrelated algebraic etaleness results; Loogle for `quasiIso_of_column_augmentation`
returned no Mathlib match. A repository search for `additiveCech` and augmentation
homology found the existing common-representative, cycle-realization, scalar and
inverse-image statements, none of which gives the two prescribed fixed-resolution
homology equivalences. The proved first-quadrant criterion and injective row
augmentation are relevant reusable parts, but constructing the coefficient chain
map and proving its quasi-isomorphism is substantial and was not replaced by a
bare existing equivalence.

The cycle-lift clauses, injectivity of iCycles and surjectivity of homologyπ make
p and q unique, so the existential lemma determines the data used downstream.
For n=0 the augmentation is the gluing restriction; for a one-member affine
cover it identifies the same section and kills higher cohomology. Empty
intersections have zero sections, and an empty covering forces the empty scheme;
there is no missing nonempty hypothesis. The unit's `realized` nodes are unchanged:
this reduction occurs below its curve-calculation steps. The existing target
docstring describes a stronger invertible-transfer cancellation than the proof
needs; the actual forward-transfer argument is recorded in the node and report.
