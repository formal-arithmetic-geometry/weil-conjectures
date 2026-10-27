## What changed

Withdraw `Sheaf.AlgebraicGeometry.FiniteLisseFieldDualHomology` under brief step 8d.
Its sole parent `Sheaf.AlgebraicGeometry.FiniteLisseFieldDual` is unclaimed and now
proves its unchanged statement directly from the already proved adopted source module
`WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual`.

The existing global bounds give `C.IsGE a` and `C.IsLE b`. Over the finite field
`ULift (ZMod ell)`, `isFiniteLocallyConstantSheaf_homology_coefficientDual` proves
both the finite local constancy and cohomology-dual formula. The proved
`isIso_coefficientDualComparison_of_isFiniteLocallyConstantSheaf` proves the
canonical pullback comparison, definitionally the map already defined by the parent.
Every existing parent signature, definition, public import and attribute is unchanged.
The private helpers `dualPullback_isIso_of_exactPairing` and `finiteLisseDualPullbackComparison_isIso`, unused by the new proof, are removed (reviewer fix).

Update the parent node's proof route and dependencies, and detach the retired auxiliary
node's Lean attachment. The historical mathematical statement is retained in its DAG
node; this delivery does not claim to prove its stronger locally bounded generalization.
No target or adopted source module is modified.

Validation: the changed parent and its unchanged direct consumer
`Sheaf.AlgebraicGeometry.SmoothGenericDirectImage` compiled successfully together through
`lcompile.py`, in 29.1 s and 31.8 s respectively. The unchanged consumer was removed from
the packet after verification. An import-direction check permits the adopted source
import. The consumer is currently held by B7 and is not adapted.

## Proved and sorry left

Original item: one hole, `AlgebraicGeometry.Etale.sitePerfect_fieldDual_homology`.
Removed by pruning, not proved: that declaration and its unused auxiliary module.
Thus zero of the item's one holes are counted as proved, one is pruned, and zero
are split off or added. No sorry remains in any delivered Lean module.

`AlgebraicGeometry.Etale.finiteLisseFieldDual` remains completely proved, now from
the adopted bounded finite-lisse theorems. Its statement is unchanged. This is an
actual replacement argument at the parent, not a rebase or a relocation of a hole.

## No longer needed

The parent removes its proof-only imports of
`Sheaf.AlgebraicGeometry.FiniteLisseFieldDualHomology` and
`Sheaf.AlgebraicGeometry.FiniteLisseFieldSitePerfect`, and its now unused direct
`WeilConjectures.ConstructibleSheaf.Monoidal` import. It imports the proved adopted
`LisseFieldDual` module and the two field-instance modules instead. The proof-only
`WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect` import is removed together
with the two dead private helpers that needed it (reviewer fix).

The parent route no longer needs nodes `lem-fin-lisse-field-dual-homology`,
`lem-fin-lisse-field-site-perfect` or its separate `lem-weil-pbc-flc-dual` invocation.
Only the assigned homology module is withdrawn. The site-perfect module is retained
for any other current or future consumers; its finite-ring local-constancy machinery
is no longer needed by this parent proof.

The withdrawn item's old route no longer requires
`lem-trf-field-complex-cohomology-splitting`, `lem-weil-pbc-vector-space-projective`,
`lem-pod-projective-hom-evaluation-model`, `lemma-constructible-flc-serre`,
`lemma-constructible-hom-constant-locally`,
`lemma-weil-pbc-geometric-stalk-conservative`, or
`prop-weil-pbc-inverse-image-modules-exact`. This removes the item's former explicit
proof imports of `EtaleInverseImageModulesExact`, `DerivedCategory.Perfect`,
`KernelCokernel`, `EtalePoint` and `ConstantSheafOver`. All corresponding modules
and adopted source declarations remain intact; this is dependency pruning for this
route, not a claim that those results are globally unused.

The current Lean and DAG scans find only `FiniteLisseFieldDual` as a direct parent.
`tools/downstream.py --uses sitePerfect_fieldDual_homology` finds only that parent
and the item itself as textual users, with `SmoothGenericDirectImage` the remaining
transitive importer. Searches of quarantined sources, rework records and unit records
find no hidden parent. `sk-prop-sf-cbc.realized` has empty statement and step arrays,
so no realized unit statement or step is bypassed. The actual parent replacement and
its node dependency updates accompany the withdrawal in this packet.

## Where the brief, the DAG or earlier work was wrong

The earlier route introduced a stronger site-perfect local-amplitude obligation even
though its only parent already had global bounds. The source library already contains
fully proved bounded finite-lisse duality and canonical comparison theorems matching
that parent's hypotheses and conclusions. Reusing them eliminates the auxiliary
obligation entirely. The existing source proof uses finite-lisse exact pairings and
truncation devissage; it does not import the withdrawn Sheaf auxiliary module.

The adopted source-library boundary is respected: no existing source declaration,
proof, import or attribute is removed or modified. The parent comparison definition
is also untouched. Zero objects, empty schemes and reversed/degenerate cohomological
bounds are handled by the same existing bounded theorem; the supplied IsGE/IsLE
instances use the original vanishing hypothesis verbatim.

Change record: `coord/changes/finite-lisse-field-dual-prune-homology.md`.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
