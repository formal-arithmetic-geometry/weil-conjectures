## What changed

The unchanged target `AlgebraicGeometry.Scheme.Modules.moduleCechBeta_quasiIso_of_affine`
now has a complete Lean reduction to two strictly smaller theorem interfaces. The
proof evaluates the already proved affine vanishing theorem on every intersection,
constructs the Cech augmentation, proves its composite with the resolution differential
is zero by functoriality, and applies the column-to-total criterion. Beta's degreewise
identification with this augmentation is proved by reflexivity.

New proof-only imports are `Sheaf.AlgebraicGeometry.ModuleCechResolutionColumns` and
`Sheaf.Algebra.Homology.FirstQuadrantAugmentation`. Each new module contains one named
public theorem with its source, full proof in words, and matching node. The target's
node now records this Lean route. All three modules compile together without warnings.

## Proved and sorry left

Closed the target's direct hole:
`AlgebraicGeometry.Scheme.Modules.moduleCechBeta_quasiIso_of_affine`
(node `lem-sc-module-cech-beta-affine-quasi-iso`). There is no sorry left in the item.

Added two holes:
- `AlgebraicGeometry.Scheme.Modules.moduleCech_resolution_columns`
  (node `lem-sc-module-cech-resolution-columns`): computes the resolution-direction
  column augmentation under intersection cohomology vanishing, without totalization,
  affineness, or quasi-coherence hypotheses.
- `HomologicalComplex₂.quasiIso_of_column_augmentation`
  (node `lem-sc-first-quadrant-column-augmentation`): the general abelian-category
  first-quadrant homological criterion, with no scheme or sheaf hypotheses.

This is a decomposition: one upper hole closed and two lower holes added, net -1;
it is not a sorry-free proof of the underlying argument. The target combines the
local column calculation and the independent totalization calculation with real Lean
code, including the augmentation equation and beta component identification.

## No longer needed

Removed the item's direct proof import of `Sheaf.Topology.RestrictInjectiveResolution`;
that module is still needed by the new column calculation, and is imported there.
Removed the item's direct proof import of
`WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`; it remains the infrastructure
of the general criterion and of the already imported comparison definition.
No module is removed from the target's import closure. No original dependency is
mathematically pruned: restriction and the spectral-sequence theorem move into the
specific intermediate nodes that need them. The comparison construction and affine
vanishing remain direct dependencies of the target proof. No unit route is bypassed;
`sk-thm-picard-duality.realized` has no statement or step nodes to replace.

## Where the brief, the DAG or earlier work was wrong

The original stated dependencies do not package product column exactness or the
augmentation-to-total quasi-isomorphism criterion. The spectral-sequence theorem
asserts existence of pages and abutment; its statement does not assert naturality
of an edge map or identify the particular beta homology morphism. The new general
criterion explicitly fixes the map by its components, so this missing compatibility
is included in the remaining homological work rather than assumed.

Sources read: Stacks Tags 01EQ, 01ES, 01ET, 012X, and 0133. Tag 0133 is the precise
Lemma 12.25.4 referenced in the original plan. The new local statement is valid
without an open-cover hypothesis, since it only computes sections on each intersection.
The generic statement is valid for arbitrary abelian categories: diagonals are finite,
so no exactness of infinite products or coproducts is required there. Empty index types
in the local statement produce zero product columns; the generic zero bicomplex and
single-resolution-degree cases agree with the stated criterion. The chosen maps are
actual constructions; no data is chosen from an unproved existence theorem.

## New nodes

`lem-sc-module-cech-resolution-columns` in
`Sheaf.AlgebraicGeometry.ModuleCechResolutionColumns` packages the positive cohomology
vanishing, degree-zero left exactness, and exact products over tuples. Its statement
has no total complex conclusion. The universally supplied augmentation equation is
proved by the target, and the theorem only establishes column quasi-isomorphisms.

`lem-sc-first-quadrant-column-augmentation` in
`Sheaf.Algebra.Homology.FirstQuadrantAugmentation` is the general criterion of
[Stacks Tag 0133](https://stacks.math.columbia.edu/tag/0133), with the resolution degree
first. It supplies the finite diagonal cone argument and the identification of the
map via its degreewise components. The two nodes have distinct jobs and neither
restates the target. No existing definition or statement changes, so no change record
is required.

## Second reading by M1

1. I compared the delivered target module with the repository version. The target theorem signature is unchanged byte for byte; only its proof and proof-only imports changed. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. The target closes its original sorry. The two added public statements are strictly smaller interfaces: one computes each resolution column and the other is the abstract first-quadrant totalization criterion. Their hypotheses and conclusions match the uses in the target and introduce no altered definition. Verdict: pass.
3. The remaining sorries occur only in the two named split-off theorems, each with a source, a natural-language proof, and a matching DAG node. No sorry occurs in a definition; no axiom, unsafe, opaque, extern, or implemented_by declaration occurs. Verdict: pass.
4. The target proof follows the shortest available route through affine vanishing, the explicit column augmentation, and the first-quadrant criterion. Imports used only by the old proof were removed from the target and retained in the specific intermediate module that needs them. The report's no-longer-needed list records this pruning. Verdict: pass.
5. The target node's proof and proof_deps now match the Lean proof, and both new nodes record their statements, sources, proof steps, and Lean declarations. The unit route remains realized by the target node. Verdict: pass.

I changed only this report section; no Lean statement or definition was changed in the second reading.
