## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.LocalUniformHigherDirectImageBound` by a
compiled open-induction proof. The statement, universes, binders, and visibility are unchanged.
The induction property bounds cohomology on `W ⊓ g ⁻¹ᵁ V` simultaneously for every
quasi-coherent module on the inverse-image scheme and every affine open V of the affine base.
Only affine open base changes are necessary; arbitrary affine scheme base changes are omitted.

The affine case uses Mathlib's affineness of a morphism between affine schemes, the
inverse-image/image identities for opens, and the existing affine-open module-cohomology
vanishing theorem. A proved private helper uses the last exactness position of the existing
ringed-space Mayer–Vietoris sequence to kill the union cohomology. The induction step chooses
`max (max a b) c + 1`; Lean verifies all three degree inequalities and the lattice identities.
The final step specializes the bound to the restriction of the original module.

The passage from this cohomology bound to restricted ordinary higher-direct-image vanishing
is isolated in `Sheaf.AlgebraicGeometry.HigherDirectImageAffineBasisVanishing`. Its one theorem
is general in f, U, F and p, assumes an explicit affine-basis vanishing condition, and has no
quasi-coherence or qcqs hypotheses. It contains no choice of data, no uniform-bound existence
assertion, and no point-neighbourhood conclusion. It is strictly the final comparison step,
not a renamed copy of the original theorem.

Read Stacks Tags 01XJ, 08DR, 01EB, 01E1 and 01E4 from the official Stacks pages; the local
`literature/stacks-project` source is absent on this machine. No repository files were manually
written. Compilation used only the prescribed lcompile launcher.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_local_uniform_higherDirectImage_bound`
(node `lem-pc-local-uniform-higher-direct-image-bound`). It has a complete Lean proof from
existing declarations and the one new comparison lemma.

Added one hole:
`AlgebraicGeometry.isZero_restrict_higherDirectImage_of_affine_basis`
(node `lem-pc-higher-direct-image-affine-basis-vanishing`). Its proof is exactly `by sorry`;
its docstring and node give the restricted-resolution, sheafification and stalk argument.
There are no other sorries in the delivered files. The private Mayer–Vietoris helper
`isZero_openCohomology_union` is proved.

This is a decomposition, closing one upper hole and adding one strictly smaller lower hole,
not a claim of a net reduction in the number of holes. Existing imported declarations may
still depend on other sorries, as intended by stage 3.

Edge cases checked: the induction's empty affine chart uses positive-degree affine-open
vanishing; no nonempty source hypothesis is used. The successor bound ensures p is positive
in the union step and the intersection is used at degree p-1. The affine-basis criterion
includes degree zero, empty U and empty inverse image, and imposes no unjustified separatedness
or quasi-coherence hypothesis. The choices of U and n precede the input module M.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover`: replaced by
  `Sheaf.Topology.ModuleMayerVietoris`, which applies directly on the inverse-image scheme.
  Its wrapper node `lem-sc-mayer-vietoris-open-cover` is unnecessary for this proof.
- `Sheaf.Paper.HigherDirectImagePresheaf`: its node
  `lem-weil-pbc-higher-direct-image-presheaf` is now a dependency of the new comparison item,
  not a direct dependency of the original theorem. It remains transitively needed.
- `Sheaf.Topology.RestrictInjectiveResolution`: its node
  `lem-sc-ringed-space-restrict-injective-resolution` is similarly retained through the new
  comparison item, not pruned from the complete route.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`: affine vanishing is used through
  `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`, node
  `pqf-lem-affine-vanishing`. The source theorem `lem-pc-affine-vanishing` remains transitively
  needed; its direct import and direct proof-dependency edge are unnecessary.

`def-pc-fibre-product` is no longer a proof dependency: the proof uses inverse images under
morphisms between affine schemes, without constructing arbitrary fibre products.
`def-sc-open-module-cohomology` remains a statement dependency and its public import stays.
`lem-sc-invert-s-cohomology-induction` stays and is explicitly applied. No unit statement or
realized unit step is bypassed (`sk-thm-picard-duality` has empty realized bindings here).
No assertion is made that a listed module leaves every other target's import closure.

## Where the brief, the DAG or earlier work was wrong

The DAG's arbitrary-affine-base-change induction property is stronger than required for this
local conclusion. Restricting to affine opens of the chosen affine base is sufficient and
avoids constructing fibre products and transporting all coefficients along them.

The stated quasi-coherent Mayer–Vietoris wrapper is phrased on W.toScheme. Using the already
proved ringed-space version avoids an unnecessary top-open scheme equivalence. Its exactness
is sufficient for the quantitative induction step without quasi-coherence assumptions.

The source `DirectImage.Sections` local bound assumes `IsSeparated f` and chooses its bound
after the module, so it cannot prove the unchanged qcqs uniform statement. Importing it also
closes a cycle, as confirmed by import_direction.py. The existing unbounded affine-detection
theorem has different derived objects and a global conclusion; no matching ordinary restricted
comparison theorem was found. LeanSearch was unavailable; the actual failed search is recorded.

## New nodes

`lem-pc-higher-direct-image-affine-basis-vanishing`, in
`dag/nodes/sec-picard-framework/`, states the fixed-degree comparison from explicit vanishing
on inverse images of all affine opens of U to zero restricted ordinary higher direct image.
Its source is Stacks Tags 01E1 and 01E4, its module is
`Sheaf.AlgebraicGeometry.HigherDirectImageAffineBasisVanishing`, and its proof plan uses the
existing restriction-of-injective-resolutions and higher-direct-image-presheaf declarations
followed by module-stalk zero detection. It has the item's chapter and unit. No definition,
existing signature, or external module was changed; no change record is needed.

## Second reading by U2

1. The delivered module preserves the target theorem signature byte for byte; `diff` shows only proof and import changes. Verdict: pass.
2. Both delivered modules compile with `lcompile.py --all`; the original target hole is closed, and the only remaining `sorry` is the named affine-basis comparison theorem with its matching split node. No definitions contain `sorry`, and no prohibited declarations occur. Verdict: pass.
3. The split comparison statement is true, strictly smaller than the target, and adds no hypotheses to the target; its docstring gives the restricted-resolution and stalk proof, and its node records the source and dependencies. Verdict: pass.
4. The proof follows the unit route through open induction and Mayer–Vietoris, then uses the affine-basis comparison. Removed imports and dependencies are listed above; the remaining imports are used. Verdict: pass.
5. DAG `proof`, `proof_deps`, and `proof_origin` match the Lean proof, and the new node has the required fields. Verdict: pass.

I changed no declarations or statements. I verified both files by local compilation and checked the target diff, theorem axioms via the delivery probe path, import pruning, and node consistency.
