## What changed

Proved `AlgebraicGeometry.coherentFormalModule_limit_quotient` in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitQuotient`, with its signature unchanged.
Added one proved private helper: `affine_projection` (transport of the module-limit
projection theorem to sheaf sections).
Added proof imports of `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`
for local surjectivity implying epi and
`WeilConjectures.AlgebraicGeometry.Modules.TensorSection` for pure tensor sections,
and `Mathlib.Topology.Sheaves.SheafCondition.Sites` for basis morphism extensionality.

The proof uses `formalModuleQuotient_factor` and level annihilation to show the ideal
product is killed by the projection. The affine kernel formula and pure tensor sections
show its cokernel projection kills the kernel of the level projection. Two cokernel
descents give inverse morphisms. Updated the node's proof and dependencies accordingly.
No definition, existing signature, public import, or other module was changed.

Repair of the landing-tool return: removed the duplicate private theorem
`AlgebraicGeometry.hom_zero_of_affine`. The theorem named in the return,
`AlgebraicGeometry.Scheme.hom_zero_of_affine` in
`Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerImage`, is private and cannot be
used by an ordinary import. Instead the kernel composite is checked directly using
Mathlib's existing public `TopCat.Sheaf.hom_ext`, after applying the faithful
`SheafOfModules.toSheaf` functor. There is no replacement sheaf-separatedness theorem
in this delivery. Removed the previous second-reading section because it described
the returned version; the repaired version needs an independent second reading.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.coherentFormalModule_limit_quotient`
(node `lem-weil-pbc-coherent-formal-module-limit-quotient`).
There are no remaining sorries in the item and no added holes or new modules.
The existing affine projection and ideal-power affine-sections declarations are used
as supplied; their downstream proof status is not changed by this delivery.

The repaired module compiles without warnings using the launcher single-file compiler.
The proof requires no nonempty scheme, nonzero ideal, or positive-rank assumption:
empty schemes, the zero and unit ideals, and n=0 use the same construction.

## No longer needed

No imports, dependency nodes, or modules were removed. Both original proof dependencies
are used. The duplicate `AlgebraicGeometry.hom_zero_of_affine` helper is removed;
Mathlib's existing basis extensionality theorem supplies this argument directly.
`Sheaf.AlgebraicGeometry.ClosedImmersionIdealPowerImage` is not needed as an import:
its private helper is inaccessible, and its closed-immersion image theorem is unrelated
to this proof. The tensor-stalk generation argument in the old plan is unnecessary:
`formalModuleQuotient_factor` and level annihilation prove that inclusion directly.
No explicit equality of image and kernel subobjects is required; the two zero composites
suffice for constructing inverse cokernel descents. These are proof-step simplifications,
not claims that any still-imported module leaves the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated a private affine-separatedness lemma already present
in `ClosedImmersionIdealPowerImage`. The repair reuses the public generic Mathlib
basis extensionality API, rather than changing the visibility of another item's helper.
No statement error was found. The original proof plan is valid but its image/kernel
comparison can be implemented more directly as two cokernel descents. In particular,
quasi-coherence of the inverse-limit sheaf and preservation of arbitrary images by
section evaluation are neither assumed nor used. The unit's prescribed route is kept.

Searches: LeanFinder returned adic-completion results but no matching sheaf theorem;
Loogle did not resolve the queried cokernel/IsColimit combination. The launcher's grep
search returned generic cokernel APIs. Direct rg searches of the two library roots
and Mathlib found the affine projection theorem, the existing ideal-power naturality
factorization, pure tensor section identities, and `Abelian.epiDesc`/`comp_epiDesc`.

## Second reading by G1

1. **No accidental visible changes.** Compared the delivered module and node with the repository versions. The public theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, a private helper, the proof body, and DAG proof metadata differ. Verdict: pass.

2. **Proof validity.** Compiled `Sheaf/AlgebraicGeometry/CoherentFormalModuleLimitQuotient.lean` with the launcher compiler. The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The proof constructs the quotient isomorphism by cokernel descents and uses only the stated affine projection, factorization, and ideal-section results. Verdict: pass.

3. **Statements and dependencies.** No new public statement or split-off theorem was added. The private `affine_projection` helper is a transport lemma and introduces no interface. The node's proof steps and `proof_deps` now match the declarations actually used, including the formal-module factorization node. Verdict: pass.

4. **Shortest route and pruning.** The proof avoids the earlier tensor-stalk image comparison: the inclusion is obtained directly from `formalModuleQuotient_factor`, while the reverse kernel vanishing uses affine sections and pure tensors only where needed. The unit route through affine projection and ideal-power affine sections remains intact. No unused imported dependency remains. Verdict: pass.

5. **Node and unit agreement.** The node records the revised proof steps, dependencies, and origin; no statement or definition changed, and no new node is required. Edge cases (empty scheme, zero/unit ideal, and `n = 0`) are covered uniformly by the categorical argument. Verdict: pass.

Changed in this second reading: restored this required review section and verified the repaired public `TopCat.Sheaf.hom_ext` argument replaces the inaccessible duplicate private helper.
