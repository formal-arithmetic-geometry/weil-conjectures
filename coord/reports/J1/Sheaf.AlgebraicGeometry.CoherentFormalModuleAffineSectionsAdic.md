## What changed

Proved `AlgebraicGeometry.coherentFormalModule_affine_sections_adic` in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineSectionsAdic`. Its existing statement,
universe, visibility, and docstring remain byte-identical. No definition changes,
new statements, forced adaptations, or change records are needed.

The proof obtains finite sections from coherence, computes ideal-power multiplication
ranges, transports the submodules along the Spec global-sections scalar isomorphism,
and identifies successor transitions with the specified quotient isomorphisms.
All three original DAG steps and all original proof dependencies remain used.

Second reading removed the two duplicated private multiplication helpers and reused
`AlgebraicGeometry.Scheme.Modules.product_qc` and
`AlgebraicGeometry.Scheme.Modules.multiplication_range` through proof-only
`import all Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
It also reused `AlgebraicGeometry.Scheme.Modules.finite_sections_of_finiteType` through
proof-only `import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
This eliminates the added `FinitePushforwardCoherent` and tensor comparison imports.
The remaining new imports are proof-only:
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
The node's proof, proof dependencies, and proof origin describe the final implementation.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.coherentFormalModule_affine_sections_adic`
(node `lem-weil-pbc-coherent-formal-module-affine-sections-adic`).
Added zero holes; no `sorry` remains in the delivered module.
This is a proof, not a decomposition. Independent compilation of a scratch copy of
its final source with `#print axioms` succeeded without errors or warnings in 9.4 seconds:
only `propext`, `Classical.choice`, and `Quot.sound` occur, with no `sorryAx`.

## No longer needed

No original import, proof dependency, or module is pruned. Every old `proof_deps` is
retained. Relative to the first worker's sandbox, removed the added imports
`Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` and
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`, and their newly
added direct node dependencies. These were absent from the repository baseline and
are not counted as original-module pruning. Their relevant ingredients are already
available in the original dependencies' proved helpers.

## Where the brief, the DAG or earlier work was wrong

The return at fe46b4136 correctly identified a duplicated finite-type restriction proof.
The first worker's repair reused that restriction helper, but a shorter existing route
is the finite-section helper in the original affine finite-type dependency.
The multiplication helpers also duplicated existing proofs. Contrary to the earlier
reading's claim, private helpers can be reused with proof-only `import all`; the library
already uses precisely this method in `CoherentFormalModuleAffineOpenSectionsAdic`.
The second reading repaired both duplications rather than adding library statements.

The source reduction was independently read in
[Stacks Lemma 087W](https://stacks.math.columbia.edu/tag/087W), first proof paragraph.
It matches the finite-level adic tower assertion, with index n representing level n+1.
No target statements, definitions, unit statements, or unit realizations changed.

## Second reading by J1

1. **Interface: PASS.** Compared the whole module with the repository using `diff`
   and the stage-3 declaration parser; the existing theorem signature is byte-identical,
   as are its docstring and public imports. Only its proof and proof-only imports change.
   No new public declaration or data construction is introduced.
2. **Proof and axioms: PASS.** Compiled the revised source using only `lcompile.py`.
   A scratch copy with `#print axioms` for the sole delivered theorem compiled cleanly;
   its axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
   The delivered source contains no `sorry`, forbidden declaration, or hollow definition.
   The quotient isomorphism is input data from F's formal-system property; no arbitrary
   data are chosen from an unproved existence theorem.
3. **Split statements and edge cases: PASS.** No split statement, node, or hole is added.
   Read the reused finite-sections and product/range helpers and the cokernel theorem.
   The range calculation needs only quasi-coherence of K and M, not monicity of K -> O.
   Checked n=0 (power one), I=0 (successor isomorphisms), I=top (all levels zero),
   and the zero ring. None requires an unstated hypothesis.
4. **Route and pruning: PASS after repair.** Read the original node's three steps,
   `dag/units/sk-thm-p1.json` including `realized`, and Stacks 087W's affine reduction.
   All original dependencies remain used and the unit route is preserved. Independently
   ran LeanFinder for finite-type restriction, Loogle for scalar restriction of ideal
   products, and local `rg` searches with different terms. These searches identified
   reusable private helpers and existing `import all` examples. Replaced both duplicated
   multiplication helpers with calls to the original dependency; used its finite-section
   counterpart for finiteness. Every retained import supplies a statement ingredient or
   an explicitly used proof declaration. No original dependency is unused.
5. **DAG: PASS after repair.** Compared node JSON against the repository: only `proof`,
   `proof_deps`, and `proof_origin` change. The dependency set is exactly the union of
   each step's `uses` and contains all original dependencies. The only new direct node
   dependency is the cokernel/image theorem, explicitly used for successor quotients.
   No node creation or change record is required; all reused helpers are already proved.

Second reading changed the Lean proof to reuse three existing private helpers,
removed two added imports/dependencies and both duplicated helper declarations,
and updated this report and the node to match. Closed one original hole, added zero.
