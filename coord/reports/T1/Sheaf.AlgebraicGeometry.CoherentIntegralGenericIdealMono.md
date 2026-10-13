## What changed

Proved `AlgebraicGeometry.Scheme.Modules.mono_of_coherent_ideal_sum_generic_iso`
in `Sheaf.AlgebraicGeometry.CoherentIntegralGenericIdealMono`, with its signature unchanged.
Added the proved private helper `ideal_map_eq_zero_of_generic_stalk`. It reflects the
vanishing of the generic stalk map for maps into an ideal, by composing with its
inclusion into the structure sheaf and using injectivity of restriction on integral
schemes. Cancellation on the generic stalk and finite biproduct projection
extensionality then prove that the kernel inclusion is zero.

Replaced the unused proof-dependency imports with the direct statement imports
`Mathlib.AlgebraicGeometry.Noetherian` and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`.
Added the proof-only import `Mathlib.CategoryTheory.Preadditive.Biproducts`.
Updated the item's DAG proof and dependencies to this shorter route. The item and
removed dependency nodes are not realizers of `sk-thm-p1`'s statement or steps;
the unit's route is unchanged. No statement, definition, or other module changed.
The import-interface change is recorded in
`coord/changes/CoherentIntegralGenericIdealMonoImports.md`; the sole direct importer
already imports every removed public dependency independently and needs no adaptation.

The shorter proof does not use the coherence hypotheses; a declaration-scoped
unused-variable linter option preserves all existing binder names and types.
Compilation is clean. The helper treats the empty open by sheaf section extensionality;
the argument also works when the ideal is zero or when `r = 0`.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.mono_of_coherent_ideal_sum_generic_iso`
(node `lem-weil-pbc-coherent-integral-generic-ideal-map-mono`).
Added 0 holes. No `sorry` remains in the item or in a new module.
The private helper `ideal_map_eq_zero_of_generic_stalk` is fully proved.
This is a proof, not a decomposition into additional holed statements.

## No longer needed

The repair removes the unused proof-only import
`Mathlib.AlgebraicGeometry.FunctionField`; `map_injective_of_isIntegral` is supplied
by the existing imports through `Mathlib.AlgebraicGeometry.Properties`.

Removed the following imports and their proof-dependency edges from this item:

- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
  (`lem-weil-pbc-coherent-kernel-cokernel-locnoeth`): the proof does not need
  a coherent kernel.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
  (`lem-weil-pbc-quasi-coherent-module-cokernel-image`): it does not construct
  coordinate image ideals or need their quasi-coherence.
- `Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk`
  (`lem-weil-pbc-integral-scheme-ideal-generic-stalk`): sectionwise integral
  restriction injectivity replaces the generic-stalk ideal criterion.
- `Sheaf.Algebra.Homology.ModuleStalkExact`
  (`lem-weil-pbc-module-stalk-exact`): cancellation of the isomorphic generic
  stalk map suffices; the proof uses no preservation of kernels or exactness.

All four original proof dependencies are pruned from this item's proof. Other
callers may still need these modules; this delivery makes no global reachability claim.
The two direct Sheaf statement imports, `Coherent` and `ModuleStalkFunctor`, remain.

## Where the brief, the DAG or earlier work was wrong

The planned proof was valid but stronger machinery than necessary: maps into the
ideal already have their vanishing detected by the generic stalk, since the ideal
embeds in the structure sheaf. The proof therefore requires neither coherent
kernels nor quasi-coherent coordinate images, nor exactness of stalks.
The original declaration docstring records the former plan and says its formal
proof is left for the next worker; the proof below it is now complete and uses
the shorter route recorded in the DAG and this report.

## Earlier second reading (a previous round; superseded)

1. **Interface and statements.** Compared the delivered module with the repository version. The
   theorem signature is byte-for-byte unchanged; no target or definition was altered. The helper is
   private and introduces no public interface.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; compilation succeeds with no
   warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`
   declarations. The proof uses only generic-stalk functoriality, integral restriction injectivity,
   and biproduct projections, and leaves no open theorem.

3. **Statements and nodes.** The existing node statement remains exactly the theorem statement.
   Its revised proof, dependencies, and origin match the Lean proof. No new split-off statement or
   node was added, and the private helper is fully proved.

4. **Pruning and imports.** Removed imports are genuinely unused by the proof and are listed in
   `## No longer needed`; proof-only Mathlib imports are private. The direct downstream importer
   already supplies the removed public dependencies, so no adaptation is required.

5. **Unit route.** The unit `sk-thm-p1` route is preserved: generic-stalk kernel vanishing,
   coordinate projection, and monomorphism from zero kernel remain the same mathematical steps,
   with the unnecessary coherence and exactness machinery pruned.

Changed only the completed proof, its DAG proof metadata, the import change record, and this report.


## Second reading by T1

1. **Unchanged visible declarations: PASS.** Compared the delivered Lean file and node with
   the repository using a diff and byte comparison of the entire original theorem signature.
   All original binders, universes, instance assumptions, coherence hypotheses, and the `Mono χ`
   conclusion are unchanged. No definition or target changed. The public-import replacement has
   its change record. The sole direct importer, `CoherentIntegralGenericIdealMap`, independently
   imports the removed public dependencies and replacement statement modules; it compiles
   against the delivered module without adaptation.

2. **Proof and axioms: PASS.** Compiled the item and its direct importer locally through
   `lcompile.py`. In a scratch copy, `#print axioms` for both the private helper and
   `mono_of_coherent_ideal_sum_generic_iso` reports exactly `propext`, `Classical.choice`, and
   `Quot.sound`. No `sorry` or forbidden declaration is present. The proof cancels the
   isomorphic generic stalk of χ against the stalk of the kernel inclusion, proves each
   biproduct coordinate zero, and concludes by the abelian zero-kernel criterion.

3. **Split statements and edge cases: PASS.** No statement or hole was split off and no new
   node was added. The proved private helper works for arbitrary source modules: an ideal
   embeds in the structure sheaf, whose germ maps on an integral scheme are injective.
   An empty open is handled by sheaf section extensionality with no points; for the zero ideal
   inclusion cancellation still applies; for `r = 0` biproduct extensionality has no coordinates.
   No arbitrary data is chosen from an unproved existence theorem. Searched the local Sheaf and
   upstream sources and Mathlib using generic-map, injectivity, and stalk-zero terminology.
   Found Mathlib `germ_injective_of_isIntegral`, but it concerns the CommRingCat stalk,
   whereas the helper uses the Ab stalk. A scratch replacement fails due to these different
   colimit carriers. The existing short restriction argument avoids a new comparison lemma
   and its extra import, so it is retained.

4. **Top-down route and pruning: PASS.** The route uses Mathlib kernel cancellation and finite
   biproduct extensionality directly, without holed coherent-kernel or image results. Every one
   of the four original `proof_deps` is listed in `## No longer needed`. Each retained public
   import supplies a notion in the signature; the private biproduct import supplies proof lemmas.
   Checked `dag/units/sk-thm-p1.json`: neither the item nor the four pruned dependencies realizes
   its statement or a step, so this shorter route preserves the unit route.

5. **DAG agreement: PASS.** The existing node's statement and Lean record are unchanged.
   Its proof steps match generic-stalk cancellation, ideal-map vanishing, and biproduct
   coordinate extensionality; its `proof_deps` equals the union of step `uses`, and its
   `proof_origin` records the shortened coordinatewise route. No DAG repair is needed.

Second reading changed only this report. The attempted generic-germ simplification was
reverted after checking its incompatible stalk carrier; Lean, the node, and the import change
record retain the original correct delivery. Closed 1 of 1 original holes; added 0 holes.
No statement changed.
