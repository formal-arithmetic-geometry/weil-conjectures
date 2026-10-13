## What changed

Proved `AlgebraicGeometry.Scheme.exists_affine_cover_module_embedding` with its signature,
visibility, and existing docstring unchanged. Constructed the finite affine cover coproduct
and its descent map, proved the component maps affine by the affine-diagonal intersection
criterion, and used the existing finite-coproduct affine-morphism theorem. Chose the actual
module pullback for G and the adjunction unit for the embedding.

Added private, fully proved helpers `jointlyFaithful_restrict_cover` and
`faithful_pullback_cover`. Open-cover restriction reflects isomorphisms by the existing
flat-cover source theorem, preserves equalizers, and is consequently jointly faithful.
Pullback composition then proves the cover pullback faithful, so its adjunction unit is monic.
Added proof-only imports of `WeilConjectures.AlgebraicGeometry.Modules.AmpleFamily`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`,
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`, and
`Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`. Each supplies a used declaration.
Updated the item's node to match this argument and recorded the already proved source tool.
No definition, statement, public import, or other module changed.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Scheme.exists_affine_cover_module_embedding`
(node `lem-sc-picard-affine-cover-module-embedding`). No `sorry` remains in the delivered
module, and no hole was added. This is a proof, not a decomposition. Both private helpers
are complete. Local compilation passes without warnings. The construction uses the actual
finite cover, coproduct, pullback functor value and unit, with no arbitrary module data
chosen from an unproved existence statement. The empty scheme and zero module require no
extra assumptions or case exclusions.

## No longer needed

None of the original imports or original proof-dependency nodes can be pruned: finite affine
coproducts and affine-diagonal intersections are both used. No cohomological vanishing,
acyclicity, module-stalk tensor formula, or new unproved intermediate statement is needed.
The new reflection node records a theorem that is already proved in the source library;
it introduces no work item with an open proof.

## Where the brief, the DAG or earlier work was wrong

The old step 3 called the whole stalk-injectivity and quasi-coherence argument elementary
without naming its reusable ingredients. The proof now names the existing quasi-coherent
pullback and restriction-limit nodes, and records the already proved flat-cover reflection
theorem. The categorical argument proves monicity without an explicit pullback-stalk formula.
This realizes the same geometric construction; the unit route is unchanged.
`tools/blueprint_refs.py search` for flat pullback and isomorphism reflection found no blueprint
statement for the new source tool. No statement was found false or changed.

## New nodes

`lem-sc-flat-cover-module-isomorphism-reflection` records the existing, fully proved
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_map` in
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`. Its statement applies to
arbitrary modules and jointly surjective flat families, so it specializes to this open cover.
The node includes the complete source proof in words and the three search kinds; LeanSearch
was unavailable and is recorded as such. It adds no Lean module and no hole. No change record
is necessary because no interface changed.

## Second reading by V3

1. Compared the delivered module with the repository version. The existing theorem
   signature, visibility, and docstring are byte-for-byte unchanged. Only proof imports,
   two private proof helpers, and its proof were added; no change record is required.
2. Local compilation passes without errors or warnings. No sorry, axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition occurs in the delivered module. The
   witnesses are the concrete finite coproduct, sigma-desc morphism, pullback module,
   and adjunction unit. Scratch-copy axiom probes for the embedding and source reflection theorem show
   only propext, Classical.choice, and Quot.sound, with no sorryAx.
3. No statements were split off with sorry. The new reflection node records the exact
   existing source theorem, with its complete source proof in words. It applies to
   arbitrary modules and jointly covering flat families, including empty schemes.
   The finite cover and zero module cases introduce no additional assumptions.
4. Reviewed the finite-cover construction, affine-diagonal criterion, faithful pullback
   reduction, and monic adjunction unit. These retain the unit's geometric embedding
   route; the helpers replace only the stalk-injectivity implementation. Original
   imports and dependencies are used; none can be pruned.
5. Checked the DAG proof steps, proof_deps, proof_origin, new node fields, and Lean
   signatures against the actual declarations and their sources. They match the proof.

Second reading verdict: accepted unchanged proof and statements. Added this review
section; no code repair was necessary.

Additional second-reader searches: LeanFinder on faithful open-cover pullback found
only categorical over-pullback faithfulness and open-immersion pushforward faithfulness,
neither of which replaces this module argument. Loogle on adjunctions and monomorphisms
confirmed `Adjunction.unit_mono_of_L_faithful`, already used by typeclass inference.
A local search for faithful pullback and affine-cover embeddings found no shorter existing
module embedding theorem. Read the reflection source proof and the equalizer argument in
Mathlib's `JointlyReflectIsomorphisms.jointlyFaithful`. The unit record's `realized` lists
are currently empty; this delivery leaves them unchanged and does not bypass any listed
unit realization. This pre-existing bookkeeping gap does not change the embedding route.
