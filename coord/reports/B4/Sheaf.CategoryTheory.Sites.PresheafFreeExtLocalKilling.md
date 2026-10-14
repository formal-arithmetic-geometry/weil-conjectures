## What changed

The dispatched module already contains complete proofs of
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` and
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`. Its two private helpers,
`epi_locally_surjective` and `exists_presheaf_cover_lift`, are also proved.
The module was copied to the sandbox and compiled through lcompile.py successfully
in 16.2 seconds with no warnings. This report records verification of an already completed item. The second reading
corrects its proof docstring to match the actual epi-effacement reduction.

## Proved and sorry left

There are zero sorries in the assigned module, and this delivery closes zero holes and adds
zero holes. Both public declarations named above are already proved, with nodes
`lem-sc-presheaf-free-ext-local-killing-witness` and
`lem-sc-presheaf-free-ext-local-killing`. No statement or definition was changed.
The proof uses `CategoryTheory.Abelian.Ext.exists_epi_comp_eq_zero` from
`Sheaf.CategoryTheory.Abelian.ExtEpiEffacement`, whose checked-out proof is also complete.
The delivery dry run checks the module's transitive axioms.

## No longer needed

None. No imports, nodes or modules were removed. The existing dependency on
`lem-sc-ext-epi-effacement` is used by the witness proof; the local killing theorem uses
the witness. Both private constructions are used. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief says this module still contains sorry, but the checked-out module
contains none. Both node records already record the H2 proof landing on 2026-10-14.
The repair queue still names upstream review #1428's existential proof witness and True
padding, but the checked-out witness concludes directly with the Ext vanishing equation.
The landed change record `coord/changes/presheaf-ext-local-killing-witness-padding.md`
already documents that correction. No further correction or forced adaptation is necessary.
This is verification of completed work, not new proof progress or a decomposition.

## Second reading by B4

1. Interfaces: compared the sole delivered Lean module with the repository using diff.
   All four declaration signatures and all imports are byte-for-byte unchanged.
   Corrected the witness proof docstring to describe the actual fraction-based
   epi-effacement argument, explicit generator lift and Ext associativity. The
   sandbox initially differed only in the last proof's `simpa using`; restored the
   repository's direct `exact` application. No statement, definition or visibility
   change, new module, new node or change record is delivered.
2. Proofs: compiled a scratch copy with `#print axioms` for both private helpers and
   both public theorems through lcompile.py. It compiled without warnings in 12.4 seconds.
   Every declaration uses only propext, Classical.choice and Quot.sound; no sorryAx.
   The module has no sorry, axiom, unsafe, opaque, implemented_by or extern. The locally
   generated image and the generator-lift presheaf are explicit constructions. The
   existential epimorphism is eliminated only inside the theorem proof, not used to
   define public data.
3. Split statements: none added or left open. The existing witness is fully proved,
   so the final direct application is not a relocation of an unresolved hole. Checked
   q=1, x=0, empty-valued P and the empty site: the same construction works. Positivity
   is retained; no degree-zero vanishing is claimed.
4. Route and pruning: read the proof from the local-killing conclusion down through
   epi effacement, the explicit generator lift and the abelian image subsheaf. Searched
   both Lean roots for existing local-killing/lifting declarations and read Mathlib's
   Sites/LocallySurjective and Sites/EpiMono alternatives. The former's epi equivalence
   is for type-valued sheaves; the latter requires additional concrete sheafification
   compatibility hypotheses. Neither directly replaces the small-universe abelian
   helper under the present hypotheses. Both public imports supply signature notions
   (Ext/free abelian sheaves and local surjectivity); ExtEpiEffacement is correctly a
   plain proof import and is used. No old proof dependency is unused. Read
   dag/units/sk-prop-cd.json: its realized fields are empty, and this delivery changes
   neither its route nor its record. No imports or modules are pruned.
5. DAG: checked both associated nodes against the Lean signatures and proof bodies.
   The witness uses exactly lem-sc-ext-epi-effacement; the conclusion uses exactly
   lem-sc-presheaf-free-ext-local-killing-witness. Proof steps describe the image
   subsheaf, generator-pair construction, sheafified lift and Ext associativity used
   in Lean. Existing proof_origin records agree; no node edits are needed.

Changes made by the second reading: restored `exact` in the final proof, corrected
U4 to H2 in the historical landing attribution, corrected the witness proof
docstring (it described a Yoneda construction not performed by this Lean proof),
and added this independent review. Only the proof docstring differs from the repository. Both public theorems are
verified as already proved (2 of 2); this review closes zero holes and adds zero holes.
