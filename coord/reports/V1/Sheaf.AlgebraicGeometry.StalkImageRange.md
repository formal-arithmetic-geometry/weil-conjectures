## What changed

Proved `AlgebraicGeometry.Scheme.stalk_image_inclusion_range` in
`Sheaf.AlgebraicGeometry.StalkImageRange`, keeping its signature unchanged.
Use the image clause of `RingedSpace.module_stalk_exact`, then transport from the
abelian image to the categorical image through `Abelian.imageIsoImage`. The mapped
isomorphism is surjective, so precomposing the inclusion with it preserves its range.
The node proof now records these three steps; its dependency and source stay unchanged.
The proof-only imports `Sheaf.Algebra.Homology.ModuleStalkExact` and
`Mathlib.CategoryTheory.Abelian.Images` are private; statement-facing imports remain public.
The import visibility change is recorded in
`coord/changes/stalk_image_range_imports.md`.
The repair replaces the final rewrite of the exactness equality with an explicit
two-step `calc`: image-comparison range transport, then the exactness range equality.
Local compilation succeeds without warnings; the delivery dry run also runs the axiom probe.
The delivery tool compiles locally, checks axioms, and constructs a fresh commit
on current `origin/sheaf-dag`; the global build verifies the landing.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.stalk_image_inclusion_range`
(node `lem-weil-pbc-ideal-multiplication-stalk-range-image`).
No holes added or split off. No `sorry` remains in the delivered Lean module.
The proof uses the existing `RingedSpace.module_stalk_exact`; its module already
contains a complete proof in this checkout. This is a proof, not a decomposition.

## No longer needed

The two proof-only public imports were changed to private imports. A consumer module
still resolves the theorem and `image.ι`; proof implementation details are no longer
re-exported.
No planned dependency node or Sheaf module was pruned: the proof still uses
`lem-weil-pbc-module-stalk-exact` / `Sheaf.Algebra.Homology.ModuleStalkExact`.
The item's node does not realize a unit statement or step; no unit route changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original one-step proof plan did not spell out
that its exactness theorem uses `Abelian.image.ι`, whereas this theorem uses
`Limits.image.ι`. The canonical comparison isomorphism supplies the missing glue.
Searches with leanfinder, loogle, and grep identified the Mathlib comparison theorem;
local searches found the same comparison used elsewhere in the library.

The returned delivery passed mathematical review but failed during landing because
the landing process tried to read an absent
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapScalarCompatibility` source file.
That module is neither an import nor a proof dependency of this item. No replacement
module or theorem is introduced. This repair uses the prescribed delivery tool, which rebases on the current server
branch, and changes the Lean proof as described above.
The prior second reading is removed so that the repaired delivery gets a fresh reading.


## Second reading by V1

1. **Visible interface — PASS.** Diffed the sole delivered module against the
   repository. The existing theorem signature and docstring are byte for byte
   unchanged. There are no definition changes or added hypotheses. The only
   interface edit is the recorded conversion of two proof-only public imports
   to private imports in `coord/changes/stalk_image_range_imports.md`.
2. **Proof and axioms — PASS.** Compiled the module with `lcompile.py`, without
   errors or warnings. A scratch copy with `#print axioms` confirms that both
   `AlgebraicGeometry.Scheme.stalk_image_inclusion_range` and its dependency
   `AlgebraicGeometry.RingedSpace.module_stalk_exact` use exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Scanned the delivered module: no `sorry`,
   axiom, unsafe/opaque declaration, implementation override, or kernel bypass.
   The mapped comparison is an isomorphism, so its underlying map is surjective;
   the composition-range rewrite and the final exactness equality have the
   correct direction.
3. **Split statements — PASS (none).** No new declaration, node, or hole is added.
   Checked the argument for zero morphisms and zero modules: the isomorphism
   transport preserves range in these cases too. There is no arbitrary witness
   choice or postponed data construction.
4. **Route and pruning — PASS.** Read the exactness theorem and the existing
   consumer, searched local Lean for image-comparison/stalk-range results, and
   independently searched Mathlib for `range_comp_of_range_eq_top` through
   `msearch.py`. The existing exactness image clause plus Mathlib image comparison
   supplies the direct reduction; no extra sheaf lemma is needed. Every explicit
   import supplies statement names or proof lemmas. No old `proof_deps` node is
   unused: `lem-weil-pbc-module-stalk-exact` remains the sole proof dependency.
   Read `dag/units/sk-thm-p1.json`: this node is not a realized unit statement or
   step, and the unit route is unchanged. Compiled the original
   `Sheaf.AlgebraicGeometry.IdealModuleMultiplicationStalkRange` against a scratch
   build of the delivered module; it succeeds unchanged without warnings.
5. **DAG agreement — PASS.** Diffed the delivered node against the repository:
   only its proof steps changed. The three steps exactly describe extraction of
   the image-range clause, functorial image comparison, and surjective range
   transport. `proof_deps` and `proof_origin` are unchanged and appropriate.
   There are no new nodes requiring field or source checks.

Second-reading changes: retained the Lean proof and node unchanged. Corrected
this report's claim that the prescribed delivery explicitly enables server
compilation; it uses the default local checks and subsequent global-build
verification. Added this independent reading and its axiom/downstream evidence.
Holes closed: `AlgebraicGeometry.Scheme.stalk_image_inclusion_range` (one).
Holes added: none. Split off: none. Pruned nodes/modules: none.
