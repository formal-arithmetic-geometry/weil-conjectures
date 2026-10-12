## What changed

Proved `AlgebraicGeometry.RingedSpace.finiteType_image_extension` in
`lean/Sheaf/AlgebraicGeometry/ModuleFiniteTypeImageExtension.lean`, preserving its signature,
visibility, and existing docstring. Added proved private helpers for epimorphic images,
simultaneous lifting of finite families, slice-site sections and restriction of generators,
and the coproduct generation argument for extensions. Added the proof-only import
`Mathlib.Data.Finite.Sum` for finiteness of the combined index type. All original public
imports remain because the statement uses their module, generator, image, and short-exact APIs.

Updated the existing node's proof, proof dependencies, and proof origin to follow the Lean.
The extension argument uses local lifting and the categorical cokernel universal property.
The blueprint unit's realized statements and steps are unchanged.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.RingedSpace.finiteType_image_extension`
(node `lem-weil-pbc-module-finite-type-image-extension`). All three clauses are proved:
epimorphic images, images of morphisms, and short exact extensions.

No `sorry` remains in the item; no holes or new theorem modules were added.
All private helpers are proved, and both private data constructions have explicit bodies.
Single-file compilation succeeded without warnings. A separate single-file axiom check
printed exactly `[propext, Classical.choice, Quot.sound]` for the main theorem, with no
`sorryAx`. The axiom-check copy is in `scratch/Axioms.lean` and is not a delivery module.

The delivery dry run now prints OK: the module compiles and passes preflight except
for the second reading, which the second reader writes. The earlier missing
`refuse_missing` tool failure no longer occurs. No script was changed, no check was
bypassed, and nothing was pushed.

Edge cases are handled without extra assumptions: an empty family of quotient generators
uses the original open intersected with the empty intersection, and on an empty space the
point-indexed local generating cover is empty and satisfies the covering condition.

## No longer needed

The direct dependency `lem-weil-pbc-abelian-exact-iff-epi-kernel-lift` is removed from this
node's proof dependencies: `Abelian.factorThruImage` already has the required epi instance.
This is a Mathlib leaf, so no separate project module import is removed by this pruning.
No original imports were removed. The local lifting module is still used; the already
publicly imported `Sheaf.Paper.DerivedHomMayerVietoris` supplies the shared exactness and
restriction instances, now recorded explicitly as `lem-sc-derived-hom-mayer-vietoris`.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan's image-factorization step is longer than
needed with Mathlib's existing image API. The final sectionwise generation check can be
replaced by the categorical cokernel argument once quotient generators lift locally.

The cited literature file is absent in this clone; Stacks Tag 01B7 was read at
https://stacks.math.columbia.edu/tag/01B7 and agrees with the node and existing docstring.
No interfaces, definitions used by target statements, or other held modules were changed.

## Second reading by K4

1. PASS: compared the sole delivered module with the repository using `diff` and checked
   the existing theorem signature byte for byte. Its signature, visibility, and docstring
   are unchanged. Only proved private helpers, declaration-local elaboration options,
   a proof-only import, and the proof body were added. No change record is needed.
2. PASS: independently compiled the delivered module without errors or warnings, and
   compiled an exact scratch copy with `#print axioms` for
   `AlgebraicGeometry.RingedSpace.finiteType_image_extension`. It reports only `propext`,
   `Classical.choice`, and `Quot.sound`. Searched the delivered Lean for forbidden
   declarations and `sorry`; none occur. Read both private data constructions: sections
   are explicitly assembled by restriction, and generators are transported using proved
   functorial maps. Choices of neighborhoods and lifts occur inside proved theorems;
   no data is obtained from an unproved existence theorem.
3. PASS: no statements are split off, no new holes or nodes are introduced. Read every
   helper: finite intersections give simultaneous lifts, evaluation at the terminal
   slice object determines sections, restriction preserves generators, and the coproduct
   generation argument follows from the cokernel descent property. Empty generator
   families retain the original neighborhood; the point-indexed cover handles an empty
   space. Independent Mathlib grep through `msearch.py` and project `rg` found no shorter
   general finite-type extension theorem; the existing Mathlib `ofEpi` and `map` APIs
   are already used. The similar project isomorphism helper is only a special case.
4. PASS: the proof starts with the existing Mathlib generator and image APIs, uses the
   proved local-lifting declaration for the finite quotient family, and completes the
   extension argument categorically. Each import supplies statement types or proof APIs;
   the added finite-sum import is proof-only. The report names the only old dependency
   removed, `lem-weil-pbc-abelian-exact-iff-epi-kernel-lift`. Checked `sk-thm-p1.json`:
   neither that leaf nor this item realizes a unit statement or step; the unit's recorded
   route is preserved. The referenced blueprint `_section.md` is absent in this clone,
   so the unit check uses the complete statement, steps, and `realized` record in JSON.
5. PASS: compared the node JSON with the repository. Only `proof`, `proof_deps`, and
   `proof_origin` differ. The union of the steps' `uses` equals `proof_deps` exactly.
   The six recorded steps follow the implemented proof, including restriction instances
   from `DerivedHomMayerVietoris`, local lifts, coproduct generation, and the covering.

Second reading changed only this report to record the independent checks and the missing
blueprint source-file limitation. No Lean or node repair was needed. Closed holes: one,
`AlgebraicGeometry.RingedSpace.finiteType_image_extension`; added holes: zero.
