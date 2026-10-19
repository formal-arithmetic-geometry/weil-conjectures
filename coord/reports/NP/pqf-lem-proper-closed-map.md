## Worker report

Record the exact existing theorem `AlgebraicGeometry.IsProper.isClosedMap` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`, branch `slopmaster2`.
No new module, helper, definition node, or dependency repair is needed. Only the
item's `lean` field changes.

Source: `literature/blueprint/master/blueprint/sec-curve-estimates/sk-thm-br/pqf-lem-proper-closed-map.md`,
statement and sole proof paragraph. This node has no `blueprint_update`.
The existing declaration's docstring reads: “A proper morphism is a closed map.”
and carries `(blueprint: pqf-lem-proper-closed-map)` (with backticks around the id).
Its exact source signature is:

```lean
theorem IsProper.isClosedMap (f : X ⟶ Y) [IsProper f] : IsClosedMap f
```

The surrounding section explicitly binds `universe u` and
`variable {X Y Z : Scheme.{u}}`; the declaration uses only `X` and `Y`.

Hypothesis and conclusion correspondence:

- “Let f : X → S be a morphism of schemes”: `{X Y : Scheme.{u}}` and
  `(f : X ⟶ Y)`. Renaming the target `S` to `Y` changes nothing.
- “proper”: `[IsProper f]`, using Mathlib's scheme-morphism properness.
- “Then f is a closed map”: `IsClosedMap f`, the predicate saying that the
  image of each closed subset under the underlying continuous map is closed.
  This is the full closed-map assertion, including every closed subset.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is recorded as `lean.convention = true`,
  with null declaration/module: it explicitly fixes no independent notion.
  Its properness convention is Mathlib `AlgebraicGeometry.IsProper`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, whose full declaration in the
  context `(f : X ⟶ Y)` is
  `class IsProper : Prop extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f`.
  Its docstring specifies precisely those three conditions. Universally closed
  morphisms are quasi-compact, so this agrees with finite type in the convention.
- The sole proof dependency `lem-weil-pbc-proper-closed-image` has status
  `mathlib`; its recorded match is `AlgebraicGeometry.Scheme.Hom.isClosedMap`
  in `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`, with full signature
  `lemma Scheme.Hom.isClosedMap {X Y : Scheme} (f : X ⟶ Y) [UniversallyClosed f] : IsClosedMap f`.
  The node's `mathlib_match.how` explains the parent instance
  `IsProper.toUniversallyClosed` and the consequent closed range. The existing
  theorem for this item uses `f.isClosedMap` directly. The source proof's pointer
  is thus realized by the same Mathlib closed-map theorem, with properness
  supplying its universally-closed hypothesis.

Edge cases checked: arbitrary schemes in every universe `u`, empty source and
empty target whenever the morphism exists, identity morphisms, and closed
subsets including the empty set and the whole source. There is no nonemptiness,
Noetherian, field, characteristic, or absolute separatedness restriction.
No statement correction or disputed statement is needed.

Searches (all performed before recording the match):

- `msearch.py ... leanfinder "A proper morphism of schemes is a closed map"`:
  eight hits, including `Scheme.Hom.isClosedMap`, `IsProper.toUniversallyClosed`,
  and `IsProper`; identifies the Mathlib ingredients.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, IsClosedMap"`: zero hits.
- `msearch.py ... leansearch "A proper morphism of schemes is a closed map"`:
  eight hits, including the same closed-map theorem and parent instance.
- `msearch.py ... grep "IsProper.*isClosedMap|isClosedMap.*IsProper" AlgebraicGeometry`:
  one hit on the proper-map characterization in `Morphisms/UniversallyClosed.lean`.
- `rg` of `IsProper.isClosedMap`, `pqf-lem-proper-closed-map`, and related
  closed-map expressions in `WeilConjectures/` and `lean/Sheaf/`: the older
  source checkout has uses of the general theorem, but omits the exact wrapper;
  no side-library duplicate found. `dag/lean_names_upstream.json` records the
  exact wrapper under this blueprint id.
- Read both local Mathlib source files `Morphisms/Proper.lean` and
  `Morphisms/UniversallyClosed.lean`, including the definitions and signatures.
- `scompile.py --source WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  the current published source contains the exact wrapper and docstring, in its
  `Basic` section. This resolves the stale local source discrepancy and confirms
  the node's existing slopmaster2 audit attachment.

Validation: the prescribed delivery wrapper checks the imported existing
constant with `#check @AlgebraicGeometry.IsProper.isClosedMap` through scompile.py,
then runs server preflight. No new Lean file is delivered or compiled.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
