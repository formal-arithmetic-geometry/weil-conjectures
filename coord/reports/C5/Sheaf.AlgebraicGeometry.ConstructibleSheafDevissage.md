## What changed

Proved `AlgebraicGeometry.Etale.exists_constructible_sheaf_devissage` with its exact
original signature in `Sheaf.AlgebraicGeometry.ConstructibleSheafDevissage`.
Two proved private helpers identify extension through an open/closed factorization
and compare an open in a closed subscheme with the canonical scheme-theoretic image.
The main proof uses Noetherian induction on closed supports, generic constancy,
the sheaf open-closed exact sequence, exact closed pushforward and finite-filtration
closure. Its conversion to actual subobjects uses the already proved private
`CategoryTheory.subobject_filtration_of_closure`, accessed by `import all` from
`Sheaf.CategoryTheory.FiniteFiltrationRefinement`; no helper was copied.
Updated the item's node proof and proof dependencies to this route.
No target, definition, existing signature or public import changed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.exists_constructible_sheaf_devissage`
(node `lem-fin-constructible-devissage`). Added zero holes; split off zero statements.
The item has zero remaining `sorry`s. Both private helpers have complete proof terms.

Validation: the final module compiled cleanly with `lcompile.py` in 3.2 seconds.
The required `deliver3.py --no-push` then passed compilation, the declaration axiom
probe and preflight (review class CODEX because the node route changed).
Static checks confirm the unchanged theorem signature, zero source holes,
line lengths and existing DAG dependencies. Earlier transient compile-server
response failures were resolved by retrying; no Lean error remained.

## No longer needed

Removed proof imports:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `lem-kun-dimension-finite-type` is unnecessary because Noetherian induction suffices.
- `Sheaf.AlgebraicGeometry.LisseOpenDimensionDrop`:
  `fin2-lem-lisse-dense-open` is unnecessary; proved generic constancy supplies a dense
  lisse open, and strict decrease is checked directly on closed supports.
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`:
  `lem-cbc-open-closed-recollement` is unnecessary; this is entirely sheaf-level,
  using exact finite direct image directly.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`:
  replaced by `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange`,
  whose identity-source specialization proves exactly the needed closure comparison.
  The mathematical extension-by-zero base-change dependency remains.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: redundant direct import;
  its definitions and composition API are provided by the retained imports.

No statement module is withdrawn; these removals describe this item's proof only.
The unit record has no realized statement or steps, and its compact-support
base-change route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan needlessly required finite-dimensional induction and cited the
recollement theorem for exactness without an exactness clause in its actual Lean
statement. The existing generic-constancy theorem and the exact finite-pushforward
instance avoid both issues. The canonical closure convention needs a real
comparison: it is proved here using the kernel lift, base change, vanishing and
joint conservativity, without equating different closed subschemes by their
underlying sets.

The existing proved generic finite-filtration API is used as a tool from
`lem-pc-s3-finite-filtration-refinement`; the unit has no specialized substitute.
The direct helper used is private and therefore imported with `import all`.
No maintainer `tool_uses` approvals were added or modified.

Searches: leanfinder returned sheaf finite-type and etale-site results but no
filtration theorem; loogle had no match for `ObjectProperty.filtrationClosure`;
the search service grep returned no match. Local `rg` found the proved
finite-filtration closure and subobject conversion, generic constancy, exact
closed direct image, and the required base-change and scheme-image interfaces.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
