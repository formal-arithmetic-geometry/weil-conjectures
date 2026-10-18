## What changed

Proved `AlgebraicGeometry.Scheme.pullback_constantModule_isIso` with its signature
unchanged. The module-sheaf clause uses the component-isomorphism instance for the
existing `upperStarConstantSheafIso`. The complex clause uses the component of
Mathlib's `NatIso.mapHomologicalComplex` applied to the same natural isomorphism;
its hom is definitionally the comparison in the statement. No boundedness, finiteness,
or coefficient hypotheses are added. The proof also covers zero modules, zero
complexes, and empty schemes: both clauses use isomorphisms without nonemptiness.

Updated `lem-kun-pullback-constant` to record this shorter route and removed its three
obsolete top-level `tool_uses` entries. The unit has no realized steps that this route
would bypass. Public imports and all existing declarations and docstrings are unchanged.

Searches: Lean Finder for natural isomorphisms on homological complexes found
`CategoryTheory.NatIso.mapHomologicalComplex`; Loogle for `"mapHomologicalComplex"`
confirmed its signature; the launcher's Mathlib grep found its definition in
`Mathlib/Algebra/Homology/Additive.lean`. Repository search and inspection confirmed
`upperStarConstantSheafIso` and its existing node `lemma-constructible-pullback-constant`.
The pruned module compiled cleanly through `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.pullback_constantModule_isIso`
(node `lem-kun-pullback-constant`). Both conjuncts are fully proved.
No holes remain in the item; no holes or declarations were added; no split-offs.

## No longer needed

Removed these five proof-only imports:

- `Mathlib.CategoryTheory.Sites.Sheafification`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The first and last are available transitively through the existing public construction
import. Their nodes `def-weil-pbc-sheafification`, `def-weil-pbc-direct-image`, and
`def-weil-pbc-inverse-image` are not separate proof obligations on this route: the
existing constant-sheaf isomorphism packages that construction. The statement's
`stmt_deps` are preserved.

The stalk nodes `lemma-openclosed-stalk-upperstar`,
`lem-weil-pbc-constant-sheaf-geometric-stalk`, and
`lemma-weil-pbc-geometric-stalk-conservative` are unnecessary for this proof, as are
their three dedicated proof imports and their obsolete `tool_uses` approvals.
`lemma-constructible-pullback-constant` supplies the whole sheaf clause, while
`def-kun-constant-sheaf` and Mathlib supply the extension to complexes. No module is
withdrawn, and no assertion is made that these modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The DAG's planned stalk argument is valid but unnecessary for the fixed Lean statement:
it already names the hom of an existing natural isomorphism. Its split report said the
existing isomorphism covered only the sheaf clause, but Mathlib's existing
`NatIso.mapHomologicalComplex` extends it to arbitrary unbounded complexes directly.
This is a shorter proof below the unit level, with no statement or definition repair.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
