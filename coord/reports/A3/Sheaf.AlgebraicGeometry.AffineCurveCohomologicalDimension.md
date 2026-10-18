## What changed

Completed `AlgebraicGeometry.affineCurve_constantZMod_cohomology` in
`Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension`. Every existing declaration,
binder and public import is unchanged; the canonical constant-section map is unchanged.

Higher vanishing is the affine alternative of the already proved
`torsionEtaleCohomologicalDimensionLE_of_dim_le_one`, applied to the torsion constant sheaf.
This uses the source theorem of unit `sk-prop-cd-affine`, as required by `sk-thm-vanishing`.
For degree zero, terminal-object constant sections give the global-sections adjunction
unit as an isomorphism. `rightDerivedSingleUnit_zero` proves that homology of the canonical
derived single-unit is an isomorphism. Combining these actual maps proves invertibility
of the map in the statement, rather than merely existence of an additive equivalence.

Added private proof imports
`Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension` and
`Sheaf.CategoryTheory.RightDerivedSingleZeroUnit`. The DAG proof and proof dependencies
now describe this route. The latter is a proved generic homological-algebra tool; the
former supplies exactly the curve bound already required by the unit. They are proposed
as generic tool uses for the independent reader; no maintainer approval field was added.

Validation: the final module compiles through `lcompile.py` without errors or warnings.
Both added imports pass `tools/import_direction.py may`. Edge cases: the general curve
bound includes the empty scheme, disconnected curves, and zero-dimensional curves; only
the degree-zero clause invokes connectedness. The argument also includes `d = 1`.
No statement or definition repair, new declaration, or consumer adaptation is needed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.affineCurve_constantZMod_cohomology`
(node `sbc-thm-cohomological-dimension-of-an-affine-curve`).

Actual holes in the delivered module: 0. Holes added: 0. Split-offs: 0.
The proof uses existing library declarations; their remaining transitive obligations
stay with their existing nodes. This is a proof of the assigned theorem from those
statements, with no decomposition or moved hole.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Mathlib.CategoryTheory.Abelian.RightDerived`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`

The following old proof dependencies are no longer direct requirements of this item:

- `thm-sc-affine-cohomology`: the larger connected dimension-one Kummer computation is
  unnecessary; the existing all-torsion affine-curve bound gives precisely the needed
  vanishing and keeps the `sk-prop-cd-affine` unit route.
- `thm-sc-affine-torsion-cd` and `lem-sf-separably-closed-torsion-cd`: the arbitrary-curve
  bound already covers every curve in the statement, so a general-dimensional affine
  induction and a field bound are unnecessary.
- `def-weil-pbc-etale-site` and `def-weil-pbc-etale-cohomology`: remain statement-level
  infrastructure, but the old separate empty-scheme calculation is unnecessary.
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero` and
  `lem-weil-pbc-bounded-below-injectives-kinjective`: their homological work is encapsulated
  by the existing proved canonical single-unit comparison; no new resolution calculation
  is needed here.

Removed obsolete top-level tool approvals for `thm-sc-affine-torsion-cd`,
`lem-sf-separably-closed-torsion-cd`,
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`, and
`lem-weil-pbc-bounded-below-injectives-kinjective`. The existing approvals for Grothendieck
abelian sheaves and enough injectives remain, since those instances are used by the
canonical comparison.

The source module `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension`
remains needed for `Scheme.isTorsion_constantZMod`, even though the full Kummer calculation
in the same module is unnecessary. Every retained private import supplies a declaration
explicitly used by the proof. These are pruning claims for this item's route; shared
modules can still be needed by other parents.

## Where the brief, the DAG or earlier work was wrong

The original plan expands both a general affine-dimension bound and the degree-zero
injective-resolution comparison, although the library already provides the needed
curve bound and a proved normalization theorem for the exact canonical derived unit.
Using those existing statements gives a shorter argument.

The current blueprint update still writes an unconditional H0 identification, which
fails for the empty scheme and disconnected schemes. The existing corrected Lean
statement and connected conditional are retained exactly. Its higher-vanishing unit
route is unchanged. No target statement or definition was modified.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
