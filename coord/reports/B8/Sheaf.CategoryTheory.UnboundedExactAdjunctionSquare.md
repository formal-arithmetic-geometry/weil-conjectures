## What changed

Completed both theorems in `Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare` without
changing any existing public statement, definition, instance, or public import.

Constructed the evaluation-at-zero/constant adjunction and proved the tower properties.
Normalized the canonical derived square mate on complexes using the existing derived
counit factorization. Specialization gives the specified constant/evaluation representative
formulas. On K-injective representatives these imply invertibility; naturality transports
invertibility to every derived object. Mathlib's mate identities give the Hom, unit and
counit clauses. The existing `mapDerivedCategory_exactCube` and `exchangeMate_cube`
prove the two square-mate compatibilities. All added helpers are private and proved.

Added private proof imports of `Sheaf.CategoryTheory.DerivedExactCube` and
`Sheaf.CategoryTheory.ExchangeMateCube`. Retained the localization API and existing
source-library tower evaluation theorem. Updated the node's proof route and
proof dependencies and removed obsolete tool-use entries. No new modules or nodes.

Preflight (d) requests the proof-scope visibility record
`coord/changes/B8-unbounded-exact-adjunction-proof-scopes.md`. It documents the new
local section-variable contexts and confirms the sole downstream consumer needs no change.

## Proved and sorry left

Closed both original holes:

- `CategoryTheory.UnboundedExactTower.unboundedExactAdjunctionSquare`.
- `CategoryTheory.UnboundedExactTower.unboundedExactAdjunctionSquare_mates`.

Two holes closed, zero holes added, zero split off, zero `sorry` left in the delivered
module. No statement was weakened and no data definition contains a hole.

## No longer needed

Removed these unused private imports and their dependencies from this proof route:

- `Sheaf.CategoryTheory.DiagramSiteRealization`
  (`lem-weil-pbc-diagram-site-realization`): the existing small-diagram Grothendieck
  instance directly supplies tower resolutions. The node remains a statement dependency
  of the unchanged mathematical description; it is not withdrawn.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
  (`prop-pur-kinjective-resolutions-exist`): the existing source-library Grothendieck
  K-injective resolution instance suffices.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
  (`lem-weil-pbc-kinjective-total-derived`): use the canonical right derived functor
  and its unit already present in the public interface.
- `Sheaf.SixFunctors.ResolvingDerivedAdjunction`
  (`lem-sfb-resolving-derived-adjunction-normalization`): the actual canonical derived
  counit factorization proves normalization directly.

Also removed `lem-weil-pbc-kinjective-hom-derived` from proof dependencies and tool uses:
there is no reconstruction of natural transformations from a Hom bijection into
K-injectives. The existing natural mate is normalized directly, and K-injective
resolutions are used only to transport invertibility. Removed the now-unused private import of
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` as well; the canonical resolution
and quasi-isomorphism APIs used by this proof are already in the public interface.

No source-library declaration or module was removed. No global withdrawal is claimed;
other consumers may still need any of the branches listed above.

## Where the brief, the DAG or earlier work was wrong

The old proof plan rebuilt the adjunction normalization through a separate resolving-class
lemma and a Hom calculation on K-injectives. The library already has the exact canonical
derived adjunction and its counit factorization, and proved localization/mate cube
lemmas. These give a shorter route while retaining the original full statements,
normalizations, universes, and specified comparison maps. No false statement was found.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
