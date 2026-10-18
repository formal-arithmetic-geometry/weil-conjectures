## What changed

Proved `SheafOfModules.changeOfRings_isKFlat_of_flat_terms` without changing its signature.
Restriction of scalars is proved exact and conservative using the underlying abelian-sheaf
functors. A natural tensor cancellation identifies the two bicomplexes; restriction preserves
the totalization coproducts, so the comparison transports K-flatness. The same comparison
transports the exact tensor functor for each term, proving the flatness conclusion.

Added `Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellation`, whose one public theorem
constructs the comparison from Mathlib's sectionwise `cancelBaseChange`, restriction commuting
with sheafification, and monoidal localization. The private constructions have proved APIs;
none chooses data from an undetermined existence theorem. Updated the parent DAG proof and
its dependencies to match this construction. Both delivered files compile individually
through `lcompile.py`, with no warnings or remaining holes in these files.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.changeOfRings_isKFlat_of_flat_terms`
(`lem-pur-kflat-change-of-rings`).

Also proved the new theorem
`SheafOfModules.exists_changeOfRings_tensorCancellation`
(`lem-pur-change-of-rings-tensor-cancellation`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in either delivered module.
The existing `changeOfRingsComplex_shape` and `changeOfRingsComplex_comp` dependencies are
unchanged; this delivery proves the assigned statement from the library's declarations.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`.

The proof does not use `lem-pc-sites-module-sheafification-bilinear-extension`, or its existence
and uniqueness modules. Monoidal sheafification inverts the tensor of the presheaf unit,
which provides the required comparison directly. Its old top-level `tool_uses` approval was
removed from the parent node. The constant-ring restriction functor in the last removed
import is unrelated to the varying-ring sheaf restriction used here. The category abbreviation
in `RingedSiteModules` and the independent-universe auxiliary interfaces are also unnecessary.
The underlying notions of module sheaves, scalar restriction, sheafification, tensor products,
and total tensor complexes remain in use through their Mathlib and source declarations.

The unit `sk-def-sf-operations` has no realized statement or proof steps affected by this
pruning. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing balanced tensor contraction/comparison theorems are specialized to topological
spaces, so they cannot be applied directly on this arbitrary site. The new theorem gives the
same balanced equivalence at the site's separate object and morphism universes.

The parent plan's bilinear extension is mathematically valid but unnecessary: the monoidal
localization API supplies the sheafification step. No existing statement or definition was
changed, and no consumer adaptation or change record is required.

## New nodes

`lem-pur-change-of-rings-tensor-cancellation` records the natural isomorphism
`U(M ⊗_S E(N)) ≅ U(M) ⊗_R N`, used both termwise and on bicomplexes. It is strictly an
object-level comparison, with no K-flatness or exactness hypotheses or conclusions. Its
sectionwise inverse formulas cover zero rings and zero modules. The theorem is fully proved;
there is no new obligation to hand on.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
