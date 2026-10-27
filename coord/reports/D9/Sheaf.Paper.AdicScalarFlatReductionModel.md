## What changed

Proved `WeilConjectures.AdicScalarFlatReduction.adicScalarFlatReductionModel` in
`Sheaf.Paper.AdicScalarFlatReductionModel`, preserving every existing public declaration,
statement, and definition. All added helpers are private and proved.

The proof assembles the proved arithmetic datum and quotient arithmetic, constructs
constant-coefficient section equivalences at the independent site and coefficient sizes,
and obtains degreewise finite-free retracts from Mathlib. It reuses the proved
`constant_flat` and `model_good` helpers of the scalar-model interface, without using its
unfinished pullback theorem or `modelModules_exact`.

For reductions it composes the normalized ordinary scalar-extension adjunctions and
uses uniqueness of left adjoints. Linearity proves the full balancing formula. Mapping
this natural isomorphism to complexes gives the original differentials and chain-map
naturality. The inverse, quotient transitions, unit formula, and independence follow
from this normalization. The derived square follows from the universal counit's
naturality, retaining the specified `derivedReductionIso`.

Updated the item's DAG proof, proof dependencies, and proof origin to record this route.
Only private proof imports were added or removed. No source-library module was changed.
Local irreducibility annotations prevent repeated unfolding of the scalar maps and model
functor; the few required expansions are explicit. This fixes the initial 60-second
compile timeout without changing any definitions or raising the limit. The complete
proof compiled via `lcompile.py` in 55.7 seconds before removing temporary diagnostics.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.AdicScalarFlatReduction.adicScalarFlatReductionModel`
(node `lem-a1-adic-scalar-flat-reduction-model`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No statements were split off and no new modules were introduced.

## No longer needed

Removed private proof imports:

- `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`: its published theorem has
  coincident site/coefficient sizes. The explicit continuous-function sheafification
  argument proves precisely the section equivalences required here at independent sizes.
- `Sheaf.CategoryTheory.FiniteTypeConstantExact`: retract equations and the map formulas
  follow from functoriality and normalized sheafification/scalar-extension maps.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`:
  normalized ordinary adjunction composition supplies the balancing isomorphism and
  its uniqueness instead.
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`: no direct import is needed;
  the existing proved `model_good` helper retains its mathematical dependency.

The direct DAG dependencies `lem-pur-proetale-finite-constant-sections`,
`lem-weil-pbc-finite-type-constant-exact`, and
`lem-pc-sites-module-sheafification-bilinear-extension` are replaced as explained above.
The arithmetic datum theorem bundles the previous individual finite-quotient and
Noetherian inputs. Definitions already required by the statements remain unchanged.
Removed the corresponding obsolete top-level `tool_uses` approvals for
`lem-pur-proetale-finite-constant-sections`,
`lem-weil-pbc-finite-type-constant-exact`, and
`lem-pc-sites-module-sheafification-bilinear-extension`, preserving the order of
the remaining approvals.

These are item-level dependency removals, not withdrawals of any source declaration
or claims that the corresponding modules are globally unused.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was necessary. The planned finite constant
section theorem does not directly match the independently sized `CommRingCat` sections
in this item; the proof generalizes its standard argument privately. The planned
bilinear-extension construction can be shortened by the existing normalized ordinary
adjunction theorem.

The item already publicly imports its parent scalar-model interface, whose DAG names
this item. The delivery uses only that interface's proved flatness helpers and explicit
constructions; it does not use the unfinished parent pullback theorem. The DAG records
the flatness helpers' actual foundational results rather than adding a cyclic dependency
on the parent's full theorem. All other declarations and the unit's route are retained.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
