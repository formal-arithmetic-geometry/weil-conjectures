## What changed

Proved `CategoryTheory.moduleSheaf_coproduct_localSupport` with its original signature.
Take the existing coproduct and its coordinate map into the product. Local finite-sum
normal forms prove sectionwise injectivity. A locally finite-support tuple has local
finite-sum lifts; injectivity makes these compatible, and sheaf gluing gives its global lift.
The remaining assertions follow from the coproduct universal property.

Added `Sheaf.AlgebraicGeometry.ModuleSheafCoproductLocalGeneration`, proving the
local finite-sum normal form from the module sheafification adjunction, local
surjectivity of sheafification, sectionwise presheaf coproducts and the site axioms.
This is a separate result of the sheafified-coproduct construction, fully proved here.
The DAG proofs now follow these arguments. No existing statement or definition changed.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.moduleSheaf_coproduct_localSupport`.
Also proved `CategoryTheory.moduleSheaf_coproduct_localGeneration`, including its two
private helpers `covering_refinement` and `colimit_comparison_locally_surjective`.
Holes closed: 1. Holes added: 0. Remaining sorry declarations: none.
No unfinished result was split off.

## No longer needed

Retained the existing public statement imports, including the module-sheafification
interface. Removed the proof import
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`:
its general colimit/forgetful comparison theorem is not needed, since the proof uses
Mathlib's module sheafification adjunction directly. Thus
`lem-weil-pbc-module-sheaves-colimits-forgetful` is unnecessary for this proof;
the existing statement dependency remains a description of the chosen products.
The sectionwise-limits Mathlib leaf, the site axioms, module-sheaf category and
colimit universal property remain used. No other declared proof dependency is pruned.
The earlier sandbox-only duplicate `ModuleSheafCoproductLocalSums` was discarded;
it was never a library module and is not delivered.

## Where the brief, the DAG or earlier work was wrong

The original nine-step construction is mathematically sound, but rebuilding a subsheaf
and its universal property is unnecessary. The chosen coproduct, a proved local normal
form, and sheaf gluing give the same subsheaf as a sectionwise injective map with the
required range. This changes only an auxiliary node below the unit, not the unit route.
Empty covering families are handled by unique sheaf gluing, and the empty coproduct
uses the empty finite sum. No statement dispute or definition repair is needed.

## New nodes

`lem-pur-module-sheaf-coproduct-local-generation` records the fully proved local
finite-sum consequence of Stacks Tag 03DB. It is strictly weaker than the item: it
asserts only the local normal form in the chosen coproduct, not injectivity, the
product-image characterization, or the universal-property conclusion of the item.
It uses Mathlib's sectionwise presheaf colimits and module sheafification, and its
Lean declaration has no sorry. No change record is needed because no existing
signature or definition changed.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
