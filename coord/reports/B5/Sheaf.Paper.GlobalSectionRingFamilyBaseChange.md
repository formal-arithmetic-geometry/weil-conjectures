## What changed

Filled `CategoryTheory.ringFamilyGlobalExtension_to_family` without changing its
statement or any existing definition. Private helpers construct the sectionwise
tensor presheaf over an arbitrary small category, its extension/restriction
adjunction, and its canonical isomorphism with the existing presheaf pullback.
The tensor-presheaf proof generalizes the proved construction in
`WeilConjectures.CategoryTheory.PresheafChangeOfRingsAdjunction`; no adopted-source
file is changed. The existing sectionwise base-change theorem supplies the
quasi-isomorphisms. Evaluation detects the presheaf quasi-isomorphism and exact
sheafification preserves it. The augmentation equation is checked in degree zero
by the two adjunctions and the augmentation clause of strict functoriality.

Added a proof import from Mathlib for objectwise homology. Updated the node proof
text and provenance to record the concrete tensor-presheaf and augmentation arguments. All helpers are proved,
private, and select no data from an unproved existence assertion.

Validation: the final module compiled through `lcompile.py` in 43.3 seconds,
with the profiling options removed. All original public declarations and the
assigned theorem statement are unchanged.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ringFamilyGlobalExtension_to_family`.
Added zero holes. There are zero `sorry` declarations left in the item module.
The already proved `CategoryTheory.ringFamilyGlobalSectionComparison_quasiIso`
continues to use the existing ring Cech base-change dependencies.

## No longer needed

No planned mathematical dependencies, DAG nodes, or library modules are pruned.
The proof follows the existing node, including exact sheafification and the
sectionwise semilinear scalar-extension comparison. No public imports are removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing tensor-presheaf adjunction
proof in the adopted source is specialized to topological spaces. Its private
construction is generalized locally here to the arbitrary small category in
this item's existing statement. The sectionwise comparison already in the item
is retained and used; the remaining obligation is closed without another split.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
