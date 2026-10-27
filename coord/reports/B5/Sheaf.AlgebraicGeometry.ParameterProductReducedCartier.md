## What changed

Proved `AlgebraicGeometry.parameter_product_reduced_cartier` with its original
signature. Added two proved private helpers in the item module: finite products
of pairwise nondividing primes generate the intersection of their principal
ideals, and radical principal germ ideals imply reducedness of the associated
closed subscheme. No existing shared module or interface was changed.

The proof uses the full-system case of
`RingTheory.parameter_product_ideal_properties`, then restricts its prime and
incomparability conclusions to the injected nonunit positions. A finite-set
induction supplies the selected-product intersection, including the empty
product. Unit factors do not affect the generated ideal. The existing
closed-immersion stalk-kernel API proves reducedness directly; the stated
stalk Cartier criterion proves invertibility, and the stated complement
theorem proves density. Updated the item's DAG proof to match this route.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.parameter_product_reduced_cartier`.
Added zero holes and zero split-off statements. No `sorry` remains in the
item module. The required `lcompile.py` check passed in 4.2 seconds. The proof still depends on the existing stated theorem
`RingTheory.parameter_product_ideal_properties`; its upstream proof is a
separate item. This delivery is a proof from existing declarations, not a
claim that their entire dependency closure is sorry-free.

## No longer needed

Removed private imports `Mathlib.RingTheory.Localization.Ideal`,
`Mathlib.RingTheory.Ideal.Maps`, and `Mathlib.RingTheory.Localization.Basic`.
The item no longer directly needs
`lem-weil-pbc-localization-at-prime-of-quotient`: the proved
`Scheme.Hom.ker_stalkMap` and
`RingHom.ker_isRadical_iff_reduced_of_surjective` supply the required
closed-subscheme reducedness calculation. This does not withdraw that lemma
or any module used elsewhere. No module is withdrawn.

The permutation of selected positions to the front is unnecessary. The
full-system parameter theorem already supplies prime incomparable ideals;
the finite-product induction applies to any injected subfamily. All other
original declared proof dependencies are retained. No unit statement or
unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or repair was found. The DAG's permutation and explicit
quotient-localization reconstruction were longer than the available APIs
require. The proof and dependency list now describe the implemented route.
The original theorem includes empty schemes and zero factors; both remain
covered, with no new hypotheses. No shared definition or statement changed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
