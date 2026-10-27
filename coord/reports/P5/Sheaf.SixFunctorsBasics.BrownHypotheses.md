## What changed

Added the proved theorem
`CategoryTheory.BrownHypothesesFor.finite_nonzero_hom_of_degreewise_disjoint`
in the assigned module. It gives a finite exceptional set of nonzero Hom groups
for any sequence of cochain complexes with disjoint degree supports whose derived
images lie in the actual localizing closure. The complexes may have several
nonzero terms and need not be bounded or constructible.

Reproved `CategoryTheory.BrownHypothesesFor.eventually_hom_single_shift_eq_zero`
by applying this theorem to the complexes F_n[0][n], checking their supports and
transporting zero maps along the canonical derived shift comparison. The new
proof factors out the full-subcategory product/coproduct construction rather
than repeating it in this specialization. No import changes. All existing
statements, visibility, definitions, public imports and instances are preserved.
The finite-field assembly and the original arbitrary-field theorem are untouched.

Updated the varying-heart node and the main item's proof route and added a node
for the new proved theorem. Change record:
`coord/changes/P5-brown-disjoint-complex-support.md`.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
The sole direct sorry remains `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`. Its statement remains marked STATEMENT-DISPUTED.
The new disjoint-complex finite-support theorem and the revised varying-heart
proof are complete, with no use of that disputed theorem. This is a proved part
of the compactness obstruction, not a proof or holed decomposition of the
unsupported arbitrary-field assertion.

A source-parser comparison checks all 20 original declaration signatures and all
non-theorem bodies unchanged. Imports are identical; the only original proof
changed is eventually_hom_single_shift_eq_zero. The final prescribed single-file compile
passed in 42.4 seconds, exit 0, with no warnings. The delivery tool runs the
required declaration-axiom probe and packet checks.
No local Lake build or edits to the shared library were made. The first compile
accepted the new generalized theorem but found that destructuring hB removed
it before the specialization called it; the proof now destructures a copy.
The next compile reached the final arithmetic check; an explicit type
`n ≤ S.sup id` now reduces the identity function before omega.

## No longer needed

The varying-heart proof no longer constructs or restricts the product and
coproduct universal properties itself. Its node now depends on the generalized
finite-support theorem and the localizing-closure definition. Its old direct
dependency on `lem-sfb-brown-product-coproduct-obstruction` becomes an indirect
dependency through the new theorem, so that node remains necessary.
No module, import or declaration is withdrawn and no module is claimed pruned
from the target closure. The structural, smallness and finite-field compactness
inputs remain necessary for the existing supported assembly.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the sole original hole asserts compactness for separated
finite-type schemes over arbitrary positive-characteristic fields, whereas the
available finite and rational compactness dependencies require FiniteFieldDatum
and the integral dependency needs an explicit Ext bound. Finite type over an
arbitrary field supplies neither missing hypothesis. Both current callers
(LocalizingExceptionalAdjoint and ExceptionalInverseImageExistence) also make
arbitrary-field assertions, so restricting this theorem to the already proved
finite-field case would not repair them. The original diagnostic using a field
of infinite transcendence degree and Kummer cup symbols is retained; it is not
claimed as a formal field-cohomology counterexample.

The plan's missing field hypothesis cannot be manufactured by regrouping the
coefficient alternatives or by choosing a small skeleton. No false compactness
lemma or renamed hole is introduced. The coefficient mismatch mentioned in old
reports was already fixed by the human; the current obstruction is the field
hypothesis, not the six-case list.

The checked obstruction previously applied to single-term shifted heart objects.
The same proof only needs disjoint degree supports. The new theorem formalizes
this broader, strictly categorical step and is actually used by the existing
Ext diagnostic. Edge cases include zero complexes, finitely many nonzero
complexes, arbitrary widths of the supports, and a zero source. Fullness and
proof irrelevance identify the full-subcategory Hom types with the ambient ones.
No witness data is chosen from an unproved existence theorem. The unit route and
all target signatures remain unchanged.

## New nodes

`lem-sfb-brown-disjoint-complex-hom-support` records the new theorem, with the
actual Lean signature. It follows the finite-support argument in source module
NotPreservesCoproducts, using the proved degreewise product-coproduct comparison
in DegreewiseLimits and exact countable products in Products and
ProperLowerStarCoproducts. The proof first obtains the product and coproduct,
puts their common vertex in L by minimality, restricts the two universal
properties by fullness, and applies the existing Brown finite-support theorem.

Searches of the whole blueprint for 'compact disjoint' and 'disjoint complexes'
found no match. LeanSearch returned exact-countable-product and homological
support infrastructure, LeanFinder returned t-structure and single-complex
support lemmas, and Mathlib grep found no exact theorem. Direct project search
found the existing comparison infrastructure and the narrower varying-heart
bound, both reused. No new hole or axiom is attached to this node.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
