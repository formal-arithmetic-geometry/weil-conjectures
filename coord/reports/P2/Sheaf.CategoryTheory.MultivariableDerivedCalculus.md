## What changed

Completed the retained proofs in `lean/Sheaf/CategoryTheory/MultivariableDerivedCalculus.lean`.
No existing declaration signature, visibility, import, or docstring changed. The change record
`coord/changes/P2-multivariable-private-product-helpers.md` documents section-local helper
binders flagged by the static interface check and lists the downstream consumers; none requires
adaptation.

`CategoryTheory.multivariableDerivedCalculus` follows the seven-step DAG plan. Private, fully
proved helpers identify the triple category of a product square with the product of the
coordinate triple categories and prove that finite products of connected categories are
connected. This establishes product Guitart exactness and hence product left derivability. A
finite-set induction factors an arbitrary tuple of weak equivalences into single-coordinate
arrows, proving `Derives`. The existing unary calculus in
`WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives` then
supplies existence and detection. The right Kan extension universal property is converted to the
stated bijections, in both directions. Essential surjectivity of the resolving inclusion
followed by localization proves equality detection on resolving tuples.

`CategoryTheory.multivariableDerivedComparisons` uses Mathlib's component equation,
extensionality, identity, composition and natural-isomorphism API for left derived natural
transformations. Uniqueness and counit cancellation follow from `Functor.leftDerived_ext`.

Validation: the fresh single-file compile through `lcompile.py` completed cleanly in 4.1
seconds, without warnings on the resumed session. Both theorem signatures and the complete
import list were compared with the current repository and are identical. All Lean lines fit the
100-character limit.

Earlier sandbox work repaired three compiler errors: the extra function-extensionality step
after `ext` had already introduced the coordinate; the dependent conditional before applying
weak-equivalence membership for `eqToHom`; and the failing simplification of a transported
`eqToHom`, replaced by an explicit heterogeneous-equality argument. The retained proof uses
full-and-faithful preimage recovery when passing an arrow to the finite-set induction, retaining
the existing hypotheses and signature without an unused-section-variable warning. No new
assumptions or intermediate holes.

## Proved and sorry left

Closed both original holes: `CategoryTheory.multivariableDerivedCalculus` and
`CategoryTheory.multivariableDerivedComparisons`, both attached to
`lem-sfb-multivariable-derived-calculus`. Two of two holes proved; zero split off; zero holes
added; zero `sorry` left in the delivered module.

## No longer needed

None. No imports removed. All four declared dependencies remain used:
`lem-sfb-product-localization` (Mathlib's `Functor.IsLocalization.pi`),
`def-sfb-left-derivability-structure` (the structure and Guitart-exactness criterion),
`lem-sfb-unary-left-derived-calculus` (the existing project supplement), and
`lem-trf-localization-essentially-surjective` (through
`LocalizerMorphism.essSurj_of_hasLeftResolutions`). No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found in the brief or DAG. The resumed session retained the
completed proof and report from earlier sandbox work, checked the node and all four dependency
declarations against the current sources, and recompiled successfully. No statements,
definitions, consumers, or node records needed changes. No new nodes. The static interface check
flags the section-local helper binders;
`coord/changes/P2-multivariable-private-product-helpers.md` records their scope and all
downstream consumers. No consumer adaptation is required.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
