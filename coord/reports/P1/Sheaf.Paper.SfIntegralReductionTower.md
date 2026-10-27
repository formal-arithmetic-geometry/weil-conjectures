## What changed

Filled all three proof bodies in `Sheaf.Paper.SfIntegralReductionTower`, preserving
all existing signatures, definitions, attributes, and public imports.

The ordinary transition is obtained by evaluating the published natural transition
on complexes at degree zero of the functorial complex with constant terms and zero
differentials. Tensor generation and the sheafification universal property prove
uniqueness. The derived transition is the universal lift through the restricted
scalar-reduction counit. Exact derived restriction is a right adjoint, so it
preserves that right Kan extension. K-flat resolutions prove uniqueness from the
specified normalization. The normalized adjunction units commute with adjacent
transitions on pure tensors; localization and `NatTrans.ofOpSequence` give the
full cone naturality.

Added only private, proved helpers and proof imports for the existing unrestricted
transition, K-flat resolutions, and adjunction whiskering. Derived lifts are
already publicly available through the existing derived-change-of-rings interface.
The right-adjoint Kan-extension helper follows the proved private `kanRightAdjoint`
argument in `Sheaf.CategoryTheory.ExactRestrictionAugmentedCompletion`; importing
that larger completion interface is unnecessary.

## Proved and sorry left

Closed 3 of 3 holes:

- `WeilConjectures.sfReductionTransition_existsUnique`.
- `WeilConjectures.sfDerivedReductionTransition_existsUnique`.
- `WeilConjectures.sfIntegralReductionUnit_naturality`.

Added zero holes; split off zero statements. No `sorry` remains in the delivered
module. All helpers are private and proved.

## No longer needed

No original public import was removed and no module was withdrawn. No unit route
was bypassed. The derived transition uses Kan-extension lifting rather than a new
explicit calculus of resolution roofs; its uniqueness and unit comparison use the
published K-flat resolution and normalized adjunction interfaces. No new
resolution-independence lemma or dependency on the larger augmented-completion
interface is needed. Existing well-definedness modules remain used by their
other consumers and are not claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The module docstrings point to `def-weil-integral-reduction-tower`, whose current
Lean attachment names the other canonical integral tower interface. There was
no node with `lean.module = Sheaf.Paper.SfIntegralReductionTower`. The existing
statement and construction are retained; this delivery proves the corresponding
Sf interface directly and records its proof route on that same definition node.

The source-library boundary is respected: no adopted source file is changed.

The retained sandbox attempt did not compile: the generic site-smallness instance
left its coefficient universe unresolved, the resolution theorem's universe
arguments were in the wrong order, and simplification of the final sequence
identity omitted the constant object's reduction. These are repaired using the
concrete small-site instance already used by `SfDerivedCompleteLegacyComparison`,
explicit resolution universes, and `Functor.const_obj_obj`. Large existence
witnesses and the completed coefficient limit are locally irreducible to control
elaboration. Existing public signatures and definitions are unchanged.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
