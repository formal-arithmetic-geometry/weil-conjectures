## What changed

Implemented `forgetInvariantsExist`, `forgetRestrictionExist`, and
`unitResidualIsoExist` in `Sheaf.CategoryTheory.RelativeInvariantForgetting`.
The first uses the scalar invariant adjunction and the actual fixed-section images;
the other two use identity maps. Their uniqueness proofs retain the required
inclusion and identity normalizations.

Implemented `forgetDerivedExist` by constructing the two derived units for the
common ordinary composite and applying uniqueness of right derived functors.
A new proof-only import, `RelativeForgettingKInjectives`, isolates the one missing
structural input. The generic derivability argument is a proved private helper,
adapted from the library's `derivedCoefficientComparison` argument in
`DiagramRingRestrictionPushforward`. The proof-only import
`RingedToposDerivedPushforwardComposition` supplies the proved generic K-injective
derivability criterion `CategoryTheory.derives`. Existing definitions and public imports are
retained. The packet changes no other existing Lean module.

Remote `lcompile.py` accepted the new structural module and the item module.
The item compiled in 48.8 seconds before the final tactic-style cleanup. The
delivery preflight checks the submitted versions, including the remaining named holes.

## Proved and sorry left

Closed original holes:

- `CategoryTheory.RelativeCyclic.forgetInvariantsExist`: proved from the existing
  normalized invariant specifications.
- `CategoryTheory.RelativeCyclic.forgetRestrictionExist`: proved.
- `CategoryTheory.RelativeCyclic.unitResidualIsoExist`: proved.
- `CategoryTheory.RelativeCyclic.forgetDerivedExist`: decomposed to the structural
  K-injective preservation theorem below, with the universal-property construction,
  normalization and uniqueness fully proved.

Original holes retained, both attached to `def-sfb-relative-invariant-forgetting`:

- `CategoryTheory.RelativeCyclic.forgetBeta`.
- `CategoryTheory.RelativeCyclic.forgetDerivedShift`.

Added one hole:

- `CategoryTheory.RelativeCyclic.forgetResidual_preservesKInjectiveComplexes`, in
  `Sheaf.CategoryTheory.RelativeForgettingKInjectives`, attached to
  `lem-sfb-relative-forgetting-kinjectives`.

Thus four of the six original holes are closed, one new hole is added, and three
holes remain across the packet. The derived comparison is a decomposition, not
an unconditional proof of its structural input. No hole is inside a definition
or a private helper.

The new structural statement is strictly part of the argument: it concerns
restriction of K-injective complexes, with no invariant functor, comparison
isomorphism, computation-unit equation, or uniqueness conclusion. Its proof plan
constructs exact induction and transposes null homotopies. Edge cases checked:
trivial G gives identity forgetting, trivial J gives ordinary action forgetting,
zero coefficients give the zero category, and no degree bound is imposed.

## No longer needed

None. No original import or node is withdrawn. `RelativeCyclicTotal` remains a
public import because the public cyclic comparison definitions use it. The
unit route and all declarations of the adopted source tree are retained.

## Where the brief, the DAG or earlier work was wrong

The definition node had an empty proof array despite six named proof holes. Its
sandbox copy now records the implemented route and the two remaining original
proofs separately.

`ProductActionExactForgetting.exists_datum` takes a hypothesis that the retained
group J is profinite or topologically isomorphic to the discrete integers.
`forgetDerivedExist` quantifies over arbitrary topological J. That declaration
therefore cannot directly supply the exact-induction input here. The new node
states precisely the needed K-injective preservation at the original generality;
its construction uses profiniteness of G and does not assume compactness of J.
No existing statement is weakened or repaired.

The current blueprint's direct-images paragraph (3) now refers to the open-image
coefficient theorem and does not spell out this older agent-extracted relative
calculation. The existing node's source and wanted-reference qualification are
retained; the new proof plan explicitly identifies the agent-formulated induction
argument rather than claiming the current paragraph contains it verbatim.

## New nodes

`lem-sfb-relative-forgetting-kinjectives` records preservation of K-injective
complexes by restriction along j to (1,j), for profinite G and arbitrary topological
J. Its new module has one named theorem with source and a complete proof plan.
The existing fixed-point specifications and free-module flatness are reused;
no new data definition or unspecified witness is introduced.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
