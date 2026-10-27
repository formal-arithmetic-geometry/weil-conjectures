## What changed

Replaced `exists_field_stage_completion`'s proof hole with a reduction to the rational
localization and common-field portions of its source argument. Its signature, all supplied
ring-stage data, and its original source/proof docstring are unchanged. No existing dependency
or consumer interface was changed.

The integral left functor's DVR-linearity is proved by transporting the known compact-support
linearity through `A.integralLeft` and reflecting the equation through the full-subcategory
inclusion. The given right adjoint is then linear by adjunction. The remaining rational
construction takes these proved linearity hypotheses. The common-field construction takes
that fixed rational family and outputs only closed operations and comparisons. In particular,
neither new theorem is the original simultaneous existence statement under another name.

The consumer proves the full representative-arrow law from the smaller transition equation:
expand the functor on a composite, cancel the source comparison, substitute the transition
equation, and use naturality of the target comparison. It then constructs the original
`CoefficientConstructionFields` and `CoefficientConstructionCommon` records and returns
all five normalization families. All three delivered modules compiled successfully together
through `lcompile.py --all`. The new record definitions have real field-by-field bodies;
none chooses data from an unproved mere-existence theorem.

## Proved and sorry left

Closed the existing hole in
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_field_stage_completion`.
The module now has zero `sorry` occurrences. Its two private glue lemmas, `integral_linear`
and `representativeAction_of_transition`, are proved.

Added two holes, each the entire body of its named public theorem:

- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_rational_stage_localization`
  in `Sheaf.Paper.ExceptionalRationalStageLocalization`, node
  `lem-sf-rational-stage-localization`.
- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_common_stage_descent`
  in `Sheaf.Paper.ExceptionalCommonStageFromRational`, node
  `lem-sf-common-stage-descent-fixed-rational`.

This is a decomposition, not a hole-count improvement: one existing hole closed, two added,
net minus one. The first obligation constructs no closed operation or common-field comparison;
the second constructs no rational operation and fixes all rational operations and scalar maps
as inputs. The full representative-arrow identity is proved in the consumer rather than
restated as a new hole. There are no other holes in this packet and no holes in definitions.

## No longer needed

No module is withdrawn or globally pruned, and no existing import is removed. The four original
planned dependencies (ringed projection cocycle, coefficient scalar units, open tensor
normalization, and normalized exceptional field descent) remain needed by the two substeps.
They have moved from the item's direct proof dependencies into the new nodes' proof plans;
they are not counted as pruning. The generic linear-functor API is a private proof import.
No source-library declaration, signature, attribute, or public import was changed.

## Where the brief, the DAG or earlier work was wrong

No false target or dependency statement was found. The shortest-route search found generic
localization and pair-functor descent tools, but no theorem transporting an arbitrary supplied
finite-Tor adjunction with all the raw object/arrow normalizations required here. The existing
normalized `ExceptionalFieldDescent.exists_field_descent` has prescribed full integral
compact support as input, so it cannot simply be applied to `A.operation` by a type synonym.
The existing complementary-immersion common-stage theorem and the package Qbar descent
route require absolute separatedness, absent from this item's hypotheses.

The original plan's normalization and transport steps remain mathematical work; the packet
makes their rational and common-field boundaries explicit. Edge cases checked at the
statement level are empty schemes, repeated/identity coefficient fields, the identity
morphism, and separated morphisms between schemes without absolute separatedness. Neither
new statement adds absolute separatedness, changes coefficient universes, or weakens a
normalization. The proofs in words explain the tensor units and zero-category cases.

## New nodes

`lem-sf-rational-stage-localization`, in
`dag/nodes/sec-six-functors/lem-sf-rational-stage-localization.json`, realizes
`Sheaf.Paper.ExceptionalRationalStageLocalization`. Source: Zheng Construction 6.2 after
Lemma 5.22 and Proposition 5.24, original item steps 1--3. It constructs only rational
operations with their raw localization and scalar comparisons. The node records the
normalized field-descent, residue-Tor and proper/open coefficient dependencies, explicit
transport steps, and the Mathlib/source search results. Its auxiliary record and field
insertion definition are actual data structures, not existence-based choices.

`lem-sf-common-stage-descent-fixed-rational`, in
`dag/nodes/sec-six-functors/lem-sf-common-stage-descent-fixed-rational.json`, realizes
`Sheaf.Paper.ExceptionalCommonStageFromRational`. Source: Zheng Construction 6.6, original
item step 4. For the already fixed rational family it descends closed adjoints and inclusion
comparisons, with the transition equation. The node records coherent-pair functor descent,
natural-Hom adjunction construction and scalar-mate dependencies. It deliberately leaves the
representative-arrow extension to the proved consumer lemma. Both nodes have the item's
chapter/unit and computed blueprint ancestry, complete source proofs, and precise Lean
attachments. No change record is needed: no shared statement or definition was changed.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
