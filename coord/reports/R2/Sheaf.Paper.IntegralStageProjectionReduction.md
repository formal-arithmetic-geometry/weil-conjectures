## What changed

Replaced the hole in `WeilConjectures.integralStageProjection_reduction` by the
composition of three arrow isomorphisms. The first is scalar reduction of an
integral operation-presentation comparison. The middle is constructed with
`Arrow.isoMk` from the invertible source/target comparisons and commuting square
of `ConcreteIntegralProjection.concreteIntegralProjectionCone`. The last is the
finite operation-presentation comparison. An explicit equality obtained by
`congrArg` from `hLₘ.symm`, transported by `eqToIso`, connects its first arrow
to `finiteArrow`. The tensor models are obtained from the proved
`PurCompactSupport.tensorModel_exists`, not an unproved existence theorem.

Added two modules, `Sheaf.Paper.IntegralProjectionOperationPresentation` and
`Sheaf.Paper.FiniteProjectionOperationPresentation`, for the two remaining
same-coefficient coordinate comparisons. Both statements have complete proof
plans and source references. The item imports those modules and the concrete
cone theorem privately. Its existing public imports, statement, universes and
visibility remain unchanged. No source-library file or existing definition was
changed, and no consumer adaptation is needed.

Validation: `lcompile.py --all` compiled all three modules cleanly, with no
remaining compiler errors or warnings. The item signature was compared with
the shared source and is identical.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.integralStageProjection_reduction`
(node `lem-sf-integral-stage-projection-reduction`). No `sorry` remains in the
item module. This is a decomposition, not a net proof gain: two holes are added,
so the local count changes from one to two.

The added holes are exactly:

- `WeilConjectures.integralProjection_operationPresentation`, node
  `lem-sf-integral-projection-operation-presentation`;
- `WeilConjectures.finiteProjection_operationPresentation`, node
  `lem-sf-finite-projection-operation-presentation`.

The integral comparison has no finite level, scalar reduction or finite
operation datum; it identifies the two integral presentations alone. The finite
comparison takes arbitrary already-finite inputs, has no integral lift, and
identifies the two finite presentations alone. Neither repeats the original
integral-to-finite compatibility statement. The original argument still has
substantive Lean glue: map the integral arrow isomorphism, extract the actual
reduction square, construct an arrow isomorphism from it, rewrite `hLₘ`, and
compose. Neither projection is assumed invertible.

## No longer needed

The direct proof dependency
`lem-sf-concrete-projection-reduction-square`
(`Sheaf.Paper.ConcreteProjectionReductionSquare`) is removed from this node.
That theorem compares successive finite levels, while the actual
integral-to-finite square needed here is already part of
`concreteIntegralProjectionCone`. Its module was not imported in the original
item and is not imported in this delivery. No existing Lean import was removed,
and no module is withdrawn or claimed globally unreachable. The concrete cone
node and its dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

The planned phrase "identify the two reduced endpoints" hides two presentation
changes absent from the cited signatures. The cone theorem gives a square for
`SfProEtaleProjection.integralMap` and `finiteReductionProjection`; the goal uses
the operation projection and the fixed-scalar-realized finite component. The
successive finite reduction square does not supply either missing comparison.
The new nodes state those steps separately, and the revised item node describes
the actual Lean composition.

Searched both library roots for `finiteReductionProjection`, `fixedComponent`,
and integral projection/reduction names. Read the concrete cone, finite
reduction square, finite component definitions, higher-operation normalization
fields, and the closest existing `finiteProjectionPresentation_isIso`. The last
requires separated structure maps and finite Tor on the first finite input;
those extra hypotheses cannot be used here. The constant-scalar derived
projection identification supplies a general proof tool for the finite
presentation step, not the specialized compact-support arrow isomorphism.

The metadata cites the definition of the counit/open projection, rather than
the full finite-reduction theorem: the latter would introduce a cycle through
later duality statements, although none of those is used by this proof.

The current blueprint's `fix-prop-projection-formula.proof.md` and the unit
`sk-rem-sf-pf-done` retain the finite formula, specified reduction compatibility,
adic reconstruction and field transport route. No unit statement or step was
bypassed. A blueprint search with separate words `projection presentation` returned
29 broad hits, including the four-stage projection theorem already inspected;
none is either same-coefficient presentation lemma. Searches with the exact
phrases "projection presentation" and "integral projection normalization"
returned no hits. The helper
`blueprint_refs.py ancestor` does not recover an ancestor through the historical
module-valued `created.item`; the new nodes therefore explicitly record the
existing ancestor `fix-prop-projection-formula` and the two intermediate nodes.

Edge cases checked in the new statements: zero inputs, empty schemes, exponent
one (`m=0`), identity-open compactifications, and nonseparated structure maps.
The comparisons concern actual normalized counit/open composites and remain
valid in these cases. No Tor restriction on the first input or separatedness
of the structure morphisms is added. The ordinary tensor comparison is on flat
K-flat representatives; the integral completion-unit argument uses qcqs
finite-type schemes, rather than faithfulness of finite reduction on maps.

## New nodes

`lem-sf-integral-projection-operation-presentation` compares the operation
projection with the completed-unit ordinary integral projection, entirely over
the completed integral ring. Its proof separates endpoint normalization,
proper/open adjunction transposes, and completion-unit uniqueness. It uses the
existing tensor-completion, ordinary/completed pullback and qcqs unit lemmas as
generic tools, as does the existing concrete projection development.

`lem-sf-finite-projection-operation-presentation` compares the intrinsic finite
projection with the finite component defined by fixed-scalar realization. Its
proof separates tensor/endpoint realization, agreement of proper and open
transposes, and cancellation of the component's conjugating isomorphisms. The
general constant-scalar derived projection identification is used as a tool
for tensor and adjunction normalization; it assumes no proper base change or
projection-formula invertibility. Both nodes record the actual leanfinder,
loogle and Mathlib grep searches made for this item. No change record is needed
because no existing statement or definition is changed.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
