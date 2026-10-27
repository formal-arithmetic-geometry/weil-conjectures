## What changed

Proved `WeilConjectures.automorphismConstructibleStage_square_reduction` in the
assigned module. The private proved helper `integral_composition_reduction`
computes the entire-system reduction of the specified integral compositor.
It instantiates the generic proved helper `counit_compositor`, which uses counit
naturality and cancellation of the actual eta isomorphism. The generic proved
helper `reduction_square_paste` applies the two compositor computations to the
commuting square and cancels their invertible maps. Equality transport is handled
by equality induction. These private helpers keep the categorical calculation
separate from the large realization definitions. A local reducibility setting
for the existing full-subcategory lift exposes its underlying ambient objects;
the ambient derived pullback stays irreducible during elaboration. Transparency
checks remain enabled in the new proof. The concrete system square is normalized
through a whole-isomorphism equation and abstract component calculations, avoiding
expensive kernel unfolding of its derived-category components.

The proof concerns morphisms of entire quotient systems, including their
transition data. No assertion of joint faithfulness of finite reductions is used.
All existing signatures, definitions and imports are unchanged. The node records
this direct implementation of the reduction clause.

Validation: the complete assigned module compiled through `lcompile.py` in
44.0 seconds, with exit code zero. Temporary debug files and all profiling
options were removed before this check. All new proof helpers are proved;
there are no new declarations containing `sorry`.

## Proved and sorry left

Closed one of the seven original holes:
`WeilConjectures.automorphismConstructibleStage_square_reduction`.
Added zero holes and split off zero statements. Six existing holes remain, all
attached to `lem-sf-automorphism-constructible-stage-equivalence`:

- `WeilConjectures.automorphismStageQbarSquare_existsUnique`.
- `WeilConjectures.automorphismConstructibleStage_comparison_system`.
- `WeilConjectures.automorphismConstructibleStage_integral_coherence`.
- `WeilConjectures.automorphismConstructibleStage_integral_shifts`.
- `WeilConjectures.automorphismConstructibleStage_descended_shifts`.
- `WeilConjectures.automorphismConstructibleStage_inverse_comparisons`.

## No longer needed

None. The square-reduction clause follows directly from the existing definitions
instead of invoking the completed-operation substitution theorem. That theorem
and all other declared dependencies remain needed by the retained unfinished
clauses, so no import, module, node or tool approval is removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The direct counit computation is sufficient for the
square-reduction clause. This is a partial delivery on a module with several holes.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
