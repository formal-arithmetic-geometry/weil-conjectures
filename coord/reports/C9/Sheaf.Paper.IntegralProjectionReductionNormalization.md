## What changed

The item theorem is assembled by pasting the proper-factor and open-factor coefficient
squares. Its signature and original public import are unchanged. Two proof imports supply
those squares. No existing module other than the item is changed.

`IntegralProjectionFactorData` imports only the operation-stage interface and defines the two actual datum factors, including the source
and target equality transports, and proves their factorization in an arbitrary coefficient
category. It also proves a generic pasting lemma from associativity and functoriality;
the item applies that lemma so rewriting does not unfold the large derived-category
coordinate definitions. `IntegralProjectionMiddleMap` constructs their intermediate coefficient map by
transposing inverse pullback reduction followed by the actual proper counit, then applying
tensor reduction and the specified open coefficient map (the inverse of the actual
open reduction mate, with invertibility supplied by openReconstructionEffectivity). This is genuine data construction:
it uses neither projection, no arbitrary existence witness, and no new proof hole.

`IntegralProjectionProperFactorReduction` and `IntegralProjectionOpenFactorReduction`
state the two remaining comparisons. The first ends at the system proper image of the
intermediate tensor and contains no open projection. The second starts at that intermediate
object and contains no proper projection. The main proof pastes them, uses functoriality of
reduction, and substitutes the proved datum factorization. Thus neither residual statement
is the original theorem renamed, conjugated, or supplied with a repackaged hypothesis.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.FixProjectionCompactification.integralProjectionReductionNormalization`
(node `lem-sf-integral-projection-reduction-normalization`) by a complete Lean assembly.
The item has zero holes left, from one before this delivery.

Added two holes, each exactly the entire proof of its public theorem:

- `WeilConjectures.FixProjectionCompactification.integralProjectionProperFactorReduction`
  (`lem-sf-integral-projection-proper-factor-reduction`).
- `WeilConjectures.FixProjectionCompactification.integralProjectionOpenFactorReduction`
  (`lem-sf-integral-projection-open-factor-reduction`).

This is a decomposition: one old hole closed, two narrower holes added, net minus one.
It is not claimed as a proof free of unresolved dependencies. The generic
`ProjectionFactors.factorization` is proved without a new hole; all new definitions have
actual composite bodies. Every residual theorem has its source and argument in its docstring
and corresponding node. Server validation is through lcompile.py and deliver3.py only.

The actual system proper factor has an explicitly typed wrapper, systemFirst. It retains
the same mate while avoiding repeated expansion of postcomposition and whiskering types
in the proper-factor statement. Profiling showed subsecond theorem elaboration/type checking;
all temporary profiler options and diagnostics have been removed. The final generic
pasting lemma and item assembly were accepted by lcompile.py, as were both factor
statements and the explicit comparison data.

## No longer needed

No original import is removed; no module is withdrawn. No unit statement or unit proof
step is bypassed (`sk-rem-sf-pf-done` has empty realized statement/steps records).

The item's direct proof dependencies are now the two factor squares and their data.
Its former dependencies `lem-sf-integral-compactification-system-realization`,
`lem-cbc-completed-extension-zero-comparison` and `lem-coef-integral-residue-tor` are not
applications in the assembly itself. The last two remain dependencies of the open-factor
comparison; residue Tor also remains a dependency of the proper-factor comparison.
The supplied realization data is used directly, so a new application of the existential
`integralCompactificationSystemRealization` is unnecessary. No global pruning of those
modules is claimed, since the existing coordinate construction and other consumers use them.

## Where the brief, the DAG or earlier work was wrong

The planned two mathematical steps were not consequences obtained merely by applying the
existence theorem `integralCompactificationSystemRealization`: the item already receives
its actual `o` and `z`. That theorem does not identify the datum's projection with the
explicit `Coordinates` maps. The remaining tasks are precisely normalization of the
proper counit factor and normalization of the open tensor/compositor factor. The operation
datum's integralNormalization fields are needed when identifying its support/open/direct
coordinates; the residual proofs record them explicitly.

Searches: msearch LeanFinder returned generic monoidal-adjunction counit facts; Loogle did
not know the source-library rightAdjointProjectionMap identifier; msearch grep found no
Mathlib projection/reduction match. LeanSearch returned unrelated geometric gluing facts.
Local searches found GeneratorReductionStatement and OpenTensorReductionSquare in the
ordinary/completed expression coordinates, and IntegralProjectionOperationPresentation,
which supplies an existential arrow isomorphism rather than these fixed coefficient maps.
Blueprint searches found no duplicate proper/open factor square. The new statements were
checked on identity proper factors, identity and empty opens, and zero inputs: their maps
retain the actual adjunction units/counits, so these cases use the same equations.

## New nodes

`def-sf-integral-projection-factor-data` records the actual two datum factors and the
proved generic factorization. Module: `Sheaf.Paper.IntegralProjectionFactorData`.

`def-sf-integral-projection-middle-map` records tensor and proper-pullback coordinates,
the actual direct-image mate, open coefficient map, their middle composite, and the system
proper and open factors. Module: `Sheaf.Paper.IntegralProjectionMiddleMap`.

`lem-sf-integral-projection-proper-factor-reduction` is the coefficient square for the
proper factor, ending before the open tensor map. Module:
`Sheaf.Paper.IntegralProjectionProperFactorReduction`.

`lem-sf-integral-projection-open-factor-reduction` is the coefficient square for the open
factor, starting after the proper projection. Module:
`Sheaf.Paper.IntegralProjectionOpenFactorReduction`.

No change record is needed: no existing statement, definition, attribute or public import
is changed. New public declarations are under Sheaf only.

The new nodes request generic tool use of generator reduction coherence, integral open
reduction comparison, completed extension-by-zero comparison, and residue Tor. These are
coefficient normalization tools; they replace no unit statement or prescribed unit step.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
