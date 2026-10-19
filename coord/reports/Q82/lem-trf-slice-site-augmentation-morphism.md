# Stage-1 report: lem-trf-slice-site-augmentation-morphism

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-slice-site-augmentation-morphism.json`: existing item updated to status `split`, with five proof steps and no new nodes.
- `citations.json`: 16 step-to-node citations with verbatim statements.
- `report.md`: this report.

## Attachments

None. I searched the project source and the archived master source for the blueprint tag and the equalizer/right-adjoint description; no sorry-free project declaration states this item exactly.

## WANTED

None. The cited Stacks source is present locally at `literature/stacks-project/spaces-simplicial.tex`.

## Not duplicates

- `lem-trf-slice-site-augmentation-morphism` vs `lem-trf-total-site-augmentation-spectral-sequence`: the existing node states a much larger derived module spectral-sequence theorem; its statement does not assert the generic set-valued equalizer adjunction, so it cannot replace this item.
- `lem-trf-slice-site-augmentation-morphism` vs `lem-trf-slice-site-simplicial-augmentation`: the existing node constructs the slice-site diagram and its component localization morphisms for an actual simplicial object; this item assumes an arbitrary coherent augmented diagram and proves the equalizer right adjoint.
- `lem-trf-slice-site-augmentation-morphism` vs `lem-trf-site-augmentation-acyclic-cech`: the existing node proves an augmented Cech kernel statement for abelian sheaves on a slice site, whereas this item proves the topos-level adjunction for arbitrary compatible systems.

## What was checked and corrected

The imported item was unsplit and had an incorrect `split_report.item` value referring to `lem-trf-slice-site-simplicial-augmentation`; I corrected that metadata and supplied the missing proof. The statement, hypotheses, source, statement dependencies, and existing Mathlib-search history were retained. No definition or target statement was changed.

## Review by Q82

I read the item, the chapter `sec-trace-formula`, and unit `sk-i-curve-zero`, then read the full statements of `def-weil-pbc-topos`, `def-weil-size-convention`, `def-trf-geometric-morphism`, `lem-trf-slice-site-total-pseudofunctor`, and `lem-trf-slice-site-total-systems`. Step 1 uses the total-site construction and the compatible-system equivalence exactly as their statements provide, and uses the given coherent identifications to define the component system. Step 2 uses the geometric-morphism definition that inverse images preserve finite limits and the componentwise compatible-system description; no extra exactness hypothesis is introduced. Step 3 defines the two degree-zero-to-degree-one maps from the two `[0]→[1]` operators and takes their equalizer in the topos `D`; the cited topos statement supplies the topos setting and the cited systems statement supplies the transition data. Step 4 uses only the adjunction and the system statement: the equalizer condition is the vertex/edge compatibility, every pair of vertices of `[n]` is joined by an order map `[1]→[n]`, and the coherence laws give the identity/composition compatibility; the converse is restriction to degree zero. Step 5 checks naturality and invokes the stated definition of geometric morphism. I checked the two small edge cases explicitly: a constant system, where the equalizer condition is automatic and the recovered family is constant, and a system with unequal degree-one maps, where the equalizer cuts out precisely the maps satisfying the two edge equations. All 16 citation quotes are copied verbatim from the cited node statements. I also searched for duplicate statements and found only the larger spectral-sequence and slice-site construction nodes listed above; neither states this adjunction. No Lean was written or compiled, as required for stage 1.

## What could not be finished

Nothing. The split has no new unsplit nodes and no outstanding WANTED source.
