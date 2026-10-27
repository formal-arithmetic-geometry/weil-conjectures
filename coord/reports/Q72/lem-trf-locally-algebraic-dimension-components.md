## Files written

- `dag/nodes/sec-trace-formula/lem-trf-locally-algebraic-dimension-components.json`: statement, split into four proof steps; no Mathlib match.
- No new DAG nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quote for each node used by each step.
- `searches.jsonl`: actual search-command log; every added Mathlib search record comes from it.

## Attachments

None for this item. The library searches found no project declaration giving the full non-affine statement with attainment. The related `AlgebraicGeometry.dimension_locally_algebraic` in `WeilConjectures/AlgebraicGeometry/DimensionLocallyAlgebraic.lean:56` assumes irreducibility and belongs to the already existing `lem-sc-dimension-locally-algebraic`. `AlgebraicGeometry.dimension_at_point_components` in `WeilConjectures/RingTheory/DimensionAtPointComponents.lean:206` assumes an affine finite-type algebra and is already recorded on `lem-weil-pbc-dimension-at-point-components`. Neither is an attachment for the present general statement.

## WANTED

None. All sources needed for the argument are in the read-only repository.

## Findings and corrections

The item had no proof. Its statement agrees with the first equality in Stacks Tag 0B1B, `varieties.tex`, `item-dimension-irreducibles-passing-through`, inside `lemma-dimension-locally-algebraic`. The statement is unchanged. The proof follows its affine-neighbourhood reduction, not the second equality involving closed specializations, which is outside this item.

The affine formula is already `lem-weil-pbc-dimension-at-point-components` (Stacks 00OT), so creating an affine-formula node would duplicate it. The open/component correspondence follows by maximality from the existing stronger irreducible-closed-subset order correspondence. That two-line maximality argument stays in step 2, rather than becoming a new node. The irreducible open-dimension assertion is already `lem-sc-dimension-locally-algebraic`. These two generic dimension tools are declared in `split_report.tool_uses`, since their units differ from this item's unit.

I read the current blueprint at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md` and the current chapter text. The ancestor remains `lem-trf-local-term-locality`, as confirmed by `blueprint_refs.py ancestor`; this item is a generic dimension input below its existing nearby-cycle/semistable chain, not a change of the unit route. Whole-blueprint searches for “local topological dimension”, “dimension at a point”, “irreducible components through”, and the dimension/component concept found no blueprint statement identical to this lemma (the definition of dimension is a definition, not the formula). The item's existing `blueprint.from.place` specifies the field-extension/component-dimension use; it was retained, and `same_as` is empty.

## Unfinished work

None in this one-level split. No Lean was written and no compiler, Lake, global build or local DAG/preflight checker was run.

## Review by Q72

I read Stacks `varieties.tex` at `lemma-dimension-locally-algebraic`, including the statement and proof of (3) and (5), and checked Tag 0B1B and Tag 0A21 against `stacks-project/tags/tags`. The proof of (5) chooses an affine neighbourhood, matches components through the point, compares their dimensions using (3), and invokes the affine lemma. I also read `algebra.tex` at `lemma-dimension-at-a-point-finite-type-over-field` (00OT), including its finite-component argument and attained maximum. This supplies the stronger affine assertion that the present proof needs, with a finite type algebra over an arbitrary field and no reducedness assumption.

In step 1 I opened `def-weil-finite-type-morphism` and checked that its actual cover definition supplies an affine neighbourhood whose coordinate algebra is finite type over k, by applying it to the entire affine base Spec k. Thus no unwritten assertion about arbitrary affine opens is needed. I opened `lem-weil-pbc-dimension-at-point-open-subspace`; it explicitly gives equality of local topological dimensions at a point of an open. Its statement, not its proof, supplies the other assertion of this step.

In step 2 I opened `lem-weil-pbc-open-subspace-irreducible-closed-correspondence`. It gives a bijection, its inverse by closure, and reflection as well as preservation of inclusion. Together with the maximal-irreducible definition in `def-weil-irreducible-components`, this really does identify the components: any superset of an irreducible closed set meeting U still meets U, so maximality is detected within this correspondence. Membership of the fixed x is preserved in both directions. In particular the proof does not cite the weaker `lem-sc-components-open-injection` as if it supplied surjectivity.

In step 3 I checked `lem-weil-pbc-closed-subset-closed-subscheme` against Schemes Tag 01J3 (`lemma-reduced-closed-subscheme`, read in `schemes.tex`). It supplies a closed immersion with exactly the component as its image. `def-weil-closed-immersion` supplies the homeomorphism onto that image, so the chosen scheme is irreducible. `lem-weil-pbc-immersion-base-change-lft` explicitly supplies local finite type for an immersion, and clause (e) of `lem-weil-pbc-proper-fp-permanence` explicitly supplies composition of locally finite type morphisms; I read Morphisms Tags 01T5 and 01T3 for these facts. Thus all hypotheses of `lem-sc-dimension-locally-algebraic` hold on the closed scheme representing the component. Its open preimage of U contains the lift of x and is nonempty. That lemma states exactly that such an open has the dimension of the irreducible locally algebraic scheme. Finally `lem-weil-pbc-homeomorphism-krull-dimension` identifies the dimensions of the underlying subspaces. I opened all seven cited node statements and checked these are their conclusions, without assuming that a component was already supplied with a scheme structure.

In step 4 I opened `lem-weil-pbc-dimension-at-point-components`, whose statement supplies the affine maximum, the nonempty finite set of relevant minimal primes, and the nonnegative integer dimension. Reindexing an attained maximum along the proved bijection and the proved equality of component dimensions is an elementary final inference: the affine upper bound bounds every global component, and an affine component attaining the bound produces a global component attaining it. No global finiteness of components, separatedness or quasi-compactness of X is used.

For the B–E checks: there are no new nodes to fail self-containment, duplicate or statement-only checks. All proof citations have literal quotes in citations.json, and every non-elementary assertion in the four steps names an existing statement that supplies it. The proof does not move the conclusion into a newly named lemma. Each step has fewer than 2000 characters. Edge cases checked include the empty scheme (no point), a zero-dimensional scheme (maximum zero), a reducible scheme with a plane and a line meeting at a point (the larger component determines the value there), nonreduced thickenings (all dimensions are topological), and an infinite disjoint union of affine spaces of increasing dimensions (no finite global bound is needed, since a single chart at x suffices).

The new logged Mathlib searches used LeanSearch, Loogle, LeanFinder and grep, including a second phrasing for the affine algebra version. I read the returned generic point, height, affine-chart, component-membership, standard-smooth-presentation and spectrum-dimension hits. None states the component maximum for local topological dimension. I read the local Mathlib source for topologicalKrullDim and the Smooth.lean grep hits; its global Krull-dimension definition and smooth relative-dimension instances do not supply this arbitrary locally finite type assertion. Existing search records in the item were preserved; only searches actually run in this session were appended.
