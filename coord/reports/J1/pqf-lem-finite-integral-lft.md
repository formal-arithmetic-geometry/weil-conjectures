# Stage 1 report: pqf-lem-finite-integral-lft

## Files written

- `dag/nodes/sec-abelian-varieties/pqf-lem-finite-integral-lft.json`: item recorded as a Mathlib leaf; no new nodes.
- `citations.json`: empty because a Mathlib leaf has no proof steps.

## Attachments

None. No sorry-free project declaration carrying the item tag or exact statement was found in `WeilConjectures/`.

## WANTED

None.

## What I checked

The item source is the imported blueprint node for Stacks Tag 01WJ, whose assertion is that every finite morphism of schemes is integral. I searched the project source for the item id, its blueprint tag, and finite/integral morphism terminology; no project declaration states this item. I also searched the DAG and blueprint for duplicate statements and found no existing node to cite.

Mathlib states the assertion directly through `AlgebraicGeometry.IsFinite.instIsIntegralHom`, in `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:117-118`: for a scheme morphism `f` with `[IsFinite f]`, it supplies `[IsIntegralHom f]`. The item has no proof steps or dependencies after this exact match. LeanFinder and Loogle searches returned this declaration; source grep confirmed the instance and its lines. LeanSearch returned an unavailable service response, recorded as such in `mathlib_searches`.

## Review by J1

I read the item's imported Stacks/blueprint statement and checked that its hypotheses and conclusion match the Mathlib instance exactly: both concern an arbitrary morphism of schemes equipped with the finite-morphism property and conclude the integral-morphism property. I read the surrounding Mathlib source, including the definition of `IsFinite` and the instance at lines 117-118, rather than relying only on a search summary. Since the item is an exact Mathlib leaf, there are no proof steps, cited nodes, or edge-case constructions to split; `citations.json` is empty. I checked the small conceptual cases of the identity finite morphism and a finite affine map `Spec B -> Spec A`, both covered by the same instance. The imported determinant-trick proof was removed from the node because Mathlib supplies the theorem directly.

## What was wrong or incomplete

The imported node was not marked as a Mathlib leaf and carried an unnecessary proof sketch. Its source path refers to the blueprint checkout, which is not present as a separate file here; the node's statement and Stacks Tag 01WJ metadata were sufficient for the comparison.

## What I could not finish

Nothing.

## Second reading by J1

- Item statement: checked against Stacks `morphisms.tex`, Lemma 29.45.4, label `lemma-finite-integral`, Tag 01WJ; the finite-morphism hypothesis and integral-morphism conclusion agree exactly.
- Mathlib leaf match: checked against `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:117-118`; `IsFinite f` supplies `IsIntegralHom f` for a scheme morphism, matching the item.
- Proof steps: the imported determinant-trick step is removed by the Mathlib leaf status; there are no remaining steps or citations to audit.
- New nodes: none; B1-B7 and duplicate-node checks are vacuous.
- Edge cases: identity finite morphisms, finite affine maps `Spec B -> Spec A`, and the empty scheme are covered by the same universal instance; no hypothesis is added.
- Changes: recorded the full Stacks lemma label in `source.external.place` and documented this second reading; no mathematical statement was changed.
