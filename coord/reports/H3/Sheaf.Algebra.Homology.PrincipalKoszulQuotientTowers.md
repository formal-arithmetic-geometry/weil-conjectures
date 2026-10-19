## What changed

Filled all six proofs in `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`.
The endomorphism-power induction supplies both transition identities. Mathlib's
`mappingCone.map_descShortComplex` proves augmentation naturality, using the strict
cokernel factorization. The tensor differential is checked by a proved private lemma
for an arbitrary closed map from the tensor unit; specializing it to the single
complex gives the prescribed component equation. Cone inclusion identities and
functoriality prove the two representative augmentation compatibilities.

Existing public signatures, definitions, imports and the unit route are unchanged.
Two existing long attribute lines were wrapped to meet the 100-column limit.

Resumed validation against the current published build: the unchanged retained
module compiled cleanly through `lcompile.py` in 19.2 seconds, within the existing
60-second limit. The previous delivery log records a Git checkout timeout, not
a Lean timeout; the retained generic tensor helper already avoids specializing
the total-complex coproduct construction during the differential calculation.

## Proved and sorry left

Closed six existing holes, all belonging to
`def-pur-principal-koszul-quotient-towers`:

- `CategoryTheory.principalKoszul_transition_square`
- `CategoryTheory.principalQuotient_transition_zero`
- `CategoryTheory.principalAugmentation_naturality`
- `CategoryTheory.koszulTensorUnitComponent_comm`
- `CategoryTheory.koszulRepresentativeAugmentation_quotient`
- `CategoryTheory.koszulRepresentativeAugmentation_naturality`

No holes remain in the item. No holes were added and no statements were split off.
The private helpers `endoPow_succ_left` and `tensorClosedUnitLeft_comm` are proved.

## No longer needed

None. No imports were added or removed. The node has no declared proof dependencies
to prune; the proof follows the existing constructions and declaration docstrings.
No node or module is made unnecessary by this delivery.

## Where the brief, the DAG or earlier work was wrong

The node's `proof` list is empty, although the declaration docstrings give the
needed calculations. Those calculations suffice using Mathlib's existing cone,
cokernel, total-complex and monoidal-category APIs. No statement repair is needed.
The generic tensor helper avoids unfolding the specialized single-complex
coproduct instance during rewriting. Its proof uses only preservation of zero
morphisms, with no added tensor additivity or K-flatness assumption.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
