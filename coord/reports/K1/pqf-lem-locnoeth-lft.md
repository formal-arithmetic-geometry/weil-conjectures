Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-locnoeth-lft.json`: item converted to a Mathlib leaf; no new nodes.
- `citations.json`: empty, because the Mathlib leaf has no proof steps.

Attachments:

- None. No sorry-free project declaration states this item exactly.

WANTED:

- None.

## Not duplicates

- `pqf-lem-locnoeth-lft` vs `lem-weil-pbc-finite-type-over-noetherian`: the existing node assumes a finite type morphism and a Noetherian target and concludes that the source is Noetherian (including quasi-compactness); this item assumes only locally finite type and locally Noetherian target and concludes only locally Noetherianity.

## Review by K1

I read the imported item and its proof source, Stacks Morphisms, Lemma 29.15.6, Tag 01T6, and checked the statement hypothesis by hypothesis against Mathlib's declaration `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` in `Mathlib/AlgebraicGeometry/Noetherian.lean:239`. The declaration has a morphism `f : X ⟶ Y`, an inferred `[LocallyOfFiniteType f]` hypothesis, an inferred `[IsLocallyNoetherian Y]` hypothesis, and conclusion `IsLocallyNoetherian X`, exactly matching the item's `f : X -> S`, locally finite type, locally Noetherian target, and locally Noetherian source conclusion. I read lines 239--242 directly.

The imported paragraph proof is therefore replaced by the Mathlib leaf form: there are no proof steps or proof dependencies, and `citations.json` is empty. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches, including alternate phrasings. LeanFinder returned the exact declaration and its matching documentation twice; Loogle and msearch grep returned no hits (the service reported unknown identifiers/zero hits); LeanSearch was unavailable with an Internal Server Error, recorded as unavailable. The direct Mathlib source inspection verified the exact theorem despite those service results.

I searched the DAG and blueprint for Tag 01T6 and the local-Noetherian/finite-type wording. The only potentially related existing node is `lem-weil-pbc-finite-type-over-noetherian`, whose stronger conclusion and stronger hypotheses differ as recorded above, so it is not a duplicate and no new node is needed.

## What was wrong or changed

The imported node contained an agent-written affine proof and was still `imported`, although Mathlib already states the result exactly. It is now `status: mathlib` with `proof: []`, `proof_deps: []`, `proof_origin: null`, and an exact `mathlib_match`.

## What remains

Nothing remains for this item.

## Second reading by K1

- Item statement: checked against Stacks Morphisms, Lemma 29.15.6, Tag 01T6, and Mathlib `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` in `Mathlib/AlgebraicGeometry/Noetherian.lean:239-241`; the locally finite type and locally Noetherian hypotheses and locally Noetherian conclusion agree. Verdict: correct.
- Proof steps: no steps are present because this is a Mathlib leaf; there were therefore no uncited dependencies or elementary-step claims to audit. Verdict: correct.
- New nodes: none. The item itself is the only node, so B1-B7 and duplicate-node checks do not introduce any additional node. Verdict: correct.
- Edge cases: the statement is vacuous for the empty scheme, and specializes correctly to a field base and to zero-dimensional or one-point schemes; no extra hypotheses are introduced. Verdict: correct.

Changes made: none to the node or citations; this section records the independent source, declaration, dependency, and edge-case checks. The delivery preflight passed unchanged.
