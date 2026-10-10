# Stage 1 report: lem-sc-finite-integral-conductor

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-finite-integral-conductor.json`: split item, no Mathlib match.

## Attachments

None. No sorry-free slopmaster2 declaration states the item exactly.

## WANTED

None.

## What I checked

I read the imported item and the reviewed parent split `lem-sc-semilocal-dim-one-conductor`, including its citation of Varieties Lemma 09N2. The item statement matches the paragraph beginning “Since the fraction fields of B and A are the same”: B is Noetherian, semilocal, a domain of dimension one; A is finite over B inside the common fraction field; and a positive power of the Jacobson radical sends A into B.

The proof uses two existing Mathlib-leaf DAG nodes: the support/annihilator equality `lem-weil-pbc-finite-module-support-annihilator` and the radical-power lemma `lem-weil-pbc-fg-ideal-radical-power`. No new node was created because the combined support-to-conductor assertion is a clause of this item under delivery-errors D1/D2.

Step 1 constructs M=A/B. Finiteness of a quotient is elementary, and equality of fraction fields makes the generic localization zero. Step 2 uses the new node exactly as stated: dimension one and the domain hypothesis turn every nonzero prime in the support into a maximal ideal. Step 3 translates m_B^n M=0 back to m_B^n A contained in B by the definition of the quotient. I checked the edge cases B already normal (A=B, where n=1 works) and a nonnormal one-dimensional local domain (the normalization conductor situation), and retained the dimension-one hypothesis because without it nonmaximal nonzero primes can occur.

## Review by E1

I checked the source paragraph in Varieties Lemma 09N2 and the parent node's use of this item. Every cited node is quoted verbatim in `citations.json`; Step 2 uses exactly the support/annihilator statement and the finitely-generated-ideal radical-power statement. Step 1 and Step 3 are elementary quotient arguments, while Step 2 verifies that B is Noetherian and one-dimensional, that the generic support is empty, and that the Jacobson radical is contained in the radical of the annihilator. The imported empty proof and status were replaced with the three source-aligned steps and the document proof origin. I also removed an unnecessary citation to the finite-adjoin lemma: A is already assumed finite in the item.

## Second reading by E1

- Item statement: checked against Stacks Varieties Lemma 09N2 (label `lemma-semi-local-dimension-one-conductor`), including the semilocal Noetherian one-dimensional domain, finite intermediate algebra in the common fraction field, and conductor-power conclusion; verdict: agrees hypothesis by hypothesis.
- Step 1: checked against the 09N2 finite-module paragraph and quotient/localization definitions; the finite quotient and generic-point vanishing are elementary; verdict: sound.
- Step 2: checked the statements of `lem-weil-pbc-finite-module-support-annihilator` and `lem-weil-pbc-fg-ideal-radical-power` verbatim in `citations.json`; nonzero support primes are maximal in dimension one, and the Jacobson-radical containment follows; verdict: sound.
- Step 3: checked against the concluding sentence of the same 09N2 paragraph and the quotient definition; verdict: elementary and sound.
- New-node audit: there are no supporting new nodes; existing Mathlib leaves were searched for finite-module support/annihilator and radical-power results, with no exact conductor theorem found.
- Edge cases checked: `A = B` (take `n = 1`), a field (zero quotient), and the zero quotient; all satisfy the statement. The dimension-one hypothesis is needed for the maximal-support step.
- Changes: corrected all source `place` fields to include the exact Tag 09N2 label; no mathematical or dependency changes were needed.
