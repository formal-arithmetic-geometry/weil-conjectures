1. Files written:

   - `dag/nodes/sec-abelian-varieties/pqf-lem-affine-vanishing.json`: statement node, split; no new node files.

2. Attachments:

   - `AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine` belongs to existing node `lem-pc-affine-vanishing` (the declaration is closed and states the affine-scheme specialization used in Step 2).

3. WANTED:

   - WANTED: Stacks Project Cohomology of Schemes, Lemma 30.2.2, Tag 01XB, if the full Stacks source is required locally; the repository contains the citation but not the Stacks checkout.

4. Problems found:

   - The item has no exact sorry-free declaration in the project source: the available closed declaration is for an affine scheme `X = Spec A`, while this item is phrased for an arbitrary scheme and affine open `U`.
   - The existing blueprint proof records the Stacks input without the reduction from an affine open to its induced affine scheme. I made that reduction explicit in Steps 1 and 3 and cited the existing affine-scheme node in Step 2.

5. Nothing remains unfinished in the split. No new node was needed because the affine-scheme result already exists as `lem-pc-affine-vanishing` and the two restriction identifications are elementary.

## Review by G1

I read the item node, the `sk-prop-av-pqf-finite` unit record, and the source declaration in `WeilConjectures/AlgebraicGeometry/Cohomology/Affine.lean` at lines 284–308. That declaration is sorry-free and proves vanishing for a quasi-coherent module on an affine scheme, but it does not itself state the arbitrary affine-open formulation, so I did not attach the item directly. I also checked the existing DAG node `lem-pc-affine-vanishing`; its statement is exactly the affine-scheme theorem quoted in `citations.json`, so Step 2 takes precisely the conclusion it claims.

Step 1 checks that an affine open is treated as its induced open subscheme, that quasi-coherence restricts to it, and that the affine-open hypothesis supplies the affine-scheme hypothesis. Step 2 applies the cited node with the restricted module and translates its positive-degree notation to the stated vanishing. Step 3 checks that cohomology of the induced open subscheme with the restricted module is the same `H^p(U,F)` appearing in the item. I marked only these two identifications elementary; the sole non-elementary input is cited. I ran LeanFinder, Loogle, Mathlib grep, and LeanSearch searches for the item; LeanSearch was unavailable and is recorded as such. Small cases are consistent: for `U = Spec A` this reduces directly to the cited theorem, and for `p = 0` the statement makes no vanishing claim.

## Second reading by G1

- Item statement: checked against Stacks Project Lemma 30.2.2, Tag 01XB; hypotheses and conclusion agree exactly (scheme X, quasi-coherent module F, affine open U, all p > 0).
- Step 1: checked against the definition of an induced open subscheme and restriction of a quasi-coherent module; the affine-open hypothesis supplies the affine-scheme hypothesis, so the reduction is elementary.
- Step 2: checked against existing node `lem-pc-affine-vanishing` and its closed declaration `AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine` (Affine.lean:284–308); the cited statement gives exactly the required positive-degree vanishing after restriction.
- Step 3: checked against the definition of cohomology on an open subscheme and restriction; it identifies the induced-scheme notation with the item’s `H^p(U,F)` and is elementary.
- New nodes: none; the existing affine-scheme node was searched for and reused, so B1–B7 do not introduce a new statement.
- Small cases: `U = Spec A` specializes to `lem-pc-affine-vanishing`; the empty affine open and p = 0 are consistent with the quantified conclusion.

Changes made in this second reading: filled the item’s blueprint `from.node` and `from.place`, made the split report name the three blueprint proof locations explicitly, and added this source-based second-reading record. No mathematical statement, proof step, or citation quote required correction.
