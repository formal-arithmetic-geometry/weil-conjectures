Files written:

- `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-diagonal-basechange-upper-shriek.json`: statement, split proof, and blueprint fields; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-basechange.json`: new statement-only dependency; Mathlib searches found no match.
- `citations.json`: verbatim quotations for both proof steps.

Attachments: none.

WANTED: the local checkout has no `literature/stacks-project/duality.tex`; I checked the official Stacks Project Tag 0AAB and Tag 0E2P pages online for the source statements and proofs.

## Review by G1

I read the imported item and its parent `lem-sc-smooth-proper-diagonal-pushforward-structure`. The parent uses exactly the formula in this item, with `pr_2` as the derived pushforward and `pr_1` as the derived pullback. I searched the full DAG and blueprint for the Tag 0AAB/48.12.4 base-change assertion and for right-adjoint base-change wording; no existing node states it. The slopmaster2 source contains no declaration tagged with this item, and the item has no Lean declaration to attach.

The new node is the strictly more general Tag 0AAB statement: both schemes are Noetherian, the base-change morphism is arbitrary, the original morphism is proper, flat, and finitely presented, and the conclusion is the canonical isomorphism `a'(Lg^*K) = Lg_X^*a(K)` for every quasi-coherent derived object. It is statement-only because it is not itself being split in this delivery. Its statement introduces the cartesian square, both projections, both right adjoints, the derived categories, and the base-change isomorphism. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` under the new node id; LeanSearch was unavailable and is recorded as unavailable, while the other searches found only generic sheaf adjunctions or no result.

Step 1 applies the new statement with `Y'=X`, `g=f`, and the original `f:X -> S`; the resulting square is `P=X x_S X`, with `g_X=pr_1` and `f'=pr_2`. The hypotheses are exactly those in the item. Step 2 reads the resulting right adjoint `a'` as the given `b`, identifies the two derived pullbacks, and evaluates at `K=O_S`; the displayed target is precisely `b(O_X) = L pr_1^* a(O_S)`. The only elementary content is this specialization and the unit identity for derived pullback. `citations.json` quotes the exact statement clauses used by each step.

I checked the edge cases conceptually: for `g=id_Y`, the base-change map is the identity; for the item with `X=Spec(S)` and `f=id`, both right adjoints and pullbacks reduce to identities. No statement was weakened, and no clause of the parent diagonal-counit conclusion was moved into the new node.

What I could not finish: no local Stacks TeX checkout is present, so the source check used the official online tags; no Lean compilation is permitted for stage 1.

## Second reading by G1

- Item statement: checked against Stacks Tag 0E2P (Lemma 48.12.8), including the self-product projections and right-adjoint base-change conclusion; verdict: agrees hypothesis by hypothesis.
- Auxiliary node `lem-sc-proper-flat-right-adjoint-basechange`: checked against Stacks Tag 0AAB (Lemma 48.12.4), including qcqs bases, proper flat finite-presentation hypotheses, and the canonical base-change isomorphism; verdict: corrected to the source's qcqs hypotheses and is self-contained.
- Step 1: checked against the cartesian-square specialization in Tag 0E2P and the statement of Tag 0AAB; verdict: the assignments `Y'=X`, `g=f`, `g_X=pr_1`, and `f'=pr_2` are correct, with Noetherian schemes supplying qcqs.
- Step 2: checked against the third equality of Tag 0E2P and the existing structure-sheaf pullback node; verdict: specialization at `K=O_S` is correct and `Lf^*O_S ~= O_X` is now cited explicitly.
- Edge cases: identity base change and identity morphism give identity isomorphisms; empty and affine field cases are consistent with the statement.
- Changes: aligned the auxiliary node's base hypotheses with Tag 0AAB, added `lem-weil-pbc-module-pullback-structure-sheaf` to Step 2 and `proof_deps`, updated the verbatim citations, and recorded this review.
