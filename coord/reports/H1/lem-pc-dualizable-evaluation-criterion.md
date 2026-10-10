Files written:

- `dag/nodes/sec-picard-framework/lem-pc-dualizable-evaluation-criterion.json` (statement, split; no new nodes)
- `citations.json`

Attachments: none.  WANTED: none.

## Not duplicates

lem-pc-dualizable-evaluation-criterion vs lem-pc-perfect-rhom-tensor-comparison: this node proves the abstract closed-monoidal criterion from an evaluation isomorphism, while the existing node proves the scheme-level perfect-complex comparison that supplies that hypothesis.

## Review by H1

I read the item statement and the source cited as Stacks Tag 0FPC, cohomology-example-dual-derived. The statement retains the explicit derived tensor/internal-Hom adjunction, defines the evaluation maps and the unique coevaluation, and states both triangle identities. No new node was needed: both proof steps are the standard two-line adjunction calculation, using only the existing node `lem-sc-derived-internal-hom-adjunction`, whose statement supplies the natural Hom bijection and its functoriality.

Step 1 uses the cited adjunction to identify the adjunct of the K-triangle with `id_K`; invertibility of `phi_K` then gives the first identity. Step 2 uses the same naturality and the first identity to identify the adjunct of the D-triangle with the adjunct of `id_D`; invertibility of `phi_D` gives the second identity. The hypotheses are checked for arbitrary objects `M`, in particular `K` and `D`, exactly as required by the item. I checked the zero-object and one-term finite-free cases, where the calculation reduces to the ordinary tensor-Hom adjunction. The Mathlib searches already recorded on the item were rerun: LeanFinder found only generic rigid-category Hom equivalences, Loogle and grep found no exact criterion, and LeanSearch was unavailable.

## Second reading by H1

- Item statement: checked against Stacks Tag 0FPC (`cohomology-example-dual-derived`), including the hypotheses on `X`, `K`, `D`, `e`, every `phi_M`, and the definition of `eta`; verdict: agrees hypothesis by hypothesis and states both zig-zag identities.
- Step 1: checked against `lem-sc-derived-internal-hom-adjunction` and the first zig-zag clause of Tag 0FPC; verdict: the cited Hom bijection and functoriality support the adjunct calculation, and invertibility of `phi_K` is an explicit item hypothesis.
- Step 2: checked against the same adjunction statement and the second zig-zag clause of Tag 0FPC; verdict: naturality with `u=e`, symmetry, associativity, and the first triangle give the adjunct comparison, while invertibility of `phi_D` supplies faithfulness.
- New nodes: none; the existing-node search found the adjunction and no duplicate criterion or exact Mathlib criterion, so B1-B7 do not apply.
- Edge cases: the zero object and one-term finite-free complexes reduce to the ordinary tensor-Hom calculation; `M=K` and `M=D` satisfy the universal hypothesis.

Changes made: corrected the node's `created.item` metadata to this delivered item; no mathematical statement or proof step changed because the source and dependency audit found them consistent.
