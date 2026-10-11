1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-pseudo-coherent-lift-stably-free-complex.json` (statement, split)
- `dag/nodes/sec-abelian-varieties/lem-sc-complex-lift-class-projective.json` (statement-only, unsplit, Mathlib no match)

2. Attachments: none.

3. WANTED: none; the Stacks source was available at `/home/ubuntu/c1-stacks-review/more-algebra.tex` and was read at the cited labels.

4. The item had no proof and no exact sorry-free declaration in `WeilConjectures/`. I searched the DAG and blueprint for the Tag 0BCB statement and for the general complex-lifting input; no duplicate was found. The new node is strictly more general than the item: it abstracts the class of modules and states the five hypotheses and the quotient-complex conclusion. The item proof specializes it to finite stably free modules and records the source's checks: finite stably free modules are projective; split short exact sequences give the two-out-of-three closure; Nakayama gives surjectivity from reduction modulo the ideal; stable presentations lift by kernel construction; and pseudo-coherence gives the required bounded-above finite-free representative. The zero module and the case $I=0$ are consistent with the construction.

## Review by H1

I read More on Algebra, Lemma 15.75.2 (`lemma-lift-complex`) and Lemma 15.75.6, Tag 0BCB (`lemma-lift-complex-stably-frees`), including the proof paragraphs at lines 19390--19445 and 19517--19545 of the local source. The new node's statement is the general lemma's statement and its conclusion is exactly what the item step takes from it. In the item step, the finite stably free class is checked against the source's four auxiliary inputs: stably free modules are projective; projective short exact sequences split, giving closure; the quotient-surjectivity condition is Nakayama under the $1+I$ hypothesis; and finite stably free modules over $R/I$ lift by lifting a stable presentation and taking a kernel. The pseudo-coherence hypothesis is used in its stated bounded-above finite-free form, so those terms belong to the class. The free-term clause is the source's final assertion, obtained by choosing the free stable presentation when $E^i$ is free. I also checked edge cases $I=0$ and $E^\bullet=0$. The required Lean searches were run for the item and the new node: LeanFinder, Loogle, grep, and LeanSearch (unavailable) for the item; LeanFinder, Loogle, and grep for the new node.

## Not duplicates

- `lem-sc-complex-lift-class-projective` vs `lem-sc-pseudo-coherent-lift-stably-free-complex`: the new node is the abstract five-hypothesis projective-class theorem, while the item specializes it to finite stably free modules and adds the free-term clause.

## Second reading by H1

- Item statement: checked against More on Algebra, Lemma 15.75.6, Tag 0BCB, including the four hypotheses, the bounded-above finite stably-free conclusion, the derived reduction isomorphism, and the free-term assertion; verdict: agrees (the source's `K^\bullet` is read as its object `K`, as required by the surrounding statement and proof).
- New node `lem-sc-complex-lift-class-projective`: checked against More on Algebra, Lemma 15.75.2, label `lemma-lift-complex`, hypothesis by hypothesis; verdict: agrees with the general five-condition lemma and has no proof content.
- Item proof step 1: checked against the proof of Tag 0BCB and the cited general node statement; verdict: the application has the required class, closure, surjectivity, lifting, and bounded-above representative checks, and the conclusion is exactly the cited node's conclusion. The zero complex and `I=0` cases are consistent.
- New-node form: statement-only, self-contained ring/ideal/class/derived-complex data, TeX notation, source label, definition dependency, blueprint metadata, and recorded Lean searches; verdict: B1-B7 satisfied.
- Existing-node/Mathlib search: searched the DAG for the two lemma labels and for stably-free/projective complex lifting; no duplicate or exact Mathlib declaration was found. The recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results are retained.

Changes made: corrected the new node's `created.item` to this delivery item (it incorrectly named the downstream local-model item); expanded this second-reading record to identify the source labels, each hypothesis check, the cited statement, edge cases, node-form checks, and search results. No mathematical statement was changed.
