# Stage 1 report

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-complex-lift-acyclic-projective.json`, statement, split, no Mathlib match.

2. Attachments: none. No declaration tagged `lem-sc-complex-lift-acyclic-projective` or matching Tag 0BC9 was found under `WeilConjectures/`.

3. WANTED: none. The local Stacks source used for checking is `/home/ubuntu/c1-stacks-review/more-algebra.tex`, at the source named in the node.

4. The item follows More on Algebra, Lemma 15.75.1, Tag 0BC9. I found no duplicate node: the existing `lem-sc-complex-lift-class-projective` uses this item as its acyclic lifting input but states the derived lifting theorem, not the acyclic-complex construction. No new node was needed: the split-tail decomposition, projective lift, and descending induction are the proof steps themselves.

## Review by J1

I read the complete Tag 0BC9 statement and proof. Step 1 checks the bounded-above cutoff, the acyclic tail invariant, the decomposition into consecutive cycle modules, and membership of those summands in the class using the direct-summand hypothesis. Step 2 checks that the chosen preceding term has the prescribed quotient, that exactness identifies the image with the next cycle quotient, and that projectivity supplies the lift while hypothesis (3) makes it surjective. Step 3 checks that descending extension defines the whole bounded-above complex, preserves the quotient isomorphism, and establishes exactness degree by degree. There are no cited DAG statements, so `citations.json` is empty; every step is marked elementary because it is the explicit split-and-lift construction from the three hypotheses and the two complex definitions. I checked the edge cases `I=0`, the zero complex, and a complex concentrated in one degree; each reduces to the stated construction.

5. Nothing remains unfinished.

## Second reading by J1

- Item statement: checked hypothesis by hypothesis against More on Algebra, Lemma 15.75.1, Tag 0BC9; the ring, ideal, class conditions, bounded-above acyclic complex, termwise $P/IP$ form, and lifted conclusion agree.
- Step 1: checked against the proof's split-tail construction in Tag 0BC9; the bounded cutoff, cycle decomposition, differential, and downward use of the direct-summand condition are present. No external DAG fact is used.
- Step 2: checked against Tag 0BC9's lifting paragraph; projectivity gives the lift to the cycle module, exactness identifies its reduction with the cycle image, and condition (3) gives surjectivity. No external DAG fact is used.
- Step 3: checked against the final induction in Tag 0BC9; the descending construction yields one bounded-above complex, preserves the termwise reduction isomorphisms, and establishes exactness in every degree. No external DAG fact is used.
- New nodes: none; therefore B1--B7 and duplicate-node checks are vacuous. The Mathlib searches recorded by the worker were re-read and match the absence of an exact theorem.
- Small cases checked: the zero ideal, the zero complex, a one-term complex, and $I=R$ all reduce consistently to the stated construction.
- Changes made: corrected `created.item` to this item so delivery ownership passes; replaced the mismatched sheaf-level cochain/acyclic citations with a self-contained plain-module cochain and acyclicity definition, and cited the existing projective-module definition for the projectivity notion.
