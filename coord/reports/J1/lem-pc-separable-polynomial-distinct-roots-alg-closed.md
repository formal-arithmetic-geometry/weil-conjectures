1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-separable-polynomial-distinct-roots-alg-closed.json`: split statement; no single Mathlib declaration for the combined claim.
- `dag/nodes/sec-picard-framework/lem-pc-separable-polynomial-rootset-card.json`: statement, Mathlib leaf `Polynomial.card_rootSet_eq_natDegree`.
- `dag/nodes/sec-picard-framework/lem-pc-separable-polynomial-nodup-roots.json`: statement, Mathlib leaf `Polynomial.nodup_roots`.
- `citations.json`: verbatim step citations.

2. Attachments: none.

3. WANTED: the local checkout does not contain the Stacks source tex files; the item and child sources follow the imported Stacks tags 00U3 and 09H1 recorded in the node files.

4. The imported item had no proof. I checked the whole DAG and blueprint for duplicate statements, found and reused `lem-weil-alg-closed-linear-factorization`, and searched Mathlib before creating both children. The item proof now explicitly maps the Bezout identity, invokes algebraically closed factorization, removes multiplicities using the nodup leaf, counts roots using the root-set-cardinality leaf, and uses monicity to set the leading coefficient to one. The new nodes are statement-only Mathlib leaves as required.

## Review by J1

I read the imported item, its `sk-thm-picard-rr` unit, and the existing factorization node. The Stacks 00U3 route is reflected in four steps. Step 1 uses the separability definition exactly for the transported Bezout identity, the algebraic-closure hypothesis, and the existing factorization statement; those statements provide the claimed inputs. Step 2 uses the new nodup statement, which says precisely that the roots of a separable polynomial occur without repetition. Step 3 uses the new root-set-cardinality statement, whose hypotheses match the field, separability, and algebraically closed extension and whose conclusion gives the degree count. Step 4 uses those same three statements only for monic normalization and reindexing, which is elementary once their conclusions are available. I tested the edge cases $n=0$ (the monic constant polynomial has empty root set and empty product) and $n=1$ (the quotient factor is one linear factor). All new node statements are self-contained, TeX-escaped, and carry the required blueprint ancestry and Mathlib search records; no Lean declaration in slopmaster2 states the item.
