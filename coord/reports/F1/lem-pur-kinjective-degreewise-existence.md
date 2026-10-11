# Stage 1 report: lem-pur-kinjective-degreewise-existence

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-degreewise-existence.json`: repaired item split.
- New statement nodes: `lem-pur-kinjective-functorial-homotopies`, `lem-pur-kinjective-functorial-injective`, `lem-pur-kinjective-characterize-injective`, `prop-pur-kinjective-objects-small`, `lem-pur-kinjective-characterize-K-injective`, `lem-pur-kinjective-acyclic-quotient-complexes-bounded-size`, and `lem-pur-kinjective-set-iso-classes-bounded-size`; all unsplit and no Mathlib leaves.
- `citations.json`: verbatim citations for every node used by every proof step.

## Attachments

None. The sorry-free generic replacement declarations in `WeilConjectures/CategoryTheory/GrothendieckAbelian/KInjectiveResolution.lean` do not state that every term is injective, so they are not exact attachments for this item.

## WANTED

None.

## What was wrong and what changed

The prior criterion node used undefined cardinality and transfinite-generation language. It now states the two precise 079P hypotheses: every nonzero acyclic complex contains a nonzero bounded-above acyclic subcomplex with term sizes bounded by kappa, and every acyclic complex is a quotient of a direct sum of such complexes. Object size is explicitly defined as the cardinality of the set of subobjects. I added the missing statement-only nodes for existence of kappa and for the set of isomorphism classes, strengthened the smallness proposition to identify `|M|` with this size, and removed those lemmas from `stmt_deps` while retaining them in `proof_deps`. The report no longer lists the nonexistent transfinite node or the out-of-scope unit file.

## Not duplicates

- `lem-pur-kinjective-functorial-homotopies` vs `lem-weil-pbc-kinjective-functorial-existence`: the existing node asserts a K-injective replacement but not a functor killing a specified set of bounded-above acyclic maps by homotopy.
- `lem-pur-kinjective-functorial-injective` vs `lem-weil-pbc-kinjective-functorial-existence`: the existing node omits factorization through injective subobjects in each degree.
- `lem-pur-kinjective-characterize-K-injective` vs `lem-weil-pbc-kinjective-functorial-existence`: a bounded-size criterion is distinct from replacement existence.
- `prop-pur-kinjective-objects-small` vs `lem-weil-pbc-kinjective-functorial-existence`: transfinite smallness is not a K-injective replacement statement.

## Review by F1

I read `literature/stacks-project/injectives.tex` at Theorem 079P and each cited lemma or proposition: `lemma-functorial-homotopies`, `lemma-functorial-injective`, `lemma-characterize-injective`, `proposition-objects-are-small`, `lemma-acyclic-quotient-complexes-bounded-size`, `lemma-set-iso-classes-bounded-size`, and `lemma-characterize-K-injective`. I also read the Lean source declaration region in `WeilConjectures/CategoryTheory/GrothendieckAbelian/KInjectiveResolution.lean` to confirm there is no exact sorry-free attachment.

Step 1 uses the M statement's termwise monomorphic quasi-isomorphism and null-homotopy clause. Step 2 uses N's corresponding quasi-isomorphism and injective-subobject factorization. Step 3 uses the generator lifting criterion and the smallness factorization proposition; its hypotheses include the Grothendieck category and the generator. Step 4 uses the corrected K-injective criterion with its two explicit bounded-size hypotheses, injective terms, and vanishing homotopy maps. Step 5 uses the two new existence statements to choose kappa and representatives, then uses M, N, smallness, and both criteria. I checked that subobjects of the generator have size at most the generator's size by the size definition, and that termwise factorizations assemble at one earlier stage because there are countably many degrees, the chosen cofinality is uncountable, and transition maps are monomorphisms. I tested zero and one-degree injective complexes as edge cases and recorded verbatim quotes in `citations.json`.

## Second reading by F1

- Item and steps checked against Theorem 079P and each cited lemma; restored the required termwise monomorphism and verified all hypotheses.
- New nodes checked against their Stacks labels; corrected the overstrong complex-class node to the actual object-class lemma and added missing definition dependencies.
- Changes: corrected the item, node statement, citation quote, and dependencies; zero and one-degree edge cases checked.
