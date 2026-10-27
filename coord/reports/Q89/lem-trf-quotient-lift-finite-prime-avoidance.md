# Q89: lem-trf-quotient-lift-finite-prime-avoidance

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-quotient-lift-finite-prime-avoidance.json`: item split into five steps; no exact Mathlib match. All inherited search records retained, six fresh logged searches appended.
- `citations.json`: the one proof citation, in step 4, with a verbatim quotation from the existing prime-avoidance node.
- `report.md`: this report. `searches.jsonl` is the unmodified output log produced by msearch.py.

New nodes: 0. New Mathlib leaves: 0. The proof reuses the existing Mathlib leaf `lem-weil-pbc-prime-avoidance`.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, quotient/coset lifting with prime avoidance, `exists_representative_mod`, and `subset_union_prime`. The project has uses of ordinary prime avoidance, but no declaration found that proves this arbitrary-ring, prescribed-coset assertion. A Mathlib declaration is not a project attachment.

## Wanted sources

None. All sources used are present locally.

## Problems found and changes

The imported item had a complete, correct statement but no proof. Its statement and statement dependencies are unchanged. No repair note was present. The sandbox had no item or prior report; the item was copied from the live read clone. Its inherited six Mathlib search records and conclusions were read and preserved; the six searches in the current sandbox log are additional searches run for this delivery.

I read Stacks `varieties.tex`, Tag 09NK (`lemma-extra-silly`), statement and proof, lines 9060–9080, and its cited Algebra Tag 00DS (`algebra.tex`, `lemma-silly`, lines 2563–2594). Tag 09NK removes smaller primes, forms the ideal of allowed corrections, and applies ordinary prime avoidance once. The split gives those arguments explicitly. It uses the intersection $J=I\cap\bigcap_{i\in T}\mathfrak p_i$ in place of the source's product ideal: the same product witnesses belong to this intersection, and this form avoids introducing ideal multiplication as an additional notion. This is the same correction construction with every required containment justified, not a change of route or statement.

The latest blueprint ancestor statement and proof were read at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality{,.proof}.md`, as were the chapter and unit records. This algebra input belongs to the existing componentwise-affine-neighbourhood branch, not a replacement for the unit's contraction argument. The item retains its precise ancestor/from/via reference. Whole-DAG searches for 09NK and prime-avoidance concepts and whole-blueprint searches for `prime avoidance`, `quotient lift`, and `residue class` found no blueprint node giving the same assertion; `same_as` remains empty.

## Unfinished work

None for this one-level split. There are no new unsplit obligations.

## Not duplicates

No new nodes are created. The existing `lem-weil-pbc-prime-avoidance` is used directly, rather than duplicated. It chooses an element of an ideal; this item chooses an element of a prescribed coset and includes a separate correction construction.

## Review by Q89

I checked the item against Stacks Tag 09NK and all the form, citation, split and mathematical failure cases in delivery-errors B–E. No new nodes need source, definition, search, or duplicate audits. The existing statement defines ideals, primes and quotient cosets inline and uses `def-weil-affine-spectrum` only for its optional identification of primes with spectrum points. I opened that definition's statement; it indeed identifies the underlying points with prime ideals. No proof step needs scheme theory.

Step 1 is the source's removal of smaller primes, with termination justified by finiteness. It removes smaller, not larger, primes; avoiding a larger prime excludes membership in every smaller one. It chooses a representative by the definition of a coset. Repeated primes, the empty family and the zero ring are addressed here. There is no non-elementary citation in this step.

Step 2 separates indices according to whether the chosen representative lies in the prime. The intersection defining $J$ is an ideal directly by its closure properties. If there are no bad primes the chosen representative already works. This prevents applying a node stated for a nonempty family to an empty family. No non-elementary fact is used.

Step 3 proves every noncontainment needed in Step 4, rather than merely claiming that prime products have the property. For each bad prime choose one factor in $I$ outside it and one factor in each good prime outside it. Such factors exist because the ideal hypothesis persists and the retained distinct primes are incomparable. Their product lies in each required ideal by absorption and cannot lie in the bad prime by its defining implication. An empty product gives the same witness from $I$. This is an elementary few-line consequence of the definitions, not an extra lemma node.

Step 4 is the only non-elementary step. I opened `dag/nodes/sec-proper-base-change/lem-weil-pbc-prime-avoidance.json` and read its entire statement. It gives an element in an arbitrary ideal avoiding a nonempty finite list of ideals all but at most two of which are prime, assuming the ideal is contained in none of them. Here the ambient ring is still $A$, the ideal is precisely $J$, the family is the nonempty set $S$, all family members are prime, and Step 3 gives the noncontainments. Thus the cited statement supplies exactly $g\in J$ outside every bad prime. The quote in citations.json is copied verbatim, including the existing node's TeX. I also read its Mathlib realization `Ideal.subset_union_prime` at `Mathlib/RingTheory/Ideal/Operations.lean:1161` and the finite-set variant at line 1217. The existing node is already a Mathlib leaf, so this cross-unit citation is an allowed generic tool and does not require a new route approval.

Step 5 checks both clauses for $a+g$. Membership in $I$ fixes the quotient coset; for a bad prime subtraction of $a$ would contradict avoidance by $g$, and for a good prime subtraction of $g$ would contradict avoidance by $a$. These use only additive ideal closure and previous steps. There is no unproved compatibility or identification hidden in the conclusion.

I read the search hits, including the Dedekind representative theorem (Ideal/Lemmas.lean:963–979), pairwise-coprime CRT theorems (Ideal/Quotient/Operations.lean:255–272), and the essentially finite type quasi-finite lemma (QuasiFinite/Basic.lean:519–524). The first requires a Dedekind domain, the second coprimality not assumed here, and the last extra algebra hypotheses. Ordinary prime avoidance is the correct ingredient, not an exact match for the whole coset statement. Both semantic phrasings were tried and all new query texts agree with the msearch log; no outage was treated as absence.

I tested the reasoning on one prime; repeated primes; a comparable pair such as $(0)\subset(2)$ in $\mathbf Z$; the empty list; the zero ring; $I=A$; and $I=0$. For $I=0$ a nonempty prime family violates the hypothesis, so only the empty case applies. When $I=A$ the coset is unique and the construction still applies. In $\mathbf Z$ with $I=(5)$ and primes $(2),(3)$, it applies to every residue class, without assuming pairwise coprimality with $(0)$ or maximality in general rings. As a noncomaximal example, in $k[x,y]$ with primes $(x),(y)$, ideal $(x+y)$, and representative $0$, the product-witness argument still works. The statement does not require a field, Noetherianity, a domain, distinctness, incomparability in the original family, or comaximality. No correction to the statement or source is needed.

Every proof step is under 2000 characters (lengths 575, 489, 590, 309, 395); the only non-elementary fact is cited, proof_deps is exactly the union of uses, and the step-4 quote was checked against the cited statement. No new node repackages the conclusion or an elementary step. No SGA source, Lean write, compilation, local checker, or repository mutation was used.
