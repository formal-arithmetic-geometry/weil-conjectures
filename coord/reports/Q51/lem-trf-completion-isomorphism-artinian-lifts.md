## Files written

- `dag/nodes/sec-trace-formula/lem-trf-completion-isomorphism-artinian-lifts.json`: statement; split into five steps; not an exact Mathlib statement. Its statement, statement dependencies, inherited searches and blueprint ancestry are retained. Five actual search records from this session are appended.
- `citations.json`: one verbatim statement quote for each step/node citation (four entries).
- `report.md`: this report. Search output files and `searches.jsonl` retain the real search results.

New nodes: 0. New Mathlib leaves: 0. The existing Mathlib leaf `lem-weil-pbc-artinian-local-noetherian-nilpotent` is reused.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint tag, completion/Artinian combinations, completed lifts and related terminology. No declaration gives all the item's clauses. The completed matching-ring residue lift has different objects and only a residue-level conclusion, so it cannot attach here. No compiler, Lake or Lean-writing tool was used.

## WANTED

None. The relevant Stacks sources are present. The algebraic argument is supplied explicitly and marked `proof_origin.by = agent`, because Tag 0CAV invokes the smoothness criterion but does not spell out this Artinian completion calculation.

## Problems and corrections

The imported item has a valid statement and no proof. No statement correction, STATEMENT-DISPUTED, or route change is needed. The source already correctly says that this is an algebraic sublemma implicit in Tag 0CAV, not a verbatim assertion of that tag.

I avoided two possible gaps: equality of maps on A alone is not offered as proof of equality on its completion, and locality of the inverse completion map is not assumed without a theorem. Step 3 instead computes both maps at the same finite coordinate. Step 5 proves locality from the surjection q and the equality qc=b. The proof does not require completion to be Noetherian or the kernel of a coordinate projection to equal an extended ideal. To prove annihilation, containment in that kernel is enough and is checked on ideal generators.

## Not duplicates

No new nodes are proposed, so there are no new/existing pairs to justify. Before deciding this I searched the full DAG by Artinian, nilpotent maximal ideal, completion quotient and completion-local-map concepts, and read the potentially relevant statements. The existing Artinian nilpotence node supplies exactly step 1. The full-blueprint searches `completion`, `Artinian completion`, and `nilpotent maximal` found no blueprint node stating this Artinian lifting diagram, so the item's `same_as` remains empty. The completion definition is reused rather than duplicated; the stronger completion quotient and locality lemmas are unnecessary.

## Review by Q51

I read Stacks `more-morphisms.tex`, Tag 0CAV (`lemma-isomorphism-approximation`), including the first proof paragraph where an isomorphism of completed stalks is used to invoke Artinian smoothness. I also read Algebra Section 00M9's compatible-sequence construction, Tag 00J8 (`lemma-artinian-radical-nilpotent`) with its proof, and Tag 05GG to check whether a completion-kernel theorem was really needed; it is not. For context I read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof, together with the chapter and unit records. This is a lower algebraic tool on the inherited nodal-model chain, not a new replacement for the chapter's contracting-correspondence argument.

Step 1 cites `lem-weil-pbc-artinian-local-noetherian-nilpotent`. I opened its statement: it explicitly supplies a positive nilpotence exponent for the maximal ideal of every Artinian local ring. Both targets C' and C satisfy those hypotheses. Locality of a and b, already in the item, sends each factor of a product in a source maximal ideal into the corresponding target maximal ideal; finite sums of products are therefore killed at the stated powers. Writing the two quotient maps on classes proves their well-definedness and the factorizations. I do not cite the definition of Noetherianity for nilpotence.

Step 2 cites `def-weil-pbc-adic-completion`, whose statement explicitly defines compatible quotient sequences with componentwise operations and the canonical map. These are exactly the data used. I wrote out the restriction identities and the generators of the extended ideal power; no equality between an entire projection kernel and that ideal is needed. This calculation is elementary, as recorded.

Step 3 cites the same definition. Its compatible-sequence clause gives reduction from coordinate t=max(r,s) to both relevant coordinates. A coordinate is an actual quotient class and hence has a representative x in A. The item's hypothesis that h is coordinatewise induced by phi gives its s-th coordinate directly. The three equalities qa(x)=b(phi(x)), ahat(z)=a(x), and bhat(h(z))=b(phi(x)) establish the asserted equality of completed maps, even when r and s differ. Thus this step uses the statement of the cited definition, not a construction hidden in another node's proof.

Step 4 again cites the completion definition for coordinatewise equality hi_A=i_B phi. It then substitutes the actual inverse ring isomorphism h^{-1}; the two displayed compositions prove each required lifting identity. Step 5 has no cited node: surjectivity of q makes C'/q^{-1}(m_C) the nonzero field C/m_C, so the kernel is maximal and must be the unique maximal ideal of C'. Taking inverse images in qc=b proves locality in one line. This is elementary quotient-ring algebra, not an unstated smoothness or completion-locality theorem.

I checked the edge cases where A and B are fields (positive exponent 1), q is the identity, r=s=1, and independently chosen r<s or r>s. The common-coordinate argument handles all of them. As a concrete nontrivial check, take A=k[t]_(t), B=k[[t]], a(t)=epsilon in C'=k[epsilon]/(epsilon^3), C=k[epsilon]/(epsilon^2), and b(t)=epsilon: the construction is truncated evaluation, with r=3 and s=2, and yields the required lift. The zero-ring cases are excluded by the statement, ensuring the residue-field maximal-ideal argument is valid.

Against delivery-errors B-E: there are no statement-only new nodes, new definitions, imported proof fragments or Mathlib leaves to validate. All existing source/search/blueprint metadata is retained, all new search queries actually ran through msearch.py, and their complete outputs are saved. I inspected the completion universal-property candidates in Mathlib/RingTheory/AdicCompletion/Algebra.lean and RingHom.lean: these construct maps into a completion or complete target from compatible quotients, and are not a one-line instance of this entire lifting statement. The second semantic phrasing returned the formally smooth lifting theorem, which requires a hypothesis unavailable here and also has a different conclusion. The existing nilpotence leaf's HopkinsLevitzki declaration was read. All non-elementary input is in a cited node, every cited statement was read, and the four citation quotes are verbatim. No proof step exceeds 2000 characters (the longest is below 700); no clause is moved into a new node and no cycle is introduced (both proof dependencies are existing leaves). No SGA source is cited.

## Unfinished work

None in the mathematical split. Server dry-run and direct delivery results are recorded below after the commands complete.
