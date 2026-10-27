# Q149: lem-sfb-adic-complete-subideal

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adic-complete-subideal.json: statement, split; statement unchanged; no exact Mathlib match. Four steps, total 1739 characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-adic-surjectivity-from-principal-generators.json: one new statement-only lemma, unsplit; Stacks 090S, specialized to the ring as its own module. No Mathlib match.
- citations.json: a verbatim statement quote for each of the five step/node citations.
- searches.jsonl: actual msearch.py results, read before recording verdicts.
- report.md: this report and signed self-review.

## Attachments

None. Searched WeilConjectures for the item tag, subideal and adic-completeness notions, and for the new generator-surjectivity assertion. Read WeilConjectures/RingTheory/CompleteLocalSubideal.lean in full. Its IsAdicComplete.of_le_maximalIdeal requires a Noetherian local ring, whereas this item allows an arbitrary commutative ring and an arbitrary larger ideal. It cannot attach this item. Other principal precompleteness declarations concern p-adic integers, products or ring equivalences; none assembles finitely many generators.

## WANTED

None: the Stacks sources used are present.

## Corrections and scope

The imported item was statement-only and correct against Stacks 090T. I retained the statement and existing metadata and added its proof. There is no statement dispute. The source's symbolic convergent tail was replaced by explicit finite-sum congruences; no closedness theorem for finitely generated ideals in the K-adic topology is assumed. No local, Noetherian, regular-element or finite-generation hypothesis on K was added.

Read the chapter and unit records, the latest blueprint unit sk-thm-sf-ctf-stability and its direct-images.proof.md, especially (3). This is supporting commutative algebra within the inherited deformation-completion chain, via lem-sfb-two-ideal-adic-completeness; it does not change the geometric route. blueprint_refs.py ancestor returns None for this inherited chain; retained from.node = null and extended the precise inherited from.place for the new node. same_as is empty after whole-blueprint searches.

## Not duplicates

lem-sfb-adic-surjectivity-from-principal-generators vs lem-sfb-adic-complete-subideal: the new node asserts surjectivity for a finitely generated ideal from surjectivity for each principal generator, with no larger ideal and no completeness or separatedness hypothesis. It does not transfer completeness to any subideal. The item must prove principal surjectivity using K-completeness and must prove injectivity separately.

lem-sfb-adic-surjectivity-from-principal-generators vs lem-sbc-complete-local-subideal: the existing node transfers maximal-ideal completeness to a subideal in a Noetherian local ring. It gives no principal-generator surjectivity criterion for arbitrary rings and cannot cover the new statement.

Whole-DAG searches for 090S and lemma-when-surjective-to-completion found no existing node. Searches for principal/generator surjectivity and adic completion found no statement generalizing the new node. Whole-blueprint searches for 090S, precomplete, principal completion, surjectivity completion and finitely generated ideal found no equivalent node; read the six keyword candidates returned by the last search as statements (all are unrelated coefficient data, derived completion or tangent space). The latest blueprint contains no occurrence of 090S or its Stacks label. No existing source field has the new node's tag.

## Review by Q149

I read coord/delivery-errors.md B through E, including the repeated merged checklist, and checked the actual node statements and the source rather than relying on citation labels.

For the item I read algebra.tex, lemma-complete-by-sub (Tag 090T), including its principal-case proof and its use of lemma-when-surjective-to-completion. For the new node I read that preceding lemma and its proof (Tag 090S, confirmed in tags/tags). The new statement specializes M=A and explicitly writes its canonical compatible-sequence maps. Its statement contains no proof, proof dependencies or hidden ambient assumptions. The source permits arbitrary modules and hence certainly arbitrary rings in this specialization.

Step 1 uses def-weil-pbc-adically-complete-ring. I opened that node: its statement defines completeness by bijectivity of the canonical compatible-family map and explicitly includes intersection of all ideal powers equal to zero. This supplies precisely the separatedness used. Power containment L^n subset K^n gives injectivity in two lines.

Step 2 uses the same definition, now its surjectivity clause. Arbitrary representatives of a principal compatible family have consecutive differences in f^n A; telescoping places all later differences in K^n because f lies in K. Thus the family modulo K^n is actually compatible, and completeness produces x with the claimed congruences. The b_n are just a_n-x. No completeness equivalence for general topological Cauchy sequences is silently invoked.

Step 3 uses that definition for a second explicit compatible family, the finite tail sums s_c. Since f lies in K, s_d-s_c belongs to K^c for d at least c, so completeness gives y_n with y_n-s_c in K^c. I checked the indices and signs: f^n s_c=b_n-b_{n+c}, so b_n-f^n y_n=b_{n+c}+f^n(s_c-y_n) lies in K^{n+c}. Separatedness gives equality. This is the actual principal-case argument of 090T, marked non-elementary and retained in the item rather than outsourced to a restatement. It uses no lemma beyond the cited definition: convergence and multiplication of infinite sums are both replaced by these finite congruences.

Step 4 uses lem-sfb-adic-surjectivity-from-principal-generators and the completeness definition. I re-opened the new statement and verified that it gives exactly the canonical map's surjectivity from the principal maps, without requiring them to be injective. Each generator lies in L subset K, so steps 2–3 discharge all its hypotheses. Step 1 supplies injectivity; the definition then gives the required completeness. The one new node is a genuine finite-generator assembly input (090S), not the item or its principal-completeness clause.

For future work on the unsplit 090S node, the source's argument is: use the cofinal ideals J_n=(f_1^n,...,f_r^n), with I^{rn} subset J_n subset I^n for r>0, lift a compatible family to representatives b_n with b_{n+1}-b_n in J_n, write these differences as sums of f_i^n z_{n,i}, and lift each grouped principal series by the assumed principal surjectivity. Their finite sum together with b_1 lifts the original family. This proof guidance remains here, outside the statement-only node. For r=0 the canonical map is the identity of A.

Small cases checked: L=0 gives the identity completion; the empty generator set makes the new node's hypothesis vacuous and conclusion the identity map; a single zero generator works because all sufficiently indexed quotients are A; nilpotent f makes the tail finite; zero divisors do not require cancellation; L=K recovers the assumed completeness when K is finitely generated. If K=A, K-completeness forces A=0, so this degenerate case is also correct. For the new node I also checked a unit generator: the relevant principal target is zero and I=A, whose completion target is zero, so surjectivity holds. No nonzero-ring assumption was introduced.

All new Mathlib searches were actually run with msearch.py under this group/item. I read their hits and the candidate source: Basic.lean:555 and 627–645 concern Cauchy-family surjectivity or the definition of precompleteness; Completeness.lean:185 is completeness of a completion; LocalRing.lean:61–63 changes scalars on that completion; Functoriality.lean:437–443 assumes one fixed ideal throughout; Exactness.lean:72 preserves surjections under completion. None supplies a finite-generator criterion or smaller-ideal completeness. Two semantic phrasings were run for each assertion. Loogle returned three completion-of-completion hits for the item and zero for IsPrecomplete, Ideal.span. No unavailable service was recorded as no match.

B: the new node is self-contained, uses the existing completion definition, has a checked Stacks tag, source location and blueprint provenance, and carries only a statement. C: every use is quoted verbatim in citations.json and proof_deps is exactly the union of uses. D: the principal and separatedness arguments remain in the item; only the independent generator criterion is a node. E: all ideal containments, quotient maps, indices and degenerate cases were checked above. All four steps are shorter than 2000 characters, so there is no long-step extraction issue. No SGA source, Lean edit, compiler, Lake or build tool was used. All writes are in the sandbox.

## Unfinished work

None for this stage-1 item. The new 090S node is deliberately statement-only for a later stage-1 worker, as required by one-level splitting. Delivery validation and push are performed with the mandated deliver.py commands.
