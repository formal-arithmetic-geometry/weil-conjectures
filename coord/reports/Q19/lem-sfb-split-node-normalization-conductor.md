# Q19 stage-1 report

Item: lem-sfb-split-node-normalization-conductor. Date: 2026-10-23.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-node-normalization-conductor.json: split item, nine proof steps; full statement retained; no full Mathlib match.
- citations.json: fifteen entries quoting the statements of all nodes cited by the nine steps.
- searches.jsonl: actual searches recorded by the prescribed msearch.py command.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Every supporting result was found in the existing DAG. There is no need to turn the explicit conductor calculation into another node.

## Attachments

None. Searched the current lean/WeilConjectures source for the exact blueprint id and for conductor, split-node and normalization terminology. The conductor files found concern finite integral extensions, sections on component covers, and conductor ideal intersection, not the explicit nodal polynomial algebra and all clauses of this item. No project declaration states the item exactly. Mathlib relative normalization is also not a project attachment.

## WANTED

None. All sources used are present in literature/stacks-project. No SGA source is used.

## Problems found and corrected

The imported item had a statement, empty proof and searches, but no completed split. Its statement is true as written; no STATEMENT-DISPUTED correction is needed. In particular finiteness is asserted only for the explicit split-node normalization, not for arbitrary reduced Noetherian normalization. A DVR need not be excellent here. Its two branches need not be irreducible components of the special fibre of another ambient scheme: they are exactly the reduced components of this explicitly specified affine scheme.

The original normalization/conductor searches have been preserved. The fresh searches used two formulations of the item, as well as the PID supporting-fact search. LeanSearch returned integral-closure instances; Loogle returned integral-closure comparison under localization and smooth extension; LeanFinder returned Kummer-Dedekind conductor results and unrelated normalization terminology. None states this item. I read the relevant local Mathlib declarations in AlgebraicGeometry/Normalization.lean and RingTheory/Smooth/IntegralClosure.lean, and the polynomial normality instance in RingTheory/Polynomial/IsIntegral.lean. The PID search did find the known Mathlib result, and the subsequent DAG search found its existing leaf lem-weil-pbc-pid-noetherian-normal, which is cited rather than duplicated. The zero-hit grep in PrincipalIdealDomain.lean is not treated as absence: the result lives through DedekindDomain/Basic and Polynomial/RationalRoot.

I read the chapter and unit records, SETUP.md's three levels, GOAL.md, the worker/stage rules, and both copies of delivery-errors.md B--E. I read the current blueprint under literature/blueprint/latest, specifically sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The latter's paragraph (3) concerns direct-image preservation and compactification; the inherited auxiliary normalization chain serves that route and is not a verbatim theorem of that paragraph. I preserve the existing blueprint ancestry and spell this out in split_report.blueprint. Blueprint searches for normalization, conductor, split node, integral closure, principal ideal and integrally closed found no equivalent blueprint theorem for this full item.

## Not duplicates

No new node was created. Existing lem-per-componentwise-normalization-affine-charts supplies the scheme formula, lem-weil-pbc-integral-closure-commutes-localization supplies the ring restriction, and lem-weil-pbc-polynomial-ring-normal-domain supplies normality of the branches. The conductor and fibre-product conclusions remain proved directly in this item; they are not delegated to restated clauses.

## Review by Q19

For the general affine formula I read morphisms.tex Tag 035P, label lemma-description-normalization, in full, and Tag 0CDV, label lemma-normalization-in-terms-of-components. For localization I read morphisms.tex Tag 035K, label lemma-normalization-localization, and algebra.tex Tag 0307, label lemma-integral-closure-localize, including its denominator argument. For the base and polynomial normality I read algebra.tex Tag 00GZ, label lemma-PID-normal, and Tag 030A, label lemma-polynomial-domain-normal, including their proofs. I read models.tex Tag 0CDD, label lemma-etale-local-at-worst-nodal, for the exact uv=0 local model, rather than claiming that tag itself states the conductor square. The conductor calculation is explicitly agent-written. For smoothness I read algebra.tex Tag 00T7, label lemma-standard-smooth, with the zero-equation polynomial presentation. There are no new nodes needing separate sources.

Step 1 uses the statements of def-pc-reduced-scheme and pqf-def-locnoeth only to check that Spec T satisfies the hypotheses of lem-per-componentwise-normalization-affine-charts. I read that node's full statement: it gives the product of the component integral closures and the exact structural map, including the empty case, so this is a legitimate citation rather than borrowing from its proof. Its locally Noetherian hypothesis follows from the single affine chart T, whose Noetherianity is assumed.

Step 2 uses only def-weil-pbc-integral-closure, whose statement gives the monic-equation characterization. The finite product of lifted monic equations explicitly proves the coordinatewise integrality assertion. This avoids silently treating the affine chart node's source reference as if its statement included every ring-theoretic claim. For the zero ring, the sole element satisfies Z=0.

Step 3 uses exactly clause (2) of lem-per-componentwise-normalization-properties: restriction to any open is its componentwise normalization. I read the statement and do not rely on its generic-point or recognition clauses. The localization node states that the image of the localized closure is the integral closure after localization, for an arbitrary ring homomorphism and multiplicative set. Apply it to T into the finite product of its component fields and powers of s; this includes a component being killed by s=0. The restriction maps are the canonical fraction maps. In a normal domain the only component closure is the ring itself, so the formula from step 1 is the identity; no extra assumption of excellence or completeness enters.

Step 4 cites the polynomial-ring definition for coefficient expansions. Every mixed monomial is explicitly killed by uv, the kernel is proved by the two evaluations, and a matching pair is represented by f(u)+g(v)-c. Thus the proof establishes the claimed subring, rather than appealing to an unprovided node stating the whole clause.

Step 5 is a direct module-generation and monic-equation argument. For an arbitrary pair, subtract its constant-coefficient difference in the first factor to obtain q in Q, leaving de. Since d is a diagonal constant, 1 and e generate as a Q-module. The equation for q+de verifies integrality separately; the proof uses no uncited finite-algebra theorem.

Step 6 uses the full PID node statement for normality of R; fields have only the ideals (0) and (1), and the supplied DVR definition is a local nonfield PID. The polynomial normality node applies over either resulting normal domain. The prime calculation is explicit: uv=0 forces one coordinate into every prime, and the two coordinate ideals are incomparable prime ideals because their quotients are polynomial domains. The cited Spec-components node gives precisely the correspondence with minimal primes. I read def-sc-normalization and def-weil-pbc-reduced-normalization: their constructions give the identity on these already integrally closed component domains and then the disjoint union. Localizing the already established integral-closure identity also gives the sheaf identity on their principal opens. The finite-affine-coproduct node explicitly identifies that disjoint union with Spec E and identifies each coprojection with the ring projection. This does not require first proving Q Noetherian or citing a hidden Hilbert-basis argument; the definition of componentwise normalization itself applies to schemes generally.

Step 7 proves both inclusions of the conductor. Testing multiplication by e forces the common constant to vanish, and vanishing constants suffice against every pair in E. The displayed Q-linear combination verifies equality with (u,v), including the availability of the coefficient pairs in Q. Since it is already an E-ideal its extension is itself; the quotient maps are explicitly the constant-evaluation maps, and their induced inclusion is diagonal. No cancellation of a nonunit or unproved flatness assertion is used.

Step 8 writes the actual inverse of the canonical fibre-product map. Its equality condition is f(0)=r=g(0), and the polynomial f(u)+g(v)-r is exactly the preimage constructed in step 4. Injectivity into E checks the multiplicative and additive identities and uniqueness. This is the ring fibre product in the statement, not a scheme fibre product confused with its contravariant diagram.

Step 9 cites def-sbc-affine-space for its explicit affine description in dimensions 1 and 0, and sbc-lem-affine-space-smooth for smoothness of its projection. I read both complete statements; the latter really asserts smoothness in the recorded convention. The origins have coordinate rings R[u]/(u)=R and R[v]/(v)=R, which are reduced because R is a domain. Their structural maps, not their inclusions into the branches, are asserted smooth.

I checked B--E against the actual delivery: statements are self-contained with single-escaped TeX, no new statement-only nodes are disguised proofs, no elementary facts were inflated into nodes, and no clause is transferred into a new node. All non-elementary steps cite the statements they use; citations.json quotes verbatim text from those statements. Generic off-unit tools are declared in split_report.tool_uses, without modifying the maintainer's tool_uses. The combined statement/proof dependency traversal of each principal supporting node does not reach this item, so these citations add no cycle. Every step has fewer than 2000 characters; the longest is the component argument in step 6 (1009 characters), and it is not hiding a new comparison theorem.

Small cases checked: T=0 and the empty component product; T a field, a normal domain, or a reducible domain-product; s=0 or s=1 for restriction; R a field including characteristic 2; and R a nonexcellent DVR. The idempotent calculation does not divide by 2. Constant pairs and pairs (u,0), (0,v) give the predicted quotient and conductor; e itself is not in Q because 1 is not 0 in a field or DVR. All hypotheses of every cited result have been verified above. No source error or statement change remains.

## Unfinished work

None in the requested one-level stage-1 split. Existing unsplit dependencies remain separate queue items. Required server preflight and push results will follow from deliver.py.
