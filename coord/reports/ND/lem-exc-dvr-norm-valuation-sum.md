# Stage 1: lem-exc-dvr-norm-valuation-sum

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-dvr-norm-valuation-sum.json`: item, statement unchanged, six-step split.
- `dag/nodes/sec-smooth-purity/lem-exc-dvr-lattice-distance-determinant.json`: statement, unsplit, no Mathlib match. General relative-length/determinant theorem for an arbitrary lattice and linear automorphism, Stacks 02MI with 02MF/02MG.
- `dag/nodes/sec-smooth-purity/lem-exc-semilocal-restriction-length.json`: statement, unsplit, no Mathlib match. Stacks 02M0 for an arbitrary finite-length module over a semilocal algebra.
- `citations.json`: verbatim statement quotations for each step/node pair.
- `report.md`: this handoff.

Two new statement nodes, zero new definitions, zero Mathlib leaves. The new nodes have no proof, proof dependencies or proof sketch in their statements. Their only dependencies introduce the notions they use. Their blueprint ancestry includes the item followed by its full inherited via chain; same_as is empty after whole-blueprint searches.

## Attachments

None. Searches by exact blueprint tag and by norm/valuation, field norm, lattice/determinant and semilocal/length concepts in the read-only project sources found no completed project declaration stating the item or either new input. The item's absent lean_audit field did not supply an attachment candidate. Upstream master was treated only as reference material.

## Wanted sources

WANTED: none. All proof sources were read in the local Stacks TeX checkout; the tag-to-label mapping was checked in tags/tags.

## What was wrong or missing

The item had a complete true statement and an empty proof. I kept every hypothesis and the entire statement unchanged. In particular the field extension is arbitrary finite: neither separability nor normality, excellence or henselianity is introduced. The semilocal length theorem cannot be replaced by Mathlib's local restriction-of-scalars theorem without proving a localization decomposition. The determinant-index hits for integer lattices do not state the arbitrary-DVR relative-length theorem.

The blueprint's current main-20261015 first paragraph of lem-exc-dvr-galois.proof.md invokes the length calculation for a finite free integral closure. This item supplies its more general norm/order input. I read the chapter and sk-prop-a1-kummer unit records and retained their binding and the historical blueprint ancestry. This auxiliary node is not a unit key node, so no unit realization fields were due. No proof uses a forbidden source or changes the unit route. All existing cited statements outside the unit are definitions or Mathlib leaves; no extra tool use needs declaration.

The draft was checked to avoid assuming y belongs to B. The first server preflight rejected two phrases referring to the item; I replaced them with the explicit assumptions and normalized-valuation convention present in this node, without changing the mathematics. It uses the full lattice-distance form of 02MI for arbitrary nonzero y, and two modules B/(B intersect yB) and yB/(B intersect yB). This preserves negative valuations and makes the norm's determinant identification literal, without silently appealing to an uncited multiplicativity theorem. The localization-intersection argument and the two quotient identifications are spelled out in the item.

## Not duplicates

lem-exc-dvr-lattice-distance-determinant vs def-sc-rational-section-divisor: both source fields mention 02MD, but the latter defines rational sections and their divisors on smooth curves; it gives no finite-length comparison for two arbitrary lattices or determinant formula.

lem-exc-dvr-lattice-distance-determinant vs lem-exc-dvr-norm-valuation-sum: the new node compares two lattices in an arbitrary vector space under a linear automorphism; it has no extension algebra, maximal ideals, residue degrees, norm or weighted local sum. The item must prove the spanning, apply length restriction and compute each signed local contribution.

lem-exc-semilocal-restriction-length vs lem-exc-dvr-norm-valuation-sum: the new node concerns arbitrary finite-length B-modules over a local-to-semilocal ring map, with no fraction fields, DVRs, determinants, norms or chosen nonzero element. It supplies the restriction-of-scalars calculation, not a clause of the norm formula.

Whole-DAG tag searches found no existing 02M0, 02MI, 02MF or 02MG statement. Whole-DAG searches for the length/localization/residue-degree formula and lattice/determinant formula, whole-blueprint searches using blueprint_refs.py, and project-source declaration searches found no equal or stronger existing node. The existing DVR factorization, module length, exact localization and determinant definitions are reused, not recreated.

## Review by ND

I read Stacks algebra.tex, lemma-finite-extension-dim-1 (02MJ), including its proof, definition-ord (02MD), lemma-pushdown-module (02M0) with its simple-factor proof, lemma-compare-lattices (02MF), definition-distance (02MG) and lemma-order-vanishing-determinant (02MI) with its proof. I also read the current blueprint first paragraph quoted by the item's blueprint.from.place. The item is exactly the DVR specialization of 02MJ: order agrees with the normalized exponent by the ideal-chain computation in Step 5. There is no disputed source or statement correction.

For the lattice node I checked the hypotheses of 02MI: a DVR is a one-dimensional Noetherian local domain; M is finite and spans the finite-dimensional fraction-field vector space, and g is invertible. 02MF supplies the finiteness of both quotient lengths, 02MG supplies their signed difference, and 02MI supplies its determinant value. The statement introduces the lattice inline and defines normalized valuation inline. It is not an existence-only or hollow construction. For the semilocal node I checked 02M0 line by line: A local, B semilocal, every maximal ideal over the unique maximal ideal, finite residue extensions, and M finite length over B. No finite-module or Noetherian hypothesis on B is silently used in that lemma.

Step 1 cites the actual finite-generation and finite-dimensionality definitions. The K-span of B is a finite-dimensional subalgebra of a field; multiplication by a nonzero element is injective and hence onto, so it is a field and equals Frac(B)=L. This is the elementary finite-dimensional linear algebra argument, written in full. It supplies exactly the spanning hypothesis needed in Step 2 rather than assuming the fraction fields automatically make B a lattice.

Step 2 cites the new lattice-distance statement, which explicitly gives both finite lengths and the signed equality, and the existing endomorphism-determinant definition. I checked g is K-linear and has inverse multiplication by y^{-1}, and that H is a B-submodule of both factors. The norm in the item's statement is exactly det_K(g), so no comparison between distinct norms is asserted. Every hypothesis of the new lemma is present.

Step 3 cites the module-length definition for the chain inequality and the new semilocal-length statement for both finite sums. Its M must have finite B-length: each B-chain is an A-chain, so Step 2 proves this. The finite X, maximal contractions and finite residue degrees are explicit hypotheses of the item. Subtraction occurs only after finiteness, in integers. The quote in citations.json is the entire verbatim statement so a reader can see these hypotheses and its exact conclusion.

Step 4 cites the actual fraction definitions for ring/module localization and the Mathlib leaf saying localization preserves an exact module sequence. That node states middle exactness, so I separately wrote why the localized quotient map is surjective. Equality H_q=R intersect yR is proved with the displayed common denominator st, not taken from a definition or asserted as transport. The quotient identifications are R-linear and their kernels are exactly H_q.

Step 5 cites the DVR definition, the PID-to-Noetherian Mathlib leaf and the unit-times-uniformizer-power Mathlib leaf. I opened their statements: the latter requires a Noetherian local domain with nonzero principal maximal ideal, so the former two explicitly supply these conditions. Every ideal is principal by the DVR definition. I also wrote the numerator/denominator factorization of an arbitrary nonzero fraction and the cancellation argument proving exponent uniqueness; no separate fractional-factorization theorem is hidden in the normalized-valuation convention. The ideal lattice between (t^n) and R consists of the n+1 powers, which proves length R/(t^n)=n directly from the length definition. For negative r=-n the actual multiplication map by t^n identifies t^{-n}R/R with R/t^nR. Thus the difference is r in both signs, including r=0. This is an elementary consequence of the cited factorization, not a new lemma node. Step 6 is substitution into a finite sum and cites nothing further.

I checked the counterexample-sensitive small cases. For the item, B=A and y a unit gives 0=0; y=t^r gives r=r for every integer r. Over A=Z_(2), B=Z_(2)[i], y=1+i has norm 2, local exponent 1 and residue degree 1; its inverse gives -1. Over A=Z_(5), B=Z_(5)[i] there are two maximal ideals with residue degree 1. The element 2+i has norm 5 and local exponents 0 and 1; (2+i)/(2-i) has norm 1 and opposite local exponents, so the signed local sum cancels. None of these tests assumes a unique maximal ideal. For the lattice node V=0 gives determinant 1 and both quotients zero; rank-one g=t^r gives the indicated signed lengths; g=diag(t,t^{-1}) on R^2 gives equal nonzero lengths and determinant 1. For the semilocal node M=0 gives 0=0; B local gives the known restriction formula; B=k x k and M=k x 0 gives one local length 1 and one 0; a finite residue extension B/k of degree f with M=B gives length f. A zero B ring, if permitted, only has M=0 and the empty sum and is harmless.

I checked delivery-errors B1-B10: complete statement-only inputs, named notions or inline local/semilocal definitions, single-escaped mathematical TeX, exact tags and labels, actual logged searches, no unverified leaf claim, full blueprint records and no project attachment. Both semantic phrasings and all four tool types were run for both new inputs. One early Loogle query contained an unknown identifier; it is recorded as invalid/unavailable evidence and was replaced by a valid named Loogle query, rather than used as evidence of absence. I read the relevant hits in LocalRing/Length.lean, OrderOfVanishing/Basic.lean and FreeModule/Finite/CardQuotient.lean. The original item's inherited search records are preserved, and fresh item-specific norm searches were added.

I checked C1-C8 and D1-D5 against the node statements, not their proofs: the two non-elementary inputs are explicitly named, no definition stands in for a theorem, and the localized quotient argument uses exactly the exactness the existing leaf states. The two new nodes do not contain the weighted norm formula, are not elementary restatements, and have no dependency back on the item. The elementary spanning, intersection, ideal-chain and sign arguments stay in the item's steps. I checked E1-E7: no hidden normality, separability, localness of B or finite residue assumption is added, B_q rather than B is the local ring in Step 5, and fractions rather than ring elements are allowed throughout. No source error was found.

## Unfinished work

No part of this one-level split is intentionally unfinished. The two statement-only inputs are deliberately unsplit for later work, as required. No Lean was written or compiled. Delivery is reserved for the fresh second reader.

## Validation

The preliminary server check_dag and review_split requests were issued before writing this report. They reported a worktree-capacity queue. The mandatory deliver.py --no-push dry run is the final validation; its result is recorded after it completes.

## Second reading by ND

- Item statement: checked every hypothesis against Stacks Tag 02MJ, algebra.tex lemma-finite-extension-dim-1, and the exponent convention against Tags 02MD and 00PD; PASS, faithful DVR specialization, no separability, normality, henselianity or excellence used.
- Step 1: read def-weil-finitely-generated-module and def-weil-finite-dimensional-subspace; checked the finite-dimensional subalgebra argument in the field L and the spanning requirement of the lattice lemma; PASS.
- Step 2: read lem-exc-dvr-lattice-distance-determinant and def-weil-endomorphism-determinant against Stacks 02MI/02MF/02MG; checked the inverse multiplication map and both B-module structures; PASS.
- Step 3: read def-weil-pbc-module-length and lem-exc-semilocal-restriction-length against Stacks 02M0; checked finite B-length from A-chains, residue-field hypotheses, both applications and integer subtraction; PASS.
- Step 4: read the exact statements of def-weil-pbc-localization-at-prime, def-weil-pbc-module-localization, lem-weil-pbc-localization-module-exact and def-weil-pbc-module-length; checked common denominator st, surjectivity, quotient kernels and length preservation; FIX, made localization embeddings and Frac(B_q)=L explicit and wrote the submodule-chain justification of equal lengths.
- Step 5: read def-sc-discrete-valuation-ring, lem-weil-pbc-pid-noetherian-normal, lem-weil-pbc-dvr-unit-times-uniformizer-power and def-weil-pbc-module-length against 00PD/02MD; checked Noetherianity before factorization, all ideals above (t^n), fraction exponent uniqueness, and multiplication by t^n for negative exponents; PASS.
- Step 6: checked literal substitution from Steps 4-5 into Step 3, including both signs and zero exponents; PASS.
- New node lem-exc-dvr-lattice-distance-determinant: compared hypothesis by hypothesis with algebra.tex lemma-order-vanishing-determinant (02MI), lemma-compare-lattices (02MF), definition-distance (02MG), and definition-ord (02MD); PASS. Statement only, all notions defined inline or by actual definition nodes; not a norm-formula restatement or an elementary consequence of its cited definitions. Independent DAG/tag/whole-blueprint and project-declaration searches found no duplicate or attachment. Independent LeanFinder, LeanSearch, Loogle and source grep found no exact Mathlib leaf; read the actual local-length, Smith-quotient and integer-index hits.
- New node lem-exc-semilocal-restriction-length: compared hypothesis by hypothesis with algebra.tex lemma-pushdown-module (02M0); PASS. B/q agrees with the residue field at a maximal ideal, and no finite-module hypothesis on B is required. Statement only and self-contained; its composition-series/additivity content is not two or three lines from its definition dependencies. Independent DAG/tag/whole-blueprint and project-declaration searches found no duplicate or attachment. Independent LeanFinder, LeanSearch, Loogle and source grep found no exact Mathlib leaf; IsLocalRing.length_restrictScalars requires B itself local and does not state the semilocal sum.

Small cases checked independently: item B=A, y=t^r for arbitrary integer r, and a unit; two distinct primes above 5 in Z_(5)[i] with y=(2+i)/(2-i) give opposite valuations and norm 1. The lattice lemma gives 0=0 for V=0, signed exponent r in rank one, and equal nonzero lengths for diag(t,t^{-1}). The semilocal lemma gives 0 for M=0 (including zero B and the empty maximal spectrum), gives length f for a residue extension of degree f, and gives a single nonzero summand for B=k x k and M=k x 0. A field is excluded by the DVR definition, as required. No statement dispute or source error was found.

Changes: added the fraction-field and localization-embedding argument to Step 4 so Step 5 applies to y in L; added the image/inverse-image argument for preservation of module length and its definition citation; regenerated citations.json verbatim from each cited statement; appended the eight genuine independent search records to the two new nodes. Retained all statements, six proof steps, both useful new lemmas, the first worker's Review by ND, and the blueprint/unit route. The unrelated p-linear-filtration search hit concerns invariant-subspace determinants and is not a duplicate. Read coord/dag-sync.md and GOAL.md; no live files, Lean, compiler or build tools were used.

Second-reader validation: the mandatory deliver.py ND lem-exc-dvr-norm-valuation-sum --no-push completed with `OK (not pushed) deliver/ND/lem-exc-dvr-norm-valuation-sum at c5f279d53a: preflight passed`. The server preflight includes check_dag.py and review_split.py; none was run on this machine.
