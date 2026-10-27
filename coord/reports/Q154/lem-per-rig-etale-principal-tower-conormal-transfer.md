# Q154 stage-1 delivery

Item: lem-per-rig-etale-principal-tower-conormal-transfer.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-rig-etale-principal-tower-conormal-transfer.json — statement; split in eleven steps, unchanged statement, no Mathlib match.
- citations.json — one entry for each of the 21 step/node citations, copying the cited statement verbatim.
- report.md — this review and handoff. Searches and their returned output are retained in searches.jsonl and search-result-*.txt; write_split.py is sandbox-only preparation.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag and for completed conormal/cotangent, completedPolynomial, rigJacobian and rigEtale found no declaration stating this item. The project contains ordinary conormal results, but these do not prove the completed-presentation and uniform-truncation clauses.

## WANTED

None. All necessary source text is in literature/stacks-project. I read GOAL.md, the worker contract, stage 1, SETUP's three levels, delivery-errors B–E (including the repeated entries), the chapter and unit records, and the latest blueprint ancestor's proof. No Lean was written or compiler invoked. No repository or launcher file was modified.

## What needed repair

The imported item was unsplit, with no proof. Its mathematical statement is correct and is retained verbatim. In particular clause (ii) requires a single exponent measured in the original H, before varying L and H_0; the existing lem-per-jacobian-torsion-closed-base-change states only an exponent for a fixed quotient and measured in H_0, so citing its statement would not supply this uniformity. I read its proof as source material but do not use its unstated stronger conclusion as a citation.

The source 0AJU leaves details of the truncation equivalence omitted. Its argument must use Artin–Rees, rather than identifying J_n/J_n² with (J/J²)/H^n(J/J²): the latter is not generally true. The split explicitly identifies the kernel of J→J_n/J_n² and bounds it by J²+H^{n-k}J. Source 0GAG also displays a tensor product with reversed ring subscripts; the split never uses that ill-typed formula, and instead writes the actual quotient maps and commuting differentials. These are clarifications of the proof, not changes to the item statement or the unit route.

## Unfinished work

None for this one-level split. Existing cited nodes remain their own obligations. No new statement-only obligations were needed.

## Not duplicates

No new node pairs: the delivery creates no nodes. Whole-DAG searches for 0AJU, 0AK2, 0GAE, NL-is-limit, NL-base-change, completed conormal and homotopy/annihilation located the existing inputs. Blueprint-reference searches for completed conormal, completed polynomial, cotangent base change, NL-base-change, 0GAE and 0AJU found no imported blueprint node stating this item. The ancestor command gives lem-per-artin-gabber-affine-curve, matching the retained blueprint.from record. I reused lem-per-completed-cotangent-transitivity for its explicit Noetherianity, presentation existence and homotopy-independence clauses instead of making a duplicate of 0GAE or 0AJP/0AJQ. Its statement is stronger than that use, but its dependencies do not include this item. Ordinary presentation independence is reused from lem-weil-pbc-nl-presentations-homotopy-equivalent.

## Review by Q154

I read restricted.tex Tags 0AJP/0AJQ, 0GAE, 0AJS, 0GAG, 0AJU, 0AK2 and 0AL6 against this item. I also read algebra.tex 00S1 (ordinary presentation comparison), 00E0 (zero loci/radicals), 0319 (change of ideal), 00MA/00MB (finite-module completion), and 00IN (Artin–Rees). The proof follows these algebraic parts of the recorded local-duality/algebraization route. It uses no SGA source. No new nodes were created, so there is no additional new-node literature to certify.

Step 1 cites lem-per-completed-cotangent-transitivity: I checked its statement actually supplies presentations and Noetherianity for both algebras and homotopy independence, not merely the six-term sequence in its title. Taking C=B with identity meets its completeness and finite-type-mod-H hypotheses. I explicitly explain why the induced cohomology maps are inverse and linear, so annihilation is independent of presentation.

Step 2 uses only basis lifts in the finite free target. I recomputed δα=a and δ(aα)=(aα)δ=a² from the two assumed annihilation equations. This is an elementary calculation, not an extra node. It does not require J/J² to be projective.

Step 3 cites finite-type Noetherian permanence and finite-module completion-tensor comparison. I read both statements. The first applies to A→A[x] and the quotient A→A/L; the second applies to the cyclic module B/LB over the already Noetherian complete B and to R/LR over Noetherian R=A[x]. No assumption that B is finite over A is used. I wrote the two tensor-quotient inverses and product compatibility to justify the ring identification P/LP≅completion(R/LR).

Step 4 uses the definition of Noetherianity, the exact zero-locus/radical equivalence, the finitely-generated radical-power lemma and the change-of-ideal completion theorem. I checked their statements and that each ring/ideal is in the right base ring: H_0 and T=H(A/L) are ideals of the Noetherian quotient A/L. Both required positive power inclusions are established. The completion-mod-power statement at n=1 identifies the reduction of P_0 with the finite polynomial algebra; this supplies finite type modulo H_0 for the later use of completed presentation independence.

Step 5 cites the completed-polynomial-conormal definition for the compatible-sequence construction of the derivatives. I verified that coefficient reduction and the cofinal power reindexing commute with differentiation on those sequences. I checked π(J²)=π(J)², the surjectivity of q and ρ, and both descended homotopy equations. The map qh factors through F/LF because q is B-linear and L kills its target. Nothing assumes a tensor product preserves a kernel. These quotient and coordinate calculations are elementary steps, fully written out.

Step 6 uses finite generation of H^c in A and the already checked completed presentation-independence statement. The exponent d=c(t+1) depends only on the original annihilation bound and generators in A. I checked the pigeonhole inclusion on ideal generators and verified that neither L nor H_0 affects d. Completed presentation independence is applied over the Noetherian A/L using completeness and the finite-type reduction established in Step 4. The converse (ii)→(i) really is its specialization L=0,H_0=H.

Step 7 uses only the definitions of spectrum zero loci and adic completion. H(A/H^n) is nilpotent, and zero-adic completion is the constant inverse system, so (ii) applies with L=H^n,H_0=0. This explains why the single exponent works for the arbitrary polynomial presentations in (iii).

Step 8 cites completion-mod-power, the ordinary presentation homotopy theorem and the polynomial differential basis. I read all three statements: the first supplies the actual reduction P/H^nP, the second compares arbitrary variable sets and supplies linear homotopy inverse maps, and the third identifies the differential with the partial-derivative coordinates used here. This establishes the bound for the induced presentations without requiring compatibility of the chosen ones.

Step 9 uses finite-type Noetherian permanence and completion Noetherianity to make P Noetherian. The definition then makes J finite. The argument that its generators give B-generators of J/J² is written explicitly. The completion-tensor statement applies to the finite B-modules M and C, so their canonical completion maps are injective, giving separatedness. No finiteness of M as an A-module is asserted.

Step 10 lifts from the induced finite polynomial presentation to J and writes the cokernel class in every H^nC. It then uses exactly the separatedness already proved, so no unnamed limit-cohomology or Mittag–Leffler result is hidden here.

Step 11 cites the existing Artin–Rees statement for finite P-modules J⊆P and ideal HP. P is Noetherian and J finite by Step 9. I checked the inverse image J²+(J∩H^nP) directly, applied the Artin–Rees bound in its stated direction, and used separatedness of M. This proves the remaining kernel bound with the same e, without equating finite-level conormal modules with ordinary tensor reductions. Every non-elementary fact in these steps is a cited statement; citations.json copies actual statement text, not proof text.

I tested H=0 (all positive ideal powers vanish), H=A (completeness forces B=0), nilpotent H (finite towers stabilize), zero algebra B, r=0, J=0 and J=P, c=0 (the homotopy contracts the complex), L=0 and L=A, and H_0=0. The generator bound covers t=0, and the Artin–Rees argument only uses n≥max(1,k), so no negative exponent is formed. In step 7 every prime contains the nilpotent image of H, including the empty spectrum case. None of these cases requires an added hypothesis.

No proof step exceeds 2000 characters. I checked delivery-errors B1–B10 (self-contained existing statements, actual searches, exact sources and blueprint); C1–C8 (complete cited inputs, exact statements, no use of an internal proof as a theorem, route tools declared); D1–D5 (actual argument rather than clause-renaming, no new restatements or cycles); and E1–E7 (hypotheses, actual quotient objects, two meanings of ordinary/continuous differentials kept separate, no silent source error). The off-unit commutative-algebra citations are listed as generic tool uses in split_report, since no perverse-curve lemma replaces these algebraic facts.

Mathlib searches were run through msearch.py and their actual outputs inspected. Loogle found no joint cotangent/completion theorem; grep found only the local-ring completion cotangent-space calculation, which I opened at LocalRing.lean:161 and which is unrelated to the uniform presentation criterion. LeanSearch and both LeanFinder phrasings returned completion definitions, completion-tensor/exactness and formally-smooth lifting results, not the item. The already-recorded searches were preserved. No unavailable response is recorded as a negative result.
