## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-ramero-henselian-section-lifting.json: item, split with four steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-ramero-improve-precision.json: statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-elkik-generic-smooth-section-approximation.json: statement-only lemma, unsplit; no Mathlib match.
- citations.json: verbatim statements for every step/uses pair.
- searches.jsonl: actual msearch.py output records; queries and results copied into the relevant nodes. write_split.py is a sandbox-only preparation script.

## Attachments

None. Searched the project's WeilConjectures source for the item tag, Gabber/Ramero, henselian sections, approximation and obstruction terminology. No declaration states this bounded-loss result. The existing HenselianPairApproximation theorem assumes a G-ring, which the item does not assume; ordinary smooth section lifting also does not apply to the possibly singular C.

## Literature wanted

WANTED: Michael Temkin, Functorial desingularization of quasi-excellent schemes in characteristic zero: the non-embedded case, https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf, Theorem 3.2.3 and Remark 3.2.4, for lem-per-gabber-ramero-henselian-section-lifting (archival copy).

WANTED: Ofer Gabber and Lorenzo Ramero, Almost Ring Theory, sixth final release, https://pro.univ-lille.fr/fileadmin/user_upload/pages_pros/lorenzo_ramero/releaseLNM.pdf, Definition 5.4.1, Lemma 5.4.2, formula (5.4.4), Lemmas 5.4.8 and 5.4.12, Proposition 5.4.13 and Claim 5.4.14, printed pp.148–152, for this item and its two new nodes (archival copy).

WANTED: Renée Elkik, Solutions d'équations à coefficients dans un anneau hensélien, Chapter II, Theorem 2 bis, for lem-per-elkik-generic-smooth-section-approximation. This is the theorem GR Lemma 5.4.12 explicitly cites; the present split uses GR's stated lemma, not an unread proof of Elkik.

Both PDFs were read online through the browser, without downloading files into the shared repository. proof_origin is agent because the archival documents are absent from literature/ and the coordinate assembly is written here.

## Corrections and provenance

The mathematical statement is preserved, including Noetherianity, regularity of t on R and C, n>r, input precision n+r, and agreement only modulo t^n. The proof actually does not need regularity of t on C, but I have retained this original hypothesis.

The source citation incorrectly said GR Proposition 5.4.13 with auxiliary ideal zero. In GR notation the auxiliary ideal must be the unit ideal I=R: (R,tI)=(R,tR), and t^qI=t^qR. If I=0, the input conditions demand exact equations and produce no nontrivial approximation. Corrected that citation without changing the statement. Temkin's theorem is correct.

The latest blueprint ancestor lem-per-artin-gabber-affine-curve has no formal-resolution argument: its current Step 3 concerns duality and affine pushforwards. This auxiliary branch's attribution is inherited from the existing creation chain, already reported by the parent's accepted split. I preserved its ancestry and explicitly disclosed the mismatch in the new blueprint places and split_report, rather than inventing a sentence in the current ancestor. Searched the whole DAG and blueprint (blueprint_refs search for Gabber, Elkik, precision, henselian approximation, obstruction lifting, approximate solution, plus keyword/source searches of latest/). No blueprint node states either new lemma.

## Not duplicates

lem-per-gabber-ramero-improve-precision vs lem-per-gabber-ramero-henselian-section-lifting: the new lemma improves a polynomial solution to a single finite quotient over an arbitrary ring; it asserts no actual section and assumes no henselianity. The item's iteration and algebraization are still proved in its own steps.

lem-per-gabber-ramero-improve-precision vs lem-per-principal-adic-homomorphism-lift: the existing node assumes complete source and target and a two-sided t^h inverse to the conormal map, hence generic étaleness; the new finite-precision lemma needs only hδ=t^r and permits positive relative dimension. It cannot be obtained by specializing the existing statement.

lem-per-gabber-ramero-improve-precision vs lem-per-gabber-ramero-ideal-calculus: the existing node identifies an ideal, its smooth locus and functoriality, not improvement of solutions.

lem-per-elkik-generic-smooth-section-approximation vs lem-per-gabber-ramero-henselian-section-lifting: the new lemma starts from an actual section over the entire completion, permits arbitrary ideals and has no conductor or finite-input precision bound. The item's Steps 1–3 construct that formal section with the required initial precision.

lem-per-elkik-generic-smooth-section-approximation vs lem-weil-pbc-henselian-pair-approximation: the existing node requires a G-ring; the new node only assumes Noetherianity and replaces that condition by smoothness outside the closed fibre.

lem-per-elkik-generic-smooth-section-approximation vs lem-weil-pbc-henselian-approximation-alg-hom: the existing node requires a G-ring and states agreement modulo I, rather than all powers under generic smoothness and arbitrary Noetherianity.

lem-per-elkik-generic-smooth-section-approximation vs lem-per-etale-away-completion-hom-lifting: the existing node assumes étaleness away from the closed fibre and asserts exact, unique descent; the new node permits smooth positive relative dimension and only asserts approximation to each chosen finite order.

lem-per-elkik-generic-smooth-section-approximation vs lem-per-elkik-finite-etale-away-completion: the existing node concerns finite algebras and equivalence of categories; the new node concerns sections of an arbitrary finitely presented algebra smooth on the indicated open.

lem-per-elkik-generic-smooth-section-approximation vs lem-trf-henselian-smooth-algebra-lifting: the existing node assumes smoothness everywhere and lifts a section of the closed fibre; the new one permits singularities on the closed fibre and requires an existing formal section.

lem-per-elkik-generic-smooth-section-approximation vs lem-trf-artin-approximation-etale-local-map: that statement is local and assumes a G-ring; the new statement is for arbitrary Noetherian henselian pairs with the generic smoothness hypothesis.

There are no claimed Stacks tags for the new lemmas; neither was found verbatim in the local Stacks source. References are the GR theorem numbers, not invented tags. Related formal algebraization and perturbation nodes construct algebras or isomorphisms of complete algebras, not these finite improvements or henselian approximations of sections.

## Review by Q140

I read Temkin Theorem 3.2.3 and Remark 3.2.4 online and followed its reference through GR Definition 5.4.1, formula (5.4.4), Lemmas 5.4.2, 5.4.8 and 5.4.12, and the proof of Proposition 5.4.13 (including Claim 5.4.14). In the Noetherian case at hand, GR's Noetherian-approximation passage for a general base is unnecessary. The proof separates the genuinely non-elementary finite improvement and Elkik approximation into the two new nodes; neither new node carries a proof or proof dependency. The finite improvement's conormal-factorization hypothesis is precisely the characterization GR uses for its ideal. The second new node is the special case of Lemma 5.4.12 with U the entire complement of V(IB), so every formal section automatically has the required restriction into U. Its conclusion is expressed using inverse-limit projections, making the exact meaning of finite agreement explicit.

For Step 1 I opened def-weil-pbc-finitely-presented-algebra and def-per-gabber-ramero-obstruction-ideal. The former supplies the finite presentation and the latter explicitly defines H as an intersection of presentation ideals, each defined by hδ=b id. Thus t^r belongs to the ideal for this chosen presentation without requiring an extra presentation-independence theorem. Lifting finitely many coordinate residues and observing that J evaluates to zero modulo t^(n+r) are elementary quotient calculations.

Step 2 uses precisely the new improve-precision statement. Its premise q>2r is checked at every stage, not just initially: q_k=2r+2^k(n-r), and n-r>0. The output exponent is 2(q_k-r), and the preserved exponent is q_k-r. These are exactly the two clauses the cited node supplies. The same fixed h is used each time, so there is no hidden claim that an approximate solution preserves some new obstruction ideal.

Step 3 uses only the compatible-sequence definition in def-weil-pbc-adic-completion. For each quotient, the growing difference exponents make the coordinate residues eventually constant; finite polynomial evaluation commutes with quotient maps and therefore all relations vanish in every coordinate. This proves factorization through P/J directly. It avoids assuming a completion is flat, that t remains regular after completion, or that completion commutes with the conormal ideal. Every successive difference is divisible by t^n, which proves the precise comparison with the original approximate section.

For Step 4 I opened lem-per-gabber-ramero-ideal-calculus and read its statement. It identifies the nonsmooth locus exactly as V(H), so t^r in H proves smoothness at every prime not containing t; no smoothness on the closed fibre is asserted. The new approximation lemma applies with the original ring R and original ideal tR, not a higher-power ideal for which henselianity was not established. R is Noetherian and C is finitely presented by the item, and n>=1 follows from n>r>=0. Its equality after coordinate projection combines directly with Step 3. Each citation in these four steps has a verbatim statement quote in citations.json. The new-node statement dependencies were read and define exactly the named notions.

I tested the small cases: r=0 gives q_{k+1}=2q_k and smooth C; n=r+1 gives q_k=2r+2^k and still strictly growing precision; n=r would not grow and is correctly excluded. For J=0 or d=0 the finite improvement permits b=a and the quotient calculations still apply. A unit t makes the finite congruences vacuous, consistent with that lemma. In the approximation statement I=0 gives the identity completion and the conclusion is tautological; the zero ring and empty smooth-open cases cause no extra nonemptiness assumption. Smooth polynomial algebras of positive relative dimension show why the étale-away descent node is insufficient. No characteristic-zero, field, locality, excellence, or G-ring condition has been inserted.

I checked delivery-errors B–E against the files: statements introduce all their objects and use single TeX escapes; both new nodes are unsplit statements only; all non-elementary facts are cited nodes whose statements say what is used; no clause of the item is moved verbatim into a child, and no dependency points back to the item. The iteration and inverse-limit argument remain in the item. No step exceeds 2000 characters (the four lengths are 376, 401, 617, 614), and total proof text is under 3000 characters. Mathlib searches used the mandated msearch.py command for each node with two natural-language phrasings, Loogle and grep; I read the returned types and the formal-smooth lifting/conormal source. All services returned results, and none gives either new statement. No Lean file was written and no compiler was run.

## Unfinished work

No part of this one-level split is left unfinished. The two new statement-only nodes intentionally remain unsplit for the queue. Required delivery validation follows this review.
