# Stage-1 worker report: lem-exc-dvr-galois-degree-data

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-dvr-galois-degree-data.json`: item, statement unchanged, eight proof steps, status split.
- `dag/nodes/sec-smooth-purity/lem-exc-dvr-norm-valuation-sum.json`: new statement-only lemma, status unsplit. No Mathlib match for the norm/order identity for arbitrary nonzero elements. The generality is finite semilocal DVR algebras, without a Galois or integral-closure hypothesis.
- `citations.json`: one verbatim statement quote for every step/node citation.
- `report.md`: this report. The sandbox also contains the genuine msearch log and the captured dry-run output.

One new node, zero new Mathlib leaves. No unit record needs changing: this item is a child, not the key statement of its unit.

## Attachments

None. Searched the slopmaster2 project under WeilConjectures for the exact blueprint tag and for DVR/Galois/degree, normalization, norm/order and norm/valuation terminology. The curve SerreDuality.lean computations concern finite flat maps of curves, not the complete statement here or the arbitrary-element norm formula of the new helper. Master source was reference only. No Lean file was written or compiler invoked.

## WANTED

None. All mathematical sources used are in literature/stacks-project.

## Corrections and scope

The imported statement is true as written. In particular it needs neither excellence nor henselianity: separability gives finite normalization by Tag 032L. Residue extensions need not be separable. The item had no proof; it now separates the finite-normalization, finite-fibre/Dedekind, localization, conjugacy and degree arguments. No statement dispute or unit-route departure was found. All inherited fields were retained.

The one new helper is the general norm formula of Tag 02MJ in DVR language. It does not state the item or its degree clause: it applies to arbitrary elements y in finite extensions, with no Galois group and no normalization construction. Its application to the scalar pi_A, including the determinant calculation pi_A^n, is written in step 8. No proof or proof sketch is put inside the new node's statement.

## Not duplicates

There is no existing node with Tag 02MJ or the label lemma-finite-extension-dim-1. Whole-DAG statement searches and blueprint searches for 02MJ, finite-extension-dim-1, norm-order, valuation of the norm, weighted by residue and residue degrees found no equivalent statement. The item blueprint search for dvr galois degree data and galois degree also found no equivalent blueprint node.

- lem-exc-dvr-norm-valuation-sum vs lem-exc-dvr-galois-degree-data: the former is the weighted valuation identity for every nonzero field element in any finite DVR algebra satisfying the stated local conditions; the latter constructs normalization data and asserts the scalar degree identity in a Galois extension. The parent's step computes the scalar norm and proves the equality of local invariants.
- lem-exc-dvr-norm-valuation-sum vs lem-sbc-dvr-galois-normalization-ramification-dvd: the existing node only gives divisibility of e and f in a finite Galois normalization; it does not evaluate norms of arbitrary elements.
- lem-exc-dvr-norm-valuation-sum vs lem-exc-finite-galois-prime-residue-lifting: the existing node supplies prime conjugacy and residue automorphism lifting, and says nothing about the norm/order formula. It is reused for conjugacy, not duplicated.

The Mathlib general finite-flat e-f fundamental identity is not the new helper's arbitrary-element norm formula. Its use would require a further argument identifying ideal norm valuations and scalar norms. Read pinned RingTheory/RamificationInertia/Basic.lean:44-88, NumberTheory/RamificationInertia/Galois.lean:75-100,132-156,210-236 and Ideal/Norm/RelNorm.lean:401-434. The sources found by the norm searches define norms, normalized valuations and localization compatibility; none is a one-line specialization proving the helper. The item likewise is not a one-line specialization of the finite-flat invariant-algebra identity, because finite normalization and the DVR/uniformizer interpretation remain to be established. Search records are selected verbatim from searches.jsonl, including actual tool names and query text. An exploratory grep targeted the old monolithic OrderOfVanishing.lean path, which does not exist in this pinned tree; that inconclusive search is not evidence of absence. The actual Basic.lean source and the focused Ideal/Norm grep were read instead.

## Review by N7

I read Stacks more-algebra.tex, Remark 09E8 and Lemmas 09EA and 09EB, against every clause of the item, and the current main-20261015 lem-exc-dvr-galois.proof.md first paragraph against its blueprint ancestry. The chapter and sk-prop-a1-kummer unit records were read; their binding is inherited and the helper supports the indicated local ramification calculation. For the new norm helper I read Algebra Lemma 02MJ and its proof, the preceding Definition 02MD of order by length, and 00PD's uniformizer description. For a DVR, the filtration by powers of a uniformizer has successive quotient the residue field; its length/order is therefore the uniformizer exponent, exactly the normalization of valuations in the new statement. Thus 02MJ really gives the stated formula, with arbitrary y, including elements with negative valuations. Norm means the field determinant, not the absolute value appearing in several irrelevant search hits.

Step 1 uses the definition's integral-domain and principal-ideal clauses, the existing PID/Noetherian/normal Mathlib leaf, and the separate dimension-one node. I opened both theorem statements and checked that they provide exactly these conclusions. During self-review I replaced the longer monic-equation normality argument with the existing PID leaf. Its only hypothesis is an integral domain with all ideals principal, directly supplied by the DVR definition; no completeness or excellence is used.

For step 2 I opened the four cited statements. The 032L node supplies module finiteness under exactly the Noetherian, normal and separable hypotheses proved or assumed here. The integral-closure definition supplies integrality. The fraction-field/normalization node supplies B being a domain with fraction field the specified L. The existing 09IG node explicitly supplies Dedekindness, surjectivity, finite fibres and finite residue extensions for any finite fraction-field extension of a one-dimensional Noetherian domain. I read the corresponding Algebra source at 032L and 09IG. This last result is declared as a generic tool use: it is not a replacement proof of the unit's cohomological route.

Step 3 uses the maximal-preimage assertion verbatim in the integral-algebra/Jacobson-radical node, with I=m_A contained in the radical because A is local. This proves all maximal ideals lie above m_A. In the reverse direction a prime in that fibre contains the nonzero base uniformizer; in the one-dimensional domain B it must be maximal. The surjectivity and finite-fibre assertions in step 2 now give exactly a nonempty finite X, not merely a finite subset of it.

Step 4 uses the Dedekind-localization node, whose assumptions were established in step 2, and the definition of localization, whose statement explicitly gives the maximal ideal qB_q. I wrote the residue quotient map b/s to bbar/sbar, so B/q and the local residue field are identified by an explicit map. Locality follows from contraction to m_A. Finite residue degree comes from the statement of the cited 09IG node in step 2. The degree is positive because it is a field extension.

Step 5 uses the existing unit-times-uniformizer-power node, with its Noetherian local domain and nonzero principal-maximal-ideal assumptions supplied by B_q being a DVR. The base uniformizer is nonzero since the structural embeddings land in L, and is a nonunit by locality. I checked positivity, uniqueness by cancellation, and independence of the chosen uniformizer rather than assuming these.

Step 6 uses exactly the first clause of the existing finite-Galois-prime/residue-lifting node. It states both the restriction action on B and conjugacy of primes having the same contraction; it does not merely define decomposition groups. A is normal by step 1 and L/K is finite normal separable by hypothesis, so all its hypotheses hold. I read the underlying 0BRK statement and 09EA's proof. No residue separability is required or inferred.

Step 7 is the explicit elementary argument behind 09EB. The local isomorphism maps b/s to sigma(b)/sigma(s), has inverse sigma^{-1}, and fixes A. It takes a maximal-ideal generator to a generator, hence a unit multiple of the chosen target generator. Uniqueness from step 5 proves equality of e. The quotient isomorphism fixes k and maps a basis to a basis, proving equality of f. The proof does not cite a node's internal construction and does not assume the result it is deriving.

Step 8 cites the new norm formula, after checking each of its hypotheses against steps 2--4. The scalar multiplication map by pi_A is diagonal on a K-basis of L; its determinant is pi_A^[L:K]. The normalized valuation on A reads this as [L:K], and each local valuation reads the exponent already constructed in step 5. This derives the sum of e_q f_q, then uses step 7 and finiteness of X to obtain g e f. I did not silently substitute a residue automorphism-group order for the full residue degree.

I tested the helper and the item on the identity extension (one prime, e=f=1), on an unramified DVR extension (e=1 and the degree is the residue degree), and on a totally ramified extension (f=1). For a split prime such as 5 in the Gaussian field over Z_(5), g=2 and e=f=1; the scalar norm formula sums both primes and gives 2. For the helper, a unit contributes order zero, inversion changes both sides' signs, and y=pi_A has the computed positive orders. The hypotheses allow imperfect residue fields and inseparable residue extensions; the length/norm source has no residue-separability assumption. A field is not a DVR under the project's definition, so the excluded dimension-zero base is not an overlooked case.

I checked B1--B10: the new node is statement-only, introduces all objects and valuation/norm conventions, cites definition nodes or defines the convention inline, has the verified Stacks tag and genuine searches, and has exact blueprint ancestry. I checked C1--C8 step by step as described above, recorded every uses citation verbatim in citations.json, and declared the single off-unit non-leaf tool. I checked D1--D5: the proof performs the normalization/conjugacy/scalar determinant argument and does not simply apply a new copy of its degree clause. I checked E1--E7 against the actual hypotheses; in particular separability is used only where given, every finite-dimensional degree has the correct base field, and no false source claim was found. All files remain in the sandbox for the second reader.

## Unfinished work

No part of this one-level split is deferred. The new statement-only norm formula is deliberately left unsplit for a later worker. Delivery has not been pushed. The required command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py N7 lem-exc-dvr-galois-degree-data --no-push`; its complete output is captured in `dry-run.log`.

## Second reading by N7

- Item statement: checked hypothesis by hypothesis against More on Algebra Tags 09E8, 09EA, and 09EB; the DVR, finite normal separable extension, integral closure, finite nonempty maximal-ideal set, transitivity, local DVRs, positive common (e,f), and ([L:K]=gef) clauses all agree.
- Step 1: checked against the definitions and statements of `def-sc-discrete-valuation-ring`, `lem-weil-pbc-pid-noetherian-normal`, and `lem-sc-dvr-dimension-one`; the elementary reduction supplies exactly Noetherian normal dimension-one hypotheses.
- Step 2: checked against Algebra Tag 032L, the integral-closure definition, and the existing finite-extension normalization and Dedekind/fibre nodes; finiteness, domain/fraction field, Dedekindness, finite fibres, and finite residue extensions are all stated by the cited nodes.
- Step 3: checked the contraction argument against the integral-algebra/Jacobson-radical node and the preceding domain and dimension facts; the fibre is exactly the finite nonempty set of maximal ideals.
- Step 4: checked localization, residue quotient identification, locality, and finite positive residue degree against the Dedekind-localization and localization-definition nodes; the explicit (b/s\mapsto\bar b/\bar s) map supplies the needed identification.
- Step 5: checked the uniformizer-power decomposition and uniqueness against the DVR unit-times-power node and the local-domain hypotheses; positivity and independence of the uniformizer are explicitly justified.
- Step 6: checked the Galois action and conjugacy against the complete statement of `lem-exc-finite-galois-prime-residue-lifting`, with normality and separability supplied by Step 1 and the item hypotheses.
- Step 7: checked the localization isomorphism, transport of maximal-ideal generators, and induced residue-field isomorphism directly; the argument is elementary and proves equality of both (e) and (f) without using an unstated residue-separability assumption.
- Step 8: checked every hypothesis of the norm helper against Steps 2–4 and checked the determinant computation (N_{L/K}(\pi_A)=\pi_A^{[L:K]}); the normalized valuations give the sum of (e_qf_q), and Step 7 gives (gef).
- New node `lem-exc-dvr-norm-valuation-sum`: checked its self-contained statement, definitions, Tag 02MJ source, blueprint ancestry, and all recorded LeanSearch/Loogle/LeanFinder/grep searches. It is a strict auxiliary norm formula and does not restate the item; small tests include the identity, unramified, totally ramified, unit, inverse, and split-prime cases.

Changes made: (1) corrected the prime notation in Steps 6–7; (2) expanded the elementary comparison of two uniformizer generators in Step 5, using cancellation to exhibit the unit; (3) recorded independent LeanFinder, Loogle, and grep searches in the helper and the genuine search log. The ideal-norm hits `Ideal.relNorm_singleton` and `Ideal.spanNorm_singleton` (RelNorm.lean:301 and :82) concern principal ideal norms; obtaining the claimed arbitrary-element weighted formula from them still requires the prime-norm comparison, factorization and valuation identifications. RelNorm.lean:401–440 makes the Galois/perfect-field restrictions explicit for those prime-norm comparisons. No new node can be removed as a one-line Mathlib specialization or a duplicate.

Additional source/edge-case checks: Tag 02MJ assumes a Noetherian local one-dimensional base and a finite injective extension of domains; the helper's DVR hypothesis supplies the base conditions. The powers-of-uniformizer filtration has successive quotients equal to the residue field, so the length order of Tag 02MD equals the normalized exponent; differences handle negative powers. For the identity extension both sides equal the exponent of the element; units give zero, inverses negate both sides, and a split prime contributes every local summand. The zero ring and a field are excluded by the DVR definition; degree zero cannot occur for a field extension, while degree one gives the identity case. No residue separability, completeness, excellence or henselianity is silently added. The statement and helper remain unchanged, the helper is statement-only, and citations.json still contains the exact quoted statements.
