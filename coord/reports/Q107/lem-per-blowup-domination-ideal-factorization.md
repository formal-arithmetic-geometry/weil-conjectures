# Q107: lem-per-blowup-domination-ideal-factorization

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-blowup-domination-ideal-factorization.json`: statement node, now split into eight steps. Statement and statement dependencies unchanged; no Mathlib match.
- `citations.json`: thirteen verbatim statement quotations, one for every step/node citation.
- `report.md`: this report.
- `searches.jsonl`: actual msearch log, retained in the sandbox.

No new nodes and no new Mathlib leaves. This is a genuine proof using existing lemmas, rather than moving either implication into a new node.

## Attachments

None for this item. Searched the exact blueprint id and blowup/domination/factorization notions under `lean/WeilConjectures/`. The existing blowup library gives charts, principalization and lifting, but no declaration found states this equivalence. In particular the substantial finite-degree and quasi-domination files concern other statements. Reused the existing closed node `lem-sc-affine-invertible-sections`; did not recreate its affine evaluation theorem.

## WANTED

None. ILO, the Stacks sources, current blueprint and relevant project Lean sources are present.

## What needed correction or completion

The item had a statement and searches but no proof. ILO XX 4.4, printed p.373 (PDF page 379), explicitly states the domination criterion under the weaker inclusion of supports. It does not give its algebraic proof. The proof here is therefore labelled agent-written, not attributed as a proof copied from ILO. The equal-radical specialization in the item is valid, including nilpotent ideals. I made no statement correction and found no statement dispute.

Two tempting shortcuts would be wrong or incomplete. First, a Cartier ideal need not remain Cartier under an arbitrary morphism. Step 2 uses the actual equation b^a=uv and regularity of b on a K-chart to establish regularity after this particular pullback. Second, identities in R_b need not already hold in R. Step 4 multiplies every one of the finitely many discrepancies by a common b-power before asserting the required equalities in R. Also the full colon ideal need not be finitely generated: step 6 retains only finitely many coefficients, rather than claiming it is finite.

The inherited `blueprint.from.place` described a literal completion-comparison sentence in ancestor Step 3. I read `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`: its current Step 3 is the duality-symmetry paragraph and no longer contains that sentence. The inherited from.node and via chain have been retained; the place and split report now distinguish the current ancestor paragraph from the technical completion/punctual-purity chain through which this item was introduced. The latest unit statement and proof, and the chapter and unit records, were also read. This is algebra below those unit steps, with no change to their proof route.

The existing `thm-nagata-blowup-universal-property` statement is phrased in terms of its own constructed map and even refers to its own data; I did not rely on that imprecise statement for an existence claim. Instead step 8 cites the explicit general space lifting statement, its definition of scheme representables, and the Yoneda morphism bijection. The cited space statement explicitly identifies its chart construction with ordinary scheme blowups.

## Search record and reuse

The inherited item searches are preserved. Actual additional searches for the item used LeanFinder in two distinct phrasings, LeanSearch, Loogle `reesAlgebra, Ideal`, and msearch grep `blowup|blow.up|reesAlgebra` in `AlgebraicGeometry`. The hits give radical power containment, Rees algebra construction, or general ideal-sheaf maps, not blowup domination and ideal factorization. The item is not a Mathlib leaf. The results, including signatures, were read.

I also investigated a possible auxiliary inverse-ideal node with the logged fractional-ideal searches. Those results assume domains, principal fractional ideals, or Dedekind hypotheses, or start with invertibility already given. Before creating it, I found the existing exact affine evaluation statement `lem-sc-affine-invertible-sections`. Its evaluation clause plus the formula phi(b^a)/b^a gives the comparison needed here in a few lines (step 3). Accordingly no such new node was created. The auxiliary searches remain honestly in the log; no fictitious query was added to any node.

DAG searches covered blowup/chart/universal-property/ideal-inverse notions; whole-blueprint searches were run for `blowup`, `ideal factor`, `locally principal`, and `fractional` (and `fractional ideal`). There is no imported statement equivalent to the item. The existing divisorial fractional-module node assumes a Noetherian normal domain and concerns height-one valuation lattices, so it is not a substitute for an arbitrary-ring chart argument.

## Not duplicates

There are no new nodes. The proposed inverse-ideal auxiliary lemma was deliberately not created because existing affine evaluation and an explicit short calculation suffice. All non-elementary tools are citations of existing nodes.

## Review by Q107

I read ILO XX 4.4 on printed p.373, including the sentence with J-prime^n=J K and the preceding support condition. I checked the supporting source statements and arguments in Stacks algebra.tex, definition-blow-up and Tag 07Z3 (lemma-affine-blowup); divisors.tex, Tags 0804 (lemma-blowing-up-affine), 02OS (lemma-blowing-up-gives-effective-Cartier-divisor), 07ZV (lemma-sum-closed-subschemes-effective-Cartier), and 0806 (lemma-universal-property-blowing-up); more-algebra.tex, Tag 0B8I (lemma-invertible), especially its evaluation map; and algebra.tex, Tag 09ME (lemma-product-ideals-principal). I also read spaces-divisors.tex Tag 085U (lemma-universal-property-blowing-up). I read the closed project source for affine invertible sections and for ideal_comap_appLE, rather than assuming a definition node provided their theorems. No new node needs a separate source review. No SGA source is used.

Step 1 uses the actual finite chart-cover statement, the actual subalgebra-of-R_b chart definition, and the affine extension theorem. The last theorem says precisely that sections of the pulled-back closed ideal are generated by the images of the original ideal; it applies with the entire affine X and each affine chart of B_K. I wrote out the common-denominator representation instead of treating the chart definition as a theorem about arbitrary fractions. Multiplication by b is injective because this particular chart embeds in R_b, even when R to R_b is not injective.

Step 2 uses the principalization statement on B_J with finite-type center J; finite generation is a hypothesis of the item. The affine extension theorem justifies composition of the ideal extensions. Its other citation is the definition of an invertible module, used only after local rank one has been proved. For every b in K the required positive a follows directly from equal radicals. The equality b^a=uv at each source stalk proves that u is regular, without using any flatness of f. This verifies the hypothesis of the next step, rather than presuming it.

Step 3 uses exactly the evaluation isomorphism in `lem-sc-affine-invertible-sections`, not merely the assertion that sections are projective or the coevaluation of a dual pair. The scheme is the affine K-chart and the module is the extended J ideal from step 2. Surjectivity supplies the finite sum evaluating to 1. The displayed linearity calculation identifies each functional with multiplication by phi(b^a)/b^a inside R_b. Expanding the finitely many x_nu in the fixed generators of J gives a finite list w_t with both required identities. The comparison is explicit; no independent fractional-ideal theorem is being smuggled in.

Steps 4, 5 and 6 cite no extra theorem. Step 4 is the finite denominator calculation using the representation already established in step 1 and the definition of localization equality. The common multiplier kills the torsion of all the listed differences; it does not need any bound for the torsion of the whole ring. Each adjusted numerator satisfies the colon condition for every generator j_u, hence for every element of J. Step 5 is a monomial pigeonhole argument: N is positive and N>=e_i for every i, and every degree-N generator of K^N lies in JC_N. Stability K C_d contained in C_(d+1) is checked by multiplication. Step 6 is precisely finite coefficient extraction from finite expressions for a finite set of generators; it does not assume R Noetherian or the colon ideal finite. These are routine calculations, not new statement-only nodes. I checked all step lengths; none exceeds 2000 characters.

Step 7 reuses the principalization theorem with center K and the affine extension theorem. It proves that extension respects the products and powers here by their generators, and that a positive power of a regular generator is regular. Only then does it invoke the ring ideal product-factor theorem; its premise is the effective-Cartier property of the product, exactly what that theorem states. Applying it on affine opens proves the local Cartier property of the extended J ideal. No domain, reducedness, density or Noetherian assumption is inserted.

Step 8 invokes the explicit unique-lift clause of `lem-sfb-space-blowup-universal-property` with its finite-type ideal J and the Cartier property just proved. The two other cited statements really provide the representation of schemes and the bijection between natural transformations of representables and scheme morphisms; no general Yoneda-evaluation theorem is taken from a mere full-faithfulness slogan. They also reflect the equation over X. These uses are declared as generic tools across units, and do not replace a unit argument.

For each of the thirteen citations I opened the existing node's statement and copied it verbatim into citations.json; the paragraphs above identify exactly what is used from it. `proof_deps` is the union of the uses lists. I kept the original statement and definitions, created no unsplit restatement of either implication, and checked that the argument uses only existing foundational lemmas. The absence of a proof in ILO is filled by the argument in the item, not by a reference to an unnamed standard fact.

Small cases: in the zero ring all charts and blowups are empty and the same formulas hold. For J=K=R one may take n=1 and L=R. If J=0, equality of radicals makes the finitely generated K nilpotent (use the same monomial bound for nilpotent generators), so some K^n=0=J times 0 and both blowups are empty. In k[epsilon]/(epsilon^2), J=0 and K=(epsilon) give n=2,L=0; reversing J,K gives n=1,L=0. For the zero-divisor example R=k[x,y]/(xy), J=K=(x), one has a single chart R[K/x]=k[x], x remains regular there while y dies on localization; n=1,L=R works, and step 4 explicitly handles this lost x-torsion. Over k[x,y], J=(x,y) and K=J^2 give the standard common blowup and K=J times J, while the formulas do not assume that the colon factor was principal. Empty charts are allowed in the cover and in affine evaluation. These checks confirm the exceptional cases that a domain-only or arbitrary-pullback argument would miss.

## Unfinished work

None in this split. All proof obligations of the item are written out or cite existing statements. Validation and delivery results are recorded below after the required server checks.

## Validation

Server review_split passed with zero new nodes. The required deliver.py --no-push invocation exited successfully: `OK (not pushed)` at `41bf1ca3698`, with server preflight passed (including check_dag and review_split). No local compiler, Lake, global build, or forbidden local validation script was run. No numbered delivery failure remains.
