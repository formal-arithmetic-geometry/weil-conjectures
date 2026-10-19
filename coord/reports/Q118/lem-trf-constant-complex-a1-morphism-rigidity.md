# Worker report: lem-trf-constant-complex-a1-morphism-rigidity

## Files written

- dag/nodes/sec-trace-formula/lem-trf-constant-complex-a1-morphism-rigidity.json: statement; five-step split using existing nodes; no Mathlib match.
- citations.json: exact statement excerpts for all 16 step/node citation pairs.
- report.md: this report. The retained prepare_split.py and searches.jsonl document preparation and actual searches and are sandbox support files.

New nodes: 0. Mathlib leaves: 0. No unit record changed: this item is not its unit's key statement.

## Attachments

None. The search in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag, rigidity of morphisms, homotopy invariance and constant complexes found no declaration giving this derived etale statement. The module-sheaf rigidity and scheme-theoretic rigidity declarations have different objects. No upstream master sorry declaration is treated as a finished proof.

## Wanted sources

None. The Varshavsky paper, current blueprint, cited node statements and supporting Stacks source are present locally.

## Findings and changes

The item's statement and statement dependencies are unchanged. The original item had no proof. This delivery supplies affine-line unit acyclicity, the arbitrary-complex unit calculation, adjunction fullness, and section restriction as a complete argument. The item deliberately admits nonperfect bounded finite modules over A. Replacing derived internal Hom by P-dual tensor Q would need an extra hypothesis, so that shortcut is not used. Varshavsky Lemma 3.1.4 is used only in the affine-line/point specialization needed by Lemma 3.1.3; no assertion for a general connected parameter scheme is introduced.

I compared the retained sandbox with the current repository after the interrupted turn: the repository still has the unsplit item, with the same statement, origin and unit. I retained its proof, citations and actual search records. The added Mathlib records correspond to searches.jsonl from the earlier part of this same dispatched task. Its two LeanFinder phrasings, Loogle, grep and LeanSearch returned ordinary scheme/affine-space facts or complex restriction facts, not the finite-coefficient derived etale assertion. No search is claimed to be unavailable when it returned hits, and no invented query is recorded.

The whole-DAG and blueprint search found nearby ordinary-sheaf results lem-pur-lisse-morphism-rigidity and lem-pur-site-constant-module-hom, and the sheafified derived-Hom statement lem-weil-pbc-finite-ring-derived-local-constancy. These do not by themselves identify global derived morphisms with point morphisms: sheafification can lose global extension classes. I used the existing acyclicity and Kunneth nodes instead of creating a restatement of the item. All off-unit tools are explained individually in split_report.tool_uses. The unit route stays the normal-cone contraction proof of Varshavsky, as in the main-20261015 ancestor lem-trf-local-term-locality and the existing constant-defect chain. No SGA source is used.

## Unfinished work

None in the one-level split; the existing cited unsplit/imported nodes remain their own items. No Lean was written and no compiler, Lake or build command was run.

## Review by Q118

I read Varshavsky, arXiv math/0505564, Lemmas 3.1.3 and 3.1.4 (printed pp. 22–23), including the construction whose fibres are phi_a. Its specialization X=affine line and Y=Spec k is exactly the equality this item needs. I also read the current main-20261015 sk-i-curve-zero unit and lem-trf-local-term-locality, its recorded blueprint_update, and the repository chapter/unit records. They place this rigidity input below contracting-correspondence local terms; it does not replace any higher-level route. There are no new nodes whose statements require separate source review.

Step 1 uses the actual statement of lem-kun-0ezp: over a separably closed point, every etale object is a disjoint union of points. The sheaf gluing formula is written out, including its componentwise A-action. Evaluation and the constant-module functor are inverse exact equivalences, so applying them to complexes and their localization gives the claimed derived identification. This is an explicit application of the definition of the sheaf condition and localization, not an unexplained cohomological comparison. Algebraic closure of the fixed k implies the separable closure hypothesis. The corresponding Stacks source is Tag 0EZP; no stronger normal-scheme version is used.

Step 2 uses lem-pur-a1-direct-image precisely for the unit at the constant coefficient object, with B=Spec k, and def-pur-conventions to check that its finite ring is the same A. I read the blueprint source's steps 3 and 4: they distinguish the etale and pro-etale versions, so the delivery does too. lem-weil-pbc-affine-morphism-permanence(3) provides qcqs for Spec k[t] to Spec k. lem-weil-pbc-comparison-pullback gives a, lem-sf-comparison-pullback-exact(1) identifies the constant ring sheaves, and lem-weil-pbc-comparison-direct-image-canonical-mate states invertibility of exactly the mate b used here together with its counit normalization. The transpose equation is expanded using naturality and the triangle identity, so it concerns the canonical unit rather than an arbitrary object isomorphism. Finally thm-weil-pbc-site-comparison states full faithfulness on Dplus for all finite discrete module sheaves, which reflects invertibility. Both the coefficient unit and its pullback are degree-zero objects; their right derived direct images are bounded below. The finite discrete coefficient hypothesis holds throughout. The schemes are separated finite-type over k. The step is below 2000 characters and its comparison calculation is a substitution into the cited mate's formula, not a new independent comparison lemma.

Step 3 uses the complete statement of lem-pur-ordinary-kunneth-finite-ring, which explicitly permits arbitrary objects of the unbounded small-etale derived categories. X=T and Y=s satisfy separatedness and finite type, and A is precisely the prime-to-characteristic quotient of a valuation ring in that statement. lem-kun-pullback-constant identifies coefficient pullbacks, and lem-kun-tensor-unit states both canonical derived unit constraints for arbitrary complexes. I read def-kun-kunneth-map in full: it specifies unbounded derived module adjunctions and defines kappa as the adjunct of the tensor of pulled-back counits. Substituting eta_A into that formula and using the triangle identity makes the adjunct equal to the identity of p^*Q. Hence the composite in this step is exactly eta_Q. No finite projective resolution of Q is assumed; the cited Kunneth statement has no such hypothesis.

Step 4 uses the adjunction stated explicitly in def-kun-kunneth-map. The formula w=eta_Q^{-1} Rp_*(v) eta_P and the equality of adjuncts are written out, so fullness here is proved in the step. The bounded constructible categories are full subcategories by def-weil-pbc-constructible-complexes, and P,Q are in them by hypothesis; this places w in the required Hom set. This elementary adjunction calculation introduces no new node and assumes no dualizability of P.

Step 5 uses the composition and identity inverse-image maps actually specified in lem-weil-pbc-inverse-image-composition(2),(3), their module linearity from lem-weil-pbc-inverse-image-composition-module-linear(2), and the termwise derived construction of def-weil-pbc-derived-inverse-image. The identity map is A-linear because its adjunction unit and the identity direct-image identification are A-linear; equivalently naturality with respect to multiplication by each scalar gives linearity of its inverse. Applying the natural composition maps to w and using p i_c=id gives i_c^*p^*w=w. This is the required canonical identification, and taking c=a,b proves the exact equality of the item.

I checked every uses entry against the full statement of its node (C1,C3,C4), not a lemma hidden in its proof; citations.json quotes a literal substring for each occurrence. proof_deps is exactly the union of uses. The proof does not invoke stalk/internal-Hom interchange. For edge cases I checked zero P or Q, a=b, shifted finite modules, and nonperfect finite modules such as the residue field of A when n>1: the argument only needs the arbitrary-complex Kunneth theorem and adjunction, so these cases are retained. This also checks the vulnerable Tor-amplitude issue in E1/E4. No statement correction, dispute, new definition, duplicate node, new clause restatement, or hidden independent lemma in a long step remains. Sections B–E were checked with the cited statements open; the explanatory mate and Kunneth computations address the transport ambiguity of E5 directly. The retained proof has five steps, all shorter than 2000 characters.

## Resume verification

The required first dry run of the retained split found only that the step-2 coefficient quote was shorter than the citation gate requires. I replaced it with the complete first paragraph of def-pur-conventions: it explicitly identifies the algebraically closed finite-field base, the distinct prime, and the finite coefficient quotient used in step 2. I reread all fifteen proof-dependency statements and the six statement-dependency statements against the five steps, checked all sixteen quote pairs, and confirmed the proof dependency union. I also reread Varshavsky Lemmas 3.1.3–3.1.4 and the main-20261015 affine-line and Kunneth sources. The proof and item statement required no changes.
