# Stage-1 direct delivery: det-lem-int-ext-bound

## Files written

- `dag/nodes/sec-six-functors-basics/det-lem-int-ext-bound.json`: statement, status split, twelve proof steps; no Mathlib match.
- `citations.json`: retained 57 current verbatim step/node quotation pairs, checked again against the shared DAG.
- `report.md`: current Q153 author review and delivery report. The earlier proof, citations and search history remain available in the sandbox, including `previous-report.md` and `searches.jsonl`.
- No new nodes and no Mathlib leaves. No unit record is changed: this detail node is not the unit's key statement and the existing realized map already assigns unit steps 3 and 4 to it.

## Attachments

None. Read-only searches in `WeilConjectures/` and `Comparator/` for the exact blueprint tag, constructible Ext, uniform Ext and Ext bounds found no declaration giving the numerical stratum bound and qualitative consequent. The matches about extension by zero, constructibility and other functors' dimensions do not state this item. The upstream master checkout is reference material, never evidence of a closed proof.

## WANTED

None. The current blueprint, Stacks source and Bhatt–Scholze paper are present.

## Source error and current statement

STATEMENT-DISPUTED: the original main-20261015 item/unit proof uses the ordinary dual of a possibly torsion module. For X=S a geometric point, i=u=id, R=O_E, L=R/pi and K=R, Hom_R(L,R)=0 but Ext^1_R(L,R)=R/pi. The resolution [R --pi--> R] in degrees [-1,0] computes this explicitly. The correct dual is RHom_R(L,R), with cohomology in degree 1. The current existing `det-lem-int-ext-formula` clause (2) has already been corrected by its owner. Step 4 retains the explicit argument with this derived dual; the original unit's ordinary-Hom error is reported here rather than propagated. No neighboring node is edited.

The current shared item already makes its inherited `sk-def-sf-setting` global finite-field hypothesis explicit, with k algebraically closed. I retained its exact statement, all hypotheses, both conclusions, and the numerical +3 bound. Finite type over an arbitrary characteristic-p field would not by itself imply finite absolute cohomological dimension. Completed integral coefficients are kept distinct from discrete constant coefficients throughout. Torsion L and N are allowed; no finite-free hypothesis is added to either.

The reconstruction formula is Stacks Tag 099M (`proetale-lemma-naive-completion`), more precisely than the original proof's 099Q. The Roos triangle is Tag 08TC (`derived-definition-derived-limit`) in section 08TB. The proof uses the Roos triangle and Hom directly, so it does not need an unproved claim that every immersion inverse image commutes with inverse limits.

## Blueprint and duplicate searches

I read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-lem-int-ext.json`, the current main-20261015 item and unit proof files, and the current shared item. There is no blueprint_update superseding them. The twelve steps realize the unit's finite-reduction, support, tensor, sections, derived-limit and finite-filtration route (unit paragraphs 3 and 4); step 4 repairs the explicit ordinary-dual error in paragraph 1.

I retained the earlier whole-DAG/blueprint search account in `previous-report.md`, and reran the ancestor and whole-blueprint searches for vanishing of Ext, uniform constructible and integral Ext against the current DAG. The ancestor is the item itself; no other node states both clauses. The qualitative parent `sk-lem-int-ext` does not supply the numerical bound. No node is created, and `blueprint.same_as=[]` remains appropriate.

## Not duplicates

No new nodes. In particular, coefficient restriction/direct-image comparison is already `lem-weil-pbc-ring-sheaf-change-adjunction`, and extension of heart bounds to bounded complexes is already `lem-pur-bounded-heart-amplitude`. The previous long step is replaced by applications of these statements, not by newly named restatements of the item.

## Mathlib searches

Existing mathlib_searches and the actual sandbox search log are retained. I read their results and added the Q153 current receipt-backed item searches using LeanFinder, Loogle, LeanSearch and source grep, with two natural-language phrasings. Exact queries and results are recorded in the item and `searches.jsonl`; all current services responded. The hits are generic projective/injective dimension predicates, their Ext consequences, and derived degree predicates. I read Mathlib/CategoryTheory/Abelian/Projective/Dimension.lean lines 40–88: `HasProjectiveDimensionLT` and its consequences require the dimension bound, rather than proving one for constructible sheaves. Loogle's `ModuleCat.hasProjectiveDimensionLT_of_forall_finite` is a theorem about ordinary finitely generated modules and assumes the relevant Ext vanishing; it does not supply our geometric bound. The broad adic grep returns unrelated extension names, and the focused CategoryTheory/Sites grep has no constructible/proetale hit. None is an exact match or a one-line specialization to the item. No search is claimed for a new node because none exists.

## Review by Q153

I reread delivery-errors B through E whole and reviewed the current twelve-step split myself. For the item I read the main-20261015 proof and unit, Bhatt–Scholze Definition 6.5.1 and Lemmas 6.5.3–6.5.4, and the local Stacks text: 099M (naive completion), 09A6 (morphism comparison), 093M (completion flatness), 08JJ (perfect dual), 08JA (global sections of RHom), 08TC (derived limit), and 08J5 (truncation triangles). For the repaired coefficient step I also read 0D6D, 0D6E and 07A6 (composition of derived ringed-topos pullback/direct image and their adjunction). Tags and labels were checked in `literature/stacks-project/tags/tags`. There are no new nodes requiring additional source review.

1. `sk-lem-base-field-cd` states cd_ell(k)=0 for algebraically closed k. `sk-def-cd` explicitly asserts finiteness for schemes and morphisms of finite type over such a field. The schemes are Noetherian finite type, and the open immersion is qcqs. Its definition gives the empty supremum value zero. Thus c and s are finite nonnegative integers.

2. `sk-lem-int-integral-heart` clause (1) puts N in bounded constructible degree zero; `sk-lem-integral-models` clause (2) states derived completeness and classical first reduction over the completed ring. `det-prop-integral-criterion-reductions` gives all bounded constructible reductions for Noetherian X, and `sk-thm-pe-constructible-comparison` gives their classicality for the discrete Noetherian quotient rings. These statements apply to the actual functorial quotient tower, not arbitrary choices of reductions.

3. `lem-weil-pbc-standard-quotients-perfect` includes the O_E resolution and finiteness of its quotients; `lem-weil-pbc-completed-constant-sheaf-reduction` supplies flat completion and the quotient identification. Tensoring the two-term resolution with N gives degrees [-1,0], including its Tor term when N has torsion. Its finite coefficient action implies ell-power torsion.

4. `sk-lem-int-integral-heart` clause (3) gives dualizability and dual Tor amplitude [0,1]. The closed tensor-Hom adjunction of `def-sfb-derived-tensor-hom-adjunction-modules` and the duality triangle identities give the displayed evaluation isomorphism. `sk-lem-formal-closed-support` clause (1) supplies the actual closed-support adjunction. `sk-def-sfb-module-lower-shriek` gives exact open extension and its adjunction; `sk-prop-sfb-cartesian-coefficients` gives exact pullback. `lem-pc-derived-adjoint-functors` and `lem-weil-pbc-exact-functor-derived-functor` justify deriving that exact pair. `lem-pur-rhom-global-sections` applies on the small ringed site (in a common larger universe) and identifies Hom with zeroth hypercohomology, also after shifting. The finite-projective-only clause (2) of the support node is never applied to torsion L.

5. `lem-weil-l-adic-extension-integers-dvr` gives the DVR and `lem-sc-dvr-saturation-line-smith-normal-form` gives a finite-free kernel of a finite-free surjection. The resolution is chosen on each actual pro-étale trivializing object, not globally. Flat completion from `lem-weil-pbc-completed-constant-sheaf-reduction` preserves it. Dual and reduced constant matrices provide finite local models, so the exact definition `sk-def-sfb-constructible` and the discrete-coefficient comparison apply. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` supplies the coefficient tensor comparison. Testing against an arbitrary A_n-module verifies Tor amplitude [0,1] over the quotient, without pretending A_n is a field.

6. I opened the full statement of `lem-weil-pbc-ring-sheaf-change-adjunction`. It applies to arbitrary ring sheaves and includes inverse image, derived direct image, and compatibility with the derived adjunctions. This is the needed generic statement for completed B_T and finite A_n, rather than the discrete-constant-ring comparison. `sk-prop-sfb-cartesian-coefficients` supplies the two coefficient isomorphisms. Their reduction square commutes because both maps are pullbacks of the scalar quotient map. Hence the cited comparison includes the unit map in the support fibre. No flatness of B_T→A_n is used.

7. `sk-def-cd`, `det-pbc-conventions-module-cohomology` clause (3), and `sk-thm-pe-direct-image-comparison` give the heart upper bound c; the comparison requires qcqs j and bounded-below étale antecedents, both available. `lem-weil-pbc-ring-sheaves-grothendieck` and `lem-weil-pbc-derived-functor-negative-vanishing` give lower bound zero. `lem-pc-right-derived-functor-triangulated` supplies exactness and shift compatibility. `lem-pur-bounded-heart-amplitude` then applies to the class of classical A_n-module sheaves and the input interval [-1,0], yielding [-1,c]. The class contains zero and is closed under isomorphisms. The same comparison makes the direct image classical. This step now cites the existing general bounded-input theorem instead of hiding it inline.

8. `sk-lem-formal-closed-support` clause (1) states the precise i* of the fibre used here. `lem-sf-derived-homology-long-exact` gives upper bound c+1 and lower bound -1. Exact inverse images (`sk-prop-sfb-cartesian-coefficients`, `lem-weil-pbc-exact-functor-complex-cohomology`) preserve them. The comparison in `sk-thm-pe-direct-image-comparison` includes units and inverse images, so it also identifies the fibre and its étale antecedent; classicality is justified, not inferred merely from torsion.

9. `lem-weil-pbc-truncation-triangle`, K-flat tensor descent (`lem-weil-pbc-site-derived-tensor-descent`) and `lem-sf-derived-homology-long-exact` prove the tensor bound [-1,c+2] by the displayed finite filtration. The cone/tensor compatibility is written explicitly. `sk-prop-sf-comparison` supplies the derived-unit hypothesis of `det-pe-classical-derived-equivalence`. `sk-thm-pe-constructible-comparison` gives a bounded constructible étale antecedent for D_n, and `det-pe-finite-tor-comparison-noetherian` reflects its [0,1] Tor bound: S is qcqs and A_n is discrete Noetherian. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` identifies the tensor antecedent. This checks boundedness before applying bounded-below classical comparison; constructibility of Rj* is not assumed.

10. For the sections estimate, `sk-def-cd`, `sk-prop-sf-comparison` and `det-pbc-conventions-module-cohomology` clause (2) apply to the classical ell-power torsion cohomology sheaves. The finite truncation triangles, triangulated derived-functor theorem and long exact cohomology theorem give c+s+2. `lem-weil-derived-scalar-extension-restriction-adjunction` and `lem-pur-rhom-global-sections` identify the finite and completed coefficient hypercohomology groups by testing the coefficient unit. Thus no comparison for non-discrete completed coefficients is silently assumed.

11. `det-pe-products-derived` supplies products in the required module derived category; `def-weil-derived-limit` states the Roos triangle. Completeness itself was already proved in step 2. The product universal property identifies maps into a shifted product with the product of maps. Clause (iii) of `lem-weil-pbc-hom-into-triangle-exact` then kills maps to N[r] when r-1>b and r>b. This checks the one-degree loss, giving c+s+3, without a compactness or Mittag–Leffler assumption.

12. `det-lem-int-ext-formula` clause (1) gives a finite filtration with degree-zero stratum pieces for a sheaf C. `lem-weil-pbc-hom-out-of-triangle-exact` clause (i) states exactness at the middle Hom group; induction through those triangles preserves vanishing above the maximum of the piece bounds, with no extra shift. The empty filtration has d_0=0. The maximum is independent of N, as required.

I tested zero N and L, the empty scheme/complement and empty filtration, and a geometric point with L=O_E and L=O_E/pi. The torsion point detects the original ordinary-dual error. The two-term quotient remains in [-1,0] for both free and torsion N. All n are positive, and none of the bounds depends on n, ranks, torsion length or the second variable. There is no new statement needing a separate small-case test.

All 57 quotes are literal substrings of the corresponding current cited statements; every step use has one, and proof_deps equals their union. I inspected every non-elementary step for a hidden comparison or lemma; none is longer than 2000 characters. The formerly long coefficient/amplitude step now uses two appropriate existing statement nodes, whose hypotheses are checked above. The remaining short duality, cone and finite-induction calculations are written out. Generic off-unit tools are declared in split_report.tool_uses with their purposes; no maintainer-owned tool_uses is changed. The split follows the unit route and cites no SGA source. No Lean, compiler, Lake, shared project write or git command was used.

## Unfinished work

No mathematical argument remains for this one-level split. The resumed first dry run stopped on the missing current report; the permitted server check_dag command passed with no introduced finding. The completed report and item will now undergo the required complete no-push preflight, followed by direct delivery only after it exits successfully.
