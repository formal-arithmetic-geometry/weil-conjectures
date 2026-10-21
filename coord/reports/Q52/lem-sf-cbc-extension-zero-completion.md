# Stage-1 worker report: Q52

1. Files written:
   - dag/nodes/sec-smooth-purity/lem-sf-cbc-extension-zero-completion.json: statement retained verbatim; five assembly steps, 2182 characters of proof text.
   - dag/nodes/sec-smooth-purity/lem-sf-cbc-localized-strict-tensor-descent.json: new statement-only lemma, status unsplit, no Mathlib match.
   - citations.json: verified verbatim statement quotations for every parent step citation.
   - report.md and searches.jsonl: review and real search log. Sandbox construction scripts are delivery artifacts, not project tool edits.
2. Attachments: none. AlgebraicGeometry.Scheme.sfCbcExtensionZeroCompletion in lean/Sheaf/Paper/SfCbcExtensionZeroCompletion.lean:1086 ends in sorry at line 1109. Its tensor-descent and reduced-unit helpers also contain sorry. The WeilConjectures search found sheaf and finite-coefficient comparisons, not a finished exact theorem of the item.
3. WANTED: none. All sources actually used are present.
4. The assigned problem is the size and distribution of the proof. The statement is not disputed. Existing K-flat preservation and reduced-completion-unit arguments already have DAG nodes and are reused; the missing normalized strict tensor descent is now a separate obligation. Five unused statement dependencies were removed. No Lean file or unrelated field was changed.
5. Nothing required for this stage-1 delivery remains unfinished. The new lemma is deliberately statement-only for another worker; there is no claim of a completed Lean proof.

## Sources and route

I read GOAL.md, the three levels in SETUP.md, the worker role, stage-1 document and brief, both copies of delivery-errors B–E, the chapter sec-smooth-purity and unit sk-prop-sf-cbc records. I read the ancestor fix-lem-exchanges in master and its current main-20261015 proof under sec-six-functors-basics/sk-prop-sf-cbc. Construction Step 1's open factor and Step 2's naturality are the relevant route; this delivery makes those prerequisites explicit without changing the unit. The item is not its unit's key node, so no unit file is written.

For the new lemma I read Stacks sites-modules.tex Tag 0E8I, label lemma-j-shriek-and-tensor, with its Hom/tensor proof, and Tag 03DJ, lemma-extension-by-zero-exact. The new statement is an agent refinement of the sheaf tensor theorem: strict diagrams, derived localization normalization, uniqueness and coefficient-linear evaluation are not misrepresented as verbatim Stacks assertions. I read sites-cohomology.tex Tag 0941, lemma-derived-limit-is-ok, and proetale.tex Tags 099M/099N, lemma-naive-completion/lemma-pushforward-Noetherian-case, for the strict-limit and completion typing. I read the current sheaf comparison proof in main-20261015/sec-proetale-coefficients/sk-thm-pe-constructible-comparison/lem-cbc-proetale-extension-zero-comparison.proof.md.

The current blueprint's completed-open-comparison proof still contains a claim that ordinary open extension preserves countable products. This delivery does not use it. The parent already excludes that interchange. I use only the valid preservation statement of lem-cbc-ringed-open-flat-resolution, independently of its source pointer to that broader proof.

## Allocation of the old arguments

Old Step 1's exactness, flatness and unbounded K-flat preservation are the existing lem-cbc-ringed-open-flat-resolution. The signed total-tensor argument is also stated in existing lem-sf-ringed-open-total-tensor-kflat. Parent Step 1 uses the former and the existing resolution-existence theorem. New copies would be duplicates.

Old Steps 1–2's strict tensor construction and quotient compatibility, plus old Step 5's coefficient-linearity issue, are assigned to the new lemma. It constructs the actual strict chain comparison, fixes its descent by every K-flat representative, and identifies its evaluation in the coefficient-module category. Its scope contains no completion unit, completed extension, limit presentation or etale-origin witness.

Old Step 3's projection-adjunct normalization and inversion of the reduced unit already appear exactly in clause (i) of lem-sf-cbc-completed-pullback-unit-tower. Parent Step 3 specializes it with g=id and N=J_j K, and cites lemma-weil-pbc-adic-completion-reduction for invertibility inside D(P_n). This is reused work rather than a new duplicate.

Old Step 4's definition q=t u^{-1} and cancellation remain explicit in Step 4. Old Step 6's completeness and specified limit presentation remain there as applications of the completion reflector and Rlim(t). Old Step 5's derived sheaf comparison is still proved degreewise using exactness; Step 5 retains the actual witness pair and composite in the right direction. Old Step 7's naturality and transitions are in the new lemma and Steps 2–4, and its small-case checks are below.

The new descent task is substantial: form one chain map of strict towers, preserve local scalar actions, compare its finite coefficient evaluation, and descend through the localization comparisons on the K-flat class. Independence and uniqueness are assertions about the actual derived tower map. One cannot infer them from faithfulness of derived evaluations. The formula on representatives is a condition specifying the natural transformation, not a proof sketch in an unsplit node.

## Searches

All Mathlib searches were made with msearch.py and recorded exactly in searches.jsonl, with alternate natural-language phrasing. LeanFinder returned derived exact-functor localization and Tor ingredients for the new lemma, and ordinary completion/Henselian results for the item. Loogle '"SheafOfModules", "tensor"' returned presheaf tensor declarations; '"SheafOfModules", "extend"' returned none. The broad grep returned unrelated scalar-tower declarations, so I did not interpret its truncated results as absence; the targeted grep of Algebra/Category/ModuleCat for jShriek/extensionByZero/lowerShriek/KFlat/derivedCompletion returned no hits. LeanSearch returned module scalar extension, function extension by zero and ring localization. I read the presheaf tensor source and mapDerivedCategoryFactorsh in Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:61–70. These are ingredients, not exact or one-line matches. Both item and new node record only queries that actually ran.

I searched the whole DAG and blueprint by K-flat extension, completion unit, strict tensor, quotient transitions, extension comparison and localized tensor. I opened the plausible matches rather than checking titles alone. The imported blueprint does not state the new normalized local-site descent assertion, so same_as is empty. The ancestor is fix-lem-exchanges, with via [lem-sf-cbc-extension-zero-completion]. Existing generic tools are explicitly declared in split_report. None of the reused tools reaches this item through statement/proof edges.

## Not duplicates

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-etale-generic-immersion-projection: finite-coefficient etale locally closed projection and base change, not arbitrary ringed-site strict coefficient descent.

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-comparison-open-tensor-coherence: coherence of etale/pro-etale comparison with projection maps, not construction and normalization of the strict tensor map on one ringed site.

lem-sf-cbc-localized-strict-tensor-descent vs def-sf-open-reduction-coefficient-mate: defines a scalar mate; does not state invertibility, strict derived descent or representative uniqueness.

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-open-tensor-support: essential-image support only, explicitly no projection arrow or normalization.

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-open-pullback-support: pullback support only, explicitly no comparison map.

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-open-tensor-normalization: scheme pro-etale projection/base-change maps, also for system topoi; not the normalized descent equation for every K-flat representative on arbitrary localized ringed sites, with coefficient-linear evaluations and the unit-section formula.

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-integral-open-reduction-comparison: quasi-compact scheme opens, DVR completed coefficients and complete input with realized adjunctions; the new node has arbitrary local sites and algebra towers and no completeness assertion.

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-open-tensor-support-aux: invertibility of a transpose in supplied operation data, not strict-tower localization descent or coefficient-module evaluation.

lem-sf-cbc-localized-strict-tensor-descent vs lem-weil-pbc-ringed-slice-extension-tensor: the ordinary sheaf tensor isomorphism; no strict chain transitions, derived localization or varying-coefficient evaluated realization.

lem-sf-cbc-localized-strict-tensor-descent vs new-ringed-slice-extension-tensor-hom-data: ordinary sheaf Hom equivalence, not normalized derived strict-tower descent.

lem-sf-cbc-localized-strict-tensor-descent vs lem-weil-pbc-free-sheaf-flat: flatness of free sheaves, not derived extension/tensor comparison.

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-compact-support-proper-image-tower: transition compatibility after proper pushforward for DVR compactifications, not local-site descent or its uniqueness.

lem-sf-cbc-localized-strict-tensor-descent vs lem-pur-system-clopen-tensor-compatibility: proper/open clopen-pasting tensor equality over DVR quotients, not the local coefficient-tower construction.

lem-sf-cbc-localized-strict-tensor-descent vs lem-sf-ringed-open-total-tensor-kflat: chain-level total tensor and K-flat preservation, not localization descent with prescribed representative equation and S_n-linear evaluated scalar extension.

lem-sf-cbc-localized-strict-tensor-descent vs lem-pur-finite-projection-action-laws: associativity/counit laws for finite projection maps, not normalized strict coefficient-tower descent.

lem-sf-cbc-localized-strict-tensor-descent vs lem-asd-open-projection-exchange: etale geometric base-change/projection square, not arbitrary localized-site coefficient diagrams.

lem-sf-cbc-localized-strict-tensor-descent vs def-pur-system-tensor-mate-arrows: defines DVR system arrows; does not prove the arbitrary-local-site normalized descent and evaluated realization.

lem-sf-cbc-localized-strict-tensor-descent vs lem-cbc-rational-compact-support-coefficient-coherence: rational compact-support coefficient coherence, with no arbitrary ringed-site strict-descent assertion.

lem-sf-cbc-localized-strict-tensor-descent vs lem-cbc-ringed-open-flat-resolution: K-flat and termwise flat preservation, cited in Step 1; does not construct the normalized strict tensor comparison or its coefficient-linear evaluations.

lem-sf-cbc-localized-strict-tensor-descent vs lem-pur-etale-open-derived-tensor: constant-coefficient etale derived projection, without arbitrary local ringed-site towers or the universal representative normalization.

lem-sf-cbc-localized-strict-tensor-descent vs lem-amb-open-projection-composition: composition law for two etale opens, not strict varying-coefficient descent.

lem-sf-cbc-localized-strict-tensor-descent vs lem-pur-etale-sheaf-projection-map: ordinary lift-indexed etale sum projection and stalk calculation, not derived strict-tower descent.

lem-sf-cbc-localized-strict-tensor-descent vs lem-pur-varying-ring-tensor-support: system support only, explicitly without choosing a projection map.

## Review by Q52

I checked the parent against the available blueprint and Stacks sources, and kept its statement verbatim. The Noetherian hypothesis, finite generation of I, additive-torsion residue, finite quotient sets and perfect quotient complexes are unchanged. No finite-coefficient theorem is applied to the infinite ring A. The new lemma introduces its small site, ring, local object, coefficient algebras, transitions, derived localizations and normalization; every notion has a defining dependency. It is unsplit with empty proof/proof_deps and no hollow data or proof sketch. I compared every same-tag statement listed above in full.

Step 1 uses exactly what the three cited statements say: localization identifies both sites and constant rings; K-flat resolution gives flat terms and a quasi-isomorphism; ringed-open-flat-resolution explicitly preserves those properties and the resolution. Thus flatness preservation is not inferred just from a flatness definition.

Step 2 specializes the new statement to R=A_X, V=U, S_n=(P_n)_X. V is a site object because an open is weakly etale; the restricted rings are identified in Step 1; all quotient maps are algebra homomorphisms. Strict transition compatibility comes from the actual chain normalization. Evaluated maps are S_n-linear before scalars are forgotten. No flatness of A to P_n is required.

Step 3's cited clause (i) of completed-pullback-unit-tower explicitly quantifies over every N and says the strict reduced unit is invertible, with inverse the projection adjunct. Taking g=id_X satisfies its extra morphism parameter. The separate adic-completion-reduction statement explicitly puts that adjunct isomorphism in D(X_proet,P_n). Consequently coefficient linearity is not inferred from an A-linear isomorphism, and completeness of ordinary J_j K is not assumed.

Step 4's two cited statements give the completion reflector with the specified unit and derived limit formula, and the functorial exact Rlim on actual strict towers. Cancellation q u=t is elementary. Its evaluated inverse is u_n t_n^{-1}; the expression “reduced unit” is under exactly this tensor identification. Completeness is the reflector's output property. The specified limit presentation is Rlim(t), not an interchange of ordinary extension with Rlim.

For Step 5 I opened all five citations. The comparison node is only a sheaf assertion, so the step explicitly derives it degreewise using exactness. The site-comparison node gives a finite-limit-preserving left adjoint on module sheaves, hence exactness: kernels from finite limits and cokernels from the left adjoint. The two extension nodes give exactness and degreewise action. Therefore lower cohomological bounds and quasi-isomorphisms are preserved. With delta_n the resulting comparison, the actual pair is (j! L_n, q_n^{-1} J(alpha_n) delta_n), from nu_X^*(j! L_n) to the completed finite reduction, in the P_n-category by Steps 2–3. That is precisely the retained-witness definition; different n may have different lower bounds. No transitions among witnesses are introduced.

I tested identity opens, empty opens, K=0, zero coefficient rings, constant algebra towers S_n=R, and the nonflat quotient R to R/I. Identity opens give the identity tensor map under the canonical identifications, while the reduced completion unit is still the specified unit. Zero/empty inputs give zero comparisons. Nonflat quotients require the K-flat calculation; no underived tensor replacement is made. The new tensor lemma needs neither perfection nor finiteness; these hypotheses are used in the separate completion theorem. No source-error correction to the item is needed.

Every old argument is accounted for above, either as the new descent task, an already-existing named argument, or explicit assembly. No new node copies the whole item or an elementary cancellation. All parent steps are below 2000 characters and their sum is below 3000. I checked B1–B10 (form, sources, genuine searches, blueprint and attachment), C1–C8 (actual statement citations, generic tools and cycles), D1–D5 (substantive descent task and explicit assembly) and E1–E7 (hypotheses, correct coefficient objects and normalized maps). citations.json was verified as actual statement substrings, not proof quotations. I wrote no Lean, ran no compiler, and changed neither repository nor launcher files.
