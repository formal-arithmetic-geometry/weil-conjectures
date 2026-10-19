# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-henselian-algebra-local-model.json`: split statement; its statement and statement dependencies are unchanged. Nine steps, all citing existing nodes. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim cited-statement record for each step/node pair.

## Attachments

No attachment for the item. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for its blueprint tag, finite/henselian combinations, henselization, and strict local models. `RingTheory/ProEtale/IntegralLocal.lean` discusses the finite-product theorem but does not state this item's finite-type strict-local model. The PiOfFinite section there is empty. The closed existing descent declaration `CommRingCat.exists_isPushout_of_finitePresentation`, `WeilConjectures/Mathlib/Algebra/Category/Ring/FinitePresentation.lean:216`, belongs to `lem-kun-fp-algebra-descent`, which is cited rather than duplicated. Its whole proof, through line 254, was read; the existing node records the closed audit.

## WANTED

None. The ILO volume and the Stacks sources needed here are present.

## What was wrong or missing

The item was statement-only, not a completed split. Its statement is correct, including imperfect separably closed residue fields and nonreduced finite algebras. The reference to 05WP is a valid possible approach but not an argument that constructs a model. The split instead descends a finite presentation to an etale neighbourhood and identifies the resulting strict localization by ind-etale invariance; it does not claim the ordinary local ring of the finite-type model equals C. This is below the blueprint unit level and preserves the partial-algebraization route used by the parent.

The existing `lem-weil-pbc-colimit-category-fp-algebras` explicitly gives only parts (2) and (3) of 05N9. I did not use it for existence of a descended algebra: that would be C4. Step 5 uses `lem-kun-fp-algebra-descent`, whose statement includes existence and allows a filtered category. Likewise `lem-weil-pbc-strict-local-base-ind-etale` concerns a special field base change, so it is not used for S -> H. Step 7 uses `lem-trf-henselization-prime-ind-etale`, whose actual statement gives the required map, after Step 6 identifies H with the ordinary henselization of S_p.

## Unfinished work

None for this one-level split. Existing supporting nodes retain their existing states. Only stage 1 was performed: no Lean writing, compilation, Lake, live project edits, or agents.

## Not duplicates

No new node was created. Searches of the whole DAG by 04GH, 05WP, 04GN, 04GW, 0BSL, 05N9, henselization, finite algebra, finite presentation, and Noetherian localization found the reusable inputs cited in the split. `tools/blueprint_refs.py ancestor` gives `lem-per-artin-gabber-affine-curve`; blueprint searches for henselian, henselization, henselian algebra, finite algebra, and finite presentation found no blueprint statement of this item. Its existing ancestor/place/via binding is retained and same_as is empty. The fixed chapter and unit records were read and left unchanged: this item is not the unit's key node.

## Mathlib searches

The original five search records in the repository item are retained. Fresh searches are logged verbatim in `searches.jsonl` and added with exactly the same tool/query strings to the item. I read all returned hits. LeanFinder was tried in two different formulations. The natural-language hits include finite-presentation descent infrastructure, HenselianLocalRing, finite residue-field results, finite-type Noetherianity, and etale-algebra definitions; none supplies the finite-type strict-local model. Loogle with the two expected names returned no hits. The broad lowercase grep returned no hits; a second search for `Henselian` in RingTheory returned Henselian.lean, which I opened together with RingTheory/FinitePresentation.lean. The residue-field `finite_of_finite` hit concerns finiteness as a set, not module-finiteness of the extension, and is not misidentified as the needed residue-extension lemma. No service failure was recorded as absence.

## Review by N3

I read the source of the item in ILO, Expose V 2.2.7 (printed pp. 65–66): a finite algebra over the Noetherian henselization is finitely presented and hence descends to a finite-type algebra over the underlying base. I checked its strict-local interpretation against the parent split and ILO Expose XVII 6.5. The actual extra work needed for this item's statement is to select a local factor using the completed tensor and to identify the descended model's strict localization. I read Stacks algebra.tex 04GH (`lemma-finite-over-henselian`), 0BSL (`remark-construct-sh-from-h`), 04GN/04GV/04GW (henselization and its etale presentations), 05N9 (`lemma-colimit-category-fp-algebras`), 00MC (`lemma-completion-faithfully-flat`), 05CK (`lemma-faithfully-flat-universally-injective`), 00FN/00FP (Noetherian permanence and finite presentation), and 0GIP (`lemma-base-change-strict-henselization-quasi-finite`), including its filtered-colimit argument; more-algebra.tex 06LJ; and etale-cohomology.tex 04HX. I also checked the definition node's idempotent formulation rather than assuming it was the root-lifting formulation. There are no new statements to check against sources.

Step 1 uses exactly the universal property in `def-weil-pbc-henselization-at-prime` and the idempotent definition in `def-weil-pbc-henselian-terminology`. The field k is henselian because its maximal ideal is zero. The resulting LOCAL map H -> k induces an injection of residue fields, and its composite with k -> kappa(H) is the identity; this proves the residue identification without taking it from a definition that does not state it. This is elementary and is marked so.

Step 2 checks the Noetherian hypotheses in order: D Noetherian plus R0 finite type, then localization, then ordinary/strict comparison using the trivial residue closure. The uniqueness clause of `lem-wf-strict-henselization-finite-lifts` says the finite local etale lift of k/k is H itself. Its colimit statement therefore gives H=A^sh. `lem-sc-strict-henselization-noetherian` applies to A. `lem-exc-affine-strict-local-ring-comparison` identifies the geometric and algebraic rings, with compatible R0 structure. It applies to the whole affine scheme and an algebraic closure of k; since k is separably closed its separable closure inside that field is itself.

Step 3 opens the statements of the completion-flatness, universal-injection, and finite-henselian-product nodes. Each says precisely what the step uses: completion is faithfully flat for NOETHERIAN LOCAL H; the module-injection statement applies to C without flatness of C; the product statement supplies henselian local finite factors. Nonzeroness of the completed tensor excludes the empty product. A product of at least two nonzero factors has a nontrivial idempotent, which the injection preserves and a local target forbids. This is why completion-locality selects exactly one factor; no unjustified assertion that locality descends along an arbitrary flat map occurs.

Step 4 uses the product node's explicit finite residue-extension clause, and the statement of `lem-kun-sep-closed-finite-extension-sep-closed`, so it does not assume k is algebraically closed or that L=k. Module generators are algebra generators by a written one-line linear-combination argument. The two cited Noetherian/finite-presentation nodes then give C Noetherian and finitely presented over H, under hypotheses already established.

Step 5 uses `lem-weil-pbc-strict-henselization-triples` for the actual filtered colimit, not merely its definition. Restricting to representatives of finite-presentation algebras and the set of their point data gives a small diagram. `lem-kun-fp-algebra-descent` supplies an algebra at a stage and its base-change isomorphism for this filtered diagram. Its statement does not require a directed-poset replacement. The stage is etale over R0, and the finite-presentation clause of `lem-weil-pbc-etale-algebra-finite-presentation-localization` supplies the finite type needed for F/R0. Composing finite generating sets is elementary and is written out.

Step 6 checks that the selected residue embedding into k, over k itself, is an isomorphism. It uses the etale stage's finite presentation to view its map as the constant ind-etale diagram. The statement of `lem-trf-ind-etale-strict-local-invariance` supplies the canonical S-compatible strict-local comparison, and `lem-wf-strict-henselization-finite-lifts` and the affine comparison supply the S-compatible ordinary/strict comparison for S_p. This identification is necessary before invoking the henselization-prime ind-etale lemma. The repeated residue argument is the elementary argument of Step 1, with its definitions cited again.

Step 7 takes exactly S -> (S_p)^h from `lem-trf-henselization-prime-ind-etale`, not any unsupported claim about an arbitrary colimit leg. The tensor identity from Step 5 makes Spec C -> Spec F its base change. The explicitly stated arbitrary-base-change clause of `lem-trf-ind-etale-strict-local-invariance` gives the comparison of strict localizations. This generic local-algebra tool is used as a black box, not proved by its internal proof.

Step 8 is elementary: contraction gives a prime over q, and F/z injects as a k-subalgebra of the already finite extension L. A finite-dimensional domain is a field by injective multiplication being surjective. Thus the point is CLOSED, not just a point specializing to q. Taking an algebraic closure of L gives the geometric point. These are consequences of data established in preceding steps, so no additional cited theorem is hidden.

Step 9 uses the henselization universal property to identify C with its own ordinary henselization; `lem-wf-strict-henselization-finite-lifts` then makes its strict henselization equal to C since L is separably closed. The affine comparison is the geometric identification. Combining with Step 7 gives the actual strict local ring of F at z, over F and therefore R0. The final D-finite-type assertion follows by concatenating the two finite generating sets. Every object in the conclusion is now constructed.

I checked B–E on the actual statements: no new node restates the item or one clause; no mathematical theorem is cited through a definition alone; all cited statements were opened; no SGA is used; no target, chapter, or unit statement is changed. Generic off-unit tools are declared in split_report.tool_uses, leaving maintainer-owned tool_uses untouched. All nine proof steps are shorter than 2000 characters, and the comparison in Step 6 is a direct application of existing comparison statements, not an inline unsplit lemma.

Small cases: C=H gives a model with the expected strict local ring. C=0 is excluded by the nonzero-completed-tensor hypothesis. C=H x H is excluded by the idempotent argument, including after completion. Over a separably closed imperfect field k in characteristic p, C=k[u]/(u^p-a) with a not a p-th power has residue a nontrivial finite purely inseparable extension; the proof retains L rather than incorrectly setting it equal to k. A nonreduced example C=H[e]/(e^2) is permitted: no domain or reduced hypothesis was used in Steps 3–7 or 9. The domain in Step 8 is only F/z, which is a domain because z is contracted from a maximal ideal. A zero-dimensional base A=k is also covered, with completion k and the same argument.
