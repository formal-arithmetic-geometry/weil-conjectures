# Q51: lem-trf-ind-etale-strict-local-invariance

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ind-etale-strict-local-invariance.json`: statement, split; no Mathlib match. Five proof steps; original mathematical statement preserved, with explicit definition citations added for base change and the canonical structural map.
- `citations.json`: 14 entries, covering every step/node citation with a literal excerpt from its statement.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `prepare.py` is an item-local preparation script.

No new nodes and no new Mathlib leaves. The initial sandbox had no node, split, report, or search log, only dispatcher marker files. I copied the item and retained all inherited search records, source information, creation metadata, and blueprint ancestry. The unit is not keyed by this item, so its realization fields were not changed.

## Attachments

No exact attachment for the item. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` both for the blueprint identifier and for strict-henselization, strict-localization, and ind-etale terminology. The current checkout does not contain the strict-henselization modules listed in older DAG audit records; those records alone cannot establish an attachment.

The already attached `Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` belongs to `thm-weil-pbc-weak-etale-strict-local`, at `WeilConjectures/RingTheory/ProEtale/HenselianLocalRing.lean:245`. I read the namespace and the local-map hypotheses inherited from its section, and its proof at lines 245–248. It is the ring theorem used in step 3, not an exact declaration of the scheme statement in this item.

## WANTED

None. Every mathematical source used is present locally.

## Audit of the input and route

The input is true; no STATEMENT-DISPUTED correction is needed. Its references to Algebra Tags 05WR and 0GIP point to a quasi-finite comparison and a strict-henselization base-change comparison, respectively. They require additional reasoning to yield this assertion, and importing a node that merely restated the ind-etale strict-local invariance would not split it. I instead use the affine pointed-neighbourhood presentation and Olivier's theorem, all already represented in the DAG. This does not replace the trace unit's contracting-correspondence/normal-cone route: it supplies a generic strict-local geometric tool underneath that route.

I read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, the current `main-20261015` unit and `lem-trf-local-term-locality.proof.md`, and the item's ancestral path through trace specialization and oriented nearby cycles. The unit explicitly rejects the incorrect internal-Hom stalk argument. This delivery introduces no such stalk identification and changes no coefficient category.

The blueprint searches for `ind-etale`, `strict henselization`, `strict local`, `henselization`, `local map`, and `092Z`, together with DAG tag/keyword searches, returned no blueprint node stating this complete item. `same_as` is therefore empty. The existing affine strict-local base-change comparison is a square/tensor-product comparison, whereas this item identifies the individual strict localizations and includes iteration. Its proof already demonstrates that the same generic affine-chart, stability, and Olivier tools are available. I reused those tools directly, rather than citing its proof as though it were its statement.

The existing generic tools in other units are explained in `split_report.tool_uses`. Olivier's theorem is already Lean-closed. I checked that none of the five principal theorem inputs has a dependency path back to this item, inspecting all statement and proof dependencies with a visited set. No new dependency cycle is introduced.

## Mathlib searches

The inherited Q34 searches remain verbatim. Fresh Q51 searches, executed through the required `msearch.py` command, are appended from its actual log:

- LeanFinder: “An ind etale morphism of schemes induces an isomorphism on strict henselizations at geometric points”. Returned étale definitions, postcomposition, formal unramifiedness, and algebra-map compatibility, not strict-local invariance.
- LeanFinder, second phrasing: “Strict localization of a scheme is unchanged along a weakly etale morphism at corresponding geometric points”. Returned étale-locus and localization facts, not this assertion.
- Loogle: `"strictHenselization"`, zero hits.
- grep: `strictHenseli|StrictHenseli|strictLocalization|StrictLocalization`, zero hits.
- LeanSearch: “Ind etale morphisms of schemes induce isomorphisms between strict henselizations at geometric points”. The service returned its rate-limit error; recorded as **unavailable**, not no match.

I read the returned declarations and their types. None is a generalization with a one-line specialization to the item. The negative result does not claim the project-specific Olivier theorem is absent; that theorem is explicitly reused.

## Not duplicates

No new nodes. Existing nodes were searched and reused; there are no new/existing-node pairs to justify.

## Review by Q51

I reviewed B–E of `coord/delivery-errors.md` against the delivered JSON and the actual local sources, not just the checker's expected fields. For the item I read Algebra Tag 05WR (`lemma-quasi-finite-strict-henselization`) and all of Tag 0GIP through the filtered-colimit case. For the proof actually delivered I read Etale Cohomology Tag 04HX (`lemma-describe-etale-local-ring`), including its affine-chart cofinal system; Algebra's strict-henselization and functoriality discussion; Proetale Tags 097J, 097K, 097M, 097N; and More Algebra Tag 092Z (`theorem-olivier`). There are no new-node sources to audit.

**Step 1.** The strict-localization definition gives the small colimit coordinate rings and their inverse-limit spectrum. The statement of strict-henselization functoriality, clauses (1) and (3), says exactly that those rings are strictly henselian local, that their structural maps send closed points to the chosen images, and that the canonical map comes from a local homomorphism satisfying the structural equation. The affine-spectrum definition explicitly states uniqueness of the inducing ring map. I wrote the local-spectrum open argument using a basic open and a unit, so no uncited neighborhood-invariance theorem is assumed. Restricting the structural square to the target chart and cancelling its open inclusion proves the needed A-linearity of h. The step is elementary relative to those cited statements.

**Step 2.** I read the entire statement of `lem-weil-pbc-strict-henselization-affine-chart-ind-etale`. It requires a geometric point, an affine open chart containing it, an isomorphism from the chosen ring spectrum to the actual strict localization, and compatibility of the structural ring map. The identity spectrum identifications and the factorizations from step 1 supply all of these, for both S and T. I then read `lem-weil-pbc-ind-etale-stability`: it explicitly supplies composition, the assertion that every A-map between ind-etale A-algebras is ind-etale, and ind-etale implies weakly etale. This is sufficient for the actual canonical h; merely knowing that A maps ind-etale to both rings would not suffice without that relative-map clause. No finite-presentation property of the colimit B is used.

**Step 3.** I compared the statement of `thm-weil-pbc-weak-etale-strict-local` with Tag 092Z and the Lean declaration. It requires the source to be strictly henselian, both rings local, and the map local and weakly etale. Functoriality supplies the first three; step 2 supplies the fourth. It does not require the target to be of finite presentation. The spectrum definition supplies contravariant functoriality, and the same functorial structural equality shows the resulting isomorphism and its inverse are over S. Thus this is the prescribed canonical map, not an isomorphism obtained with an unrelated residue-field choice.

**Step 4.** The affine fibre-product node's statement gives both the tensor ring and the projection homomorphisms. Ind-etale stability explicitly covers arbitrary base change. I used its C-algebra statement with C the ring of an affine open inside the preimage of U; C is unrestricted. I wrote out why the indicated open of T' is V times over U with W, using the fibre-product definition. Consequently every base-changed geometric point has the required affine charts. No quasi-separatedness, affine-intersection hypothesis, or finite-type assumption is hidden in this step.

**Step 5.** The structural-map definition identifies j with the canonical limit-projection composite. The affine-chart ind-etaleness lemma therefore applies to its map A to H_S. The local-spectrum argument implies the whole affine source maps into U, which supplies the local affine hypothesis everywhere on L. Functoriality clause (1), included in the literal citation, supplies the closed lift from the relative separable closure inside the original Omega. Applying the preceding argument to j gives exactly L localized at that lift mapping to S localized at s, hence to L. I did not identify Omega with a residue field: Omega may have transcendence over the image residue field.

For small cases I checked the identity map, an open affine restriction, a finite separable field extension with compatible embeddings into one algebraic closure, an infinite separable algebraic field extension (which still gives the same separable closure), and the structural strict-localization map. Empty source schemes give a vacuous pointwise assertion; base change may likewise produce empty charts away from the chosen point, but the chart actually used contains the chosen geometric point. Purely inseparable field extensions are excluded by ind-etaleness, so their contrary strict-local behavior is not a counterexample. Nonreduced base rings cause no step to assume reducedness or injectivity of a structural ring map.

I checked all 14 citation excerpts are verbatim substrings of their cited statements. The five step lengths are 1409, 656, 616, 1210, and 1089 characters: no non-elementary step exceeds 2000 characters. The steps carry the argument; no elementary fact, clause of the item, or duplicate has been made into a node. No SGA source is used.

## Unfinished work

None in the one-level split. Its reused dependencies retain their existing statuses and are not edited by this delivery. Required server dry run and direct push follow this report.
