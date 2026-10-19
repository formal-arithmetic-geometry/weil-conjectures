# Q55 worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-unbounded-sections-localization.json`: assigned statement, split into three proof steps; no new DAG nodes.
- `citations.json`: verbatim statement quotations for every cited node in every proof step.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the exact item id and for derived-section, localized-site, K-injective restriction, and unbounded-cohomology declarations. The project source has no sorry-free declaration stating this item. The existing derived-global-sections declarations concern schemes or specific sites and do not state the arbitrary ringed-site localization comparison.

## Wanted sources

None. The source `literature/stacks-project/sites-cohomology.tex` is present; I read Tags 08FI and 0D6F and the displayed K-injective proof.

## What was wrong or changed

The imported item was statement-only with an empty proof. Its statement agrees with Stacks Tag 0D6F, including arbitrary unbounded complexes and the natural degreewise identity. I supplied the missing proof steps and retained all hypotheses and statement dependencies. No `STATEMENT-DISPUTED` issue or source error was found. No new node was created: the existing `lem-pur-kinjective-restrict-localized` states exactly the auxiliary K-injective restriction fact needed by the proof.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs. I checked the closest existing statements: `lem-weil-pbc-cohomology-over-object-localization` only treats abelian sheaves in nonnegative degrees; `lem-pe-injective-complex-slice-section-model` is a bounded-below pro-etale comparison; and `lem-sc-derived-k-injective-restrict-open` is the open-ringed-space specialization. None states this arbitrary ringed-site, unbounded derived comparison.

## What I could not finish

Nothing remains in the stage-1 split. The required server dry run and direct delivery are the remaining operations.

## Review by Q55

I read the assigned item, its unit `sk-prop-ctf-finite-comparison`, the ancestor blueprint proof `det-ctf-finite-comparison-localizing`, and the expanded `det-pe-unbounded-classical-direct-image` source paragraph. I also read delivery-errors B through E, the stage-1 brief, GOAL, SETUP and DAG-sync instructions. The item’s blueprint place is the direct-image comparison clause that identifies evaluation at an object with cohomology on the localized site.

For Step 1 I read the complete statements of `sk-def-sfb-derived-categories` and `lem-pur-kinjective-restrict-localized`. The former explicitly says unbounded total right derived functors are computed termwise on K-injective resolutions; the latter states that restriction of a K-injective module complex to `\mathcal C/W` is K-injective. These hypotheses match the item’s arbitrary small ringed site and object `W`, so both derived evaluations can be computed from the indicated representatives.

For Step 2 I read the complete statement of `def-pur-localized-ringed-site`, which defines `(\mathcal F|_W)(V\to W)=\mathcal F(V)` and restricts morphisms sectionwise. At `\operatorname{id}_W` this gives the displayed equality of terms, and functoriality gives equality of the differentials. The step is therefore elementary once that definition is cited.

For Step 3 I checked that the identity of complexes commutes with every chain map. The right-derived-functor convention from `sk-def-sfb-derived-categories` then supplies the canonical descent to `D(\operatorname{Ab})`; applying homology gives every integer-degree comparison. The argument never uses boundedness. I checked the zero complex, an object equal to the final object, an empty slice, and complexes unbounded in both directions. All proof steps are below 2000 characters, every non-elementary use is cited, and `proof_deps` is exactly the union of the step uses. No Lean, compiler, Lake, build, or shared-file mutation was performed.
