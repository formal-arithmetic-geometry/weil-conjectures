# Worker report: lem-exc-direct-image-coproducts

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-direct-image-coproducts.json`: item, existing four-step split marked `split`; no new nodes.
- `citations.json`: verbatim statement quotation for each of the 14 cited step/node pairs.
- `searches.jsonl`: required LeanFinder, Loogle, grep and LeanSearch queries for the item.

## Attachments

None. I searched both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, its blueprint tag, and the relevant derived-direct-image/coproduct declaration. No finished declaration states this item exactly; the existing Lean metadata in the DAG is not a declaration in either read-only source checkout.

## WANTED

None. The local Stacks source contains Tag 0F11 (`lemma-finite-cd-mod-n-direct-sums`) and Tag 07K7 (`lemma-unbounded-right-derived`), which are the source route used by the split.

## What was wrong or incomplete

The imported node was still `unsplit` even though it already contained a complete acyclic-term proof and a prior split report. I retained that proof and its existing dependency route, marked the item `split`, and added the missing citation map. The imported proof deliberately replaces the blueprint's unsupported Godement/spectral-sequence paragraph with the Stacks 0F11 K-injective/acyclic-term argument; the canonical comparison maps and the empty-family case are made explicit. No statement correction was needed. The imported `uses_not_cited` entries are definitions used to parse the item's self-contained statement, while every substantive proof fact is cited in the four steps.

The item is not a Mathlib leaf: the required searches returned only general finite-coproduct or homological-complex declarations, no theorem asserting finite-cohomological-dimension derived direct-image preservation of arbitrary coproducts. The Loogle query was rejected because its first identifier was unknown; this is recorded in `searches.jsonl`, and the other three searches were run successfully.

## What I could not finish

Nothing remains for this stage-1 split. No Lean file was written and no compiler, Lake, build, or local DAG checker was run.

## Review by Q55

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, delivery-errors B–E, the fixed `sec-smooth-purity` chapter and `sk-prop-sf-cbc` unit, the current item node, and the current main-20261015 and master blueprint copies. The item statement agrees with its source: a qcqs morphism, a finite commutative coefficient ring, the stated uniform vanishing bound, ordinary unbounded étale derived categories, and the canonical coproduct map, including the empty family. I checked the source's Stacks Tag 0F11 proof at `literature/stacks-project/etale-cohomology.tex` around `lemma-finite-cd-mod-n-direct-sums` and Tag 07K7 at `literature/stacks-project/derived.tex` around `lemma-unbounded-right-derived`; the imported finite-ring adaptation keeps the same hypotheses and explains the coefficient-forgetting comparison.

Step 1 uses the Grothendieck-module-sheaf, additive-left-exact direct-image, exact/colimit-forgetting, module-to-abelian derived-comparison, filtered-colimit, enough-injectives, and derived-well-defined statements. I opened each cited node and `citations.json` copies its complete statement verbatim. These statements supply the abelian categories, exact coefficient forgetting, natural comparison of higher direct images, qcqs filtered-colimit theorem, finite-sum derived calculation, and the degree-zero identification. The finite-ring torsion observation, finite-subset filtered-colimit description, and finite-biproduct kernel/image calculation are elementary consequences written in the step itself; the zero ring is covered by the stated choice (N=1).

Step 2 uses the Grothendieck hypothesis, degreewise K-injective existence, and the derived-category coproduct theorem. Their statements explicitly provide termwise injective K-injective replacements and coproducts for arbitrary unbounded complexes, including the empty index set. I checked that no common lower bound is assumed.

Step 3 uses the injective-vanishing statement and the finite-cohomological-dimension acyclic-complex statement. The first gives (R^pF(I_s^r)=0) for injective terms; the second gives the unbounded right-derived comparison for uniformly bounded acyclic terms and its naturality. I checked the hypotheses one by one: the source is Grothendieck, the target abelian, (F) additive and left exact, and the item supplies the bound (c). The coprojection naturality equation is exactly the comparison's stated naturality.

Step 4 uses the derived-category coproduct statement for the target category. The degreewise (p=0) comparison supplies the complex isomorphism, and the chain-map equation plus the coproduct universal property identifies the localized map with the item's canonical map. The zero complex gives the empty-family edge case. I checked finite and singleton families reduce to the expected finite-sum and identity comparisons, while arbitrary sets and unbounded degrees are covered by the cited theorem.

I searched the whole DAG for the item, its Stacks places, and the dependency keywords before relying on the existing nodes; no new node or duplicate was needed. The proof dependency union exactly matches the four step `uses` lists, every cited id exists and is unmerged, and the blueprint fields and existing split report were retained. The item is the blueprint node itself (`blueprint.is`), so no created-node ancestry was required.
