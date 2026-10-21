# Worker report: lem-sfb-ring-localization-sheafification

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-ring-localization-sheafification.json`: statement, split into six proof steps; not a Mathlib leaf. All hypotheses, fraction formulas, universal-property clauses and the final canonical isomorphism are retained. The only statement edits add explicit definition citations for the site and ordinary localization.
- No new nodes and no new Mathlib leaves.
- `citations.json`: thirteen verbatim statement quotations, one for each cited node at each proof step.
- `searches.jsonl`: the actual Q17 search-command records; the item's inherited Q37 searches were retained verbatim.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and localization/sheafification concepts. There is no project declaration stating the full item exactly. The sectionwise localization construction is already recorded by `def-weil-pbc-ringed-section-localization`; its generalized public ring construction is in `lean/Sheaf/CategoryTheory/RingedSectionLocalizationOfUniverses.lean`. The closely relevant `LocalizationRings.unit_isUnit`, `hom_ext`, `lift` and `lift_unit` at `lean/Sheaf/CategoryTheory/LocalizationInverseImageCoherence.lean:1319–1378` are private helpers in the Sheaf tree, not a public declaration of this item in WeilConjectures. They provide no qualifying ATTACH. No Lean was written, compiled, or otherwise changed.

## WANTED

None. The necessary Stacks source and blueprint are present locally.

## Problems in the imported material and changes

The item was unsplit, with no proof or proof dependencies. Stacks `sites-modules.tex`, Tag 0EMC (`lemma-simple-invert`), states the sheaf-ring universal property and explicitly omits the proof. Thus `proof_origin.by` is `agent`: the delivery supplies that omitted proof rather than treating the tag as a proved step. The ring-object formulation also requires the section-ring reconstruction; a ring-object definition alone would not justify it. The proof explicitly cites the existing reconstruction statement and the existing normalized ring-sheaf-to-ring-object statement.

No mathematical statement dispute was found. The exact equality relation includes a killing power of t, so zero divisors do not invalidate the statement. No assumption of a final object is used: a global section means a compatible family of sections over every site object.

I checked the actual tags against `literature/stacks-project/tags/tags`: `algebra-definition-localization` is 00CO and `algebra-proposition-universal-property-localization` is 00CP. An initial draft had these numbers shifted by one; the delivered node uses the corrected tags.

## Existing material, blueprint, and Mathlib searches

I read `dag/chapters/sec-proetale-coefficients.json`, `dag/units/sk-prop-sfb-cartesian-coefficients.json`, and the current finite-free blueprint proof in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/sk-prop-sfb-cartesian-coefficients-finite-free.proof.md`. The localization model supplies the inverting-ell sentence of its proof, through the existing `lem-sfb-localized-basis-coefficients`. The item's inherited ancestor, via-list and exact proof-place reference are retained. Blueprint searches for `localization sheafification ring sectionwise`, `ring localization`, `0EMC`, `section-ring`, and `localization away` found no imported blueprint node stating this generic localization-sheafification result; `same_as` stays empty. The DAG concept and tag searches found the construction, the ordinary universal property, and the ring-object comparisons, which are reused instead of creating nodes.

I ran msearch.py for Q17 using LeanFinder, Loogle, grep and LeanSearch, then a second semantic phrasing and a Sites grep. The hits were ordinary ring localization, scheme structure-sheaf fractions, the TopCat localization presheaf, and the categorical localization giving sheafification. I read `Mathlib/Topology/Sheaves/CommRingCat.lean:82–107`, `Mathlib/RingTheory/Localization/Away/Basic.lean:147–159` and `Mathlib/RingTheory/Localization/Defs.lean:508–563`. The TopCat construction is only for topological spaces and is not the arbitrary-site sheaf universal property here. The ordinary lift, its formula, and homomorphism extensionality are already the Mathlib leaf `lem-weil-pbc-localization-away-universal-property`; this split cites it directly. No Mathlib search is invented or silently replaced. All search services answered successfully for the new Q17 searches.

## Generic tool uses

`det-def-sfb-ring-object-sheaf` supplies the normalized internal ring structure of a ring sheaf and preservation by ring sheaf maps. `def-weil-pbc-internal-abelian-sheaf-module-equivalence` supplies its explicitly stated section-ring reconstruction for an internal commutative monoid. These are general tools for the coefficient-basis argument, not replacements for any unit step; they are declared in `split_report.tool_uses`. The other off-unit ingredients are definitions or existing Mathlib leaves. No SGA reference is used.

## Not duplicates

No new node was created. In particular the already existing ordinary localization definition and universal-property leaf, `def-weil-pbc-ringed-section-localization`, `det-def-sfb-ring-object-sheaf`, and the internal-to-sectionwise module equivalence are reused; no subsidiary node restates a clause of this item.

## Review by Q17

I read the item against Stacks `sites-modules.tex` Tag 0EMC (`lemma-simple-invert`) together with the paragraph defining the localization presheaf immediately before it. Taking the multiplicative subpresheaf S(U) to be powers of t_U gives exactly the formula for restriction and the universal property used by the item. I read `algebra.tex` Tag 00CO (`definition-localization`, including the preceding quotient and operation formulas) and Tag 00CP (`proposition-universal-property-localization`, including its proof), and `sites.tex` Tag 00YR (`section-sheaves-algebraic-structures`), especially (alpha), (beta), (gamma), (epsilon). These establish the intended ring-valued, small-site meaning without enough points or nonzero-divisor assumptions. There are no new-node source statements to audit.

For step 1 I opened the statements of `def-weil-pbc-internal-abelian-sheaf-module-equivalence`, `sk-def-sfb-sheaf-tensor`, `det-def-sfb-ring-object-sheaf` and `def-weil-pbc-sheafification`. The first actually specifies the reconstructed section-ring sheaf and its multiplication and unit; I do not take reconstruction from the mere ring-object definition. The second states strong symmetric monoidality of sheafification, which verifies the reconstruction's monoidal-local-equivalence hypothesis. Smallness relative to the coefficient universe is already a hypothesis of the item. The third gives the unique-extension normalization of the ring structure and preservation of morphisms. Evaluation of a multiplication-preserving map on r tensor s proves that it preserves section products; conversely the cited normalized construction gives an internal morphism. Uniqueness of extension through the sheafified tensor and the sheafified integer unit recovers the original internal structure, so no arbitrary alternative ring structure is introduced. This is a short application of existing statements, not an uncited new reconstruction theorem.

For step 2 I opened `def-weil-ring-localization-away` and `lem-weil-pbc-localization-away-universal-property`. The definition states the full fraction relation and both operations, and the theorem gives exactly a unique lift to a commutative target making t invertible, with the fraction formula and extensionality on r/1. Restriction of t_U is t_V by globality; the target localization makes t_V invertible, so each application has its unit hypothesis. Identity and composition are checked on r/1 before applying the explicitly cited uniqueness assertion. There is no unsupported appeal to functoriality or cancellation.

For step 3 the sheafification definition supplies the ring unit sigma and its target; `det-def-sfb-ring-object-sheaf` supplies the commutative internal structure and morphism passage, with exactly the sheafified tensor convention. The inverse is constructed as sigma_U(1/t_U), not obtained by a sectionwise localization assertion about aP. Its compatibility follows from the restriction formula already proved. The ordinary localization definition supplies the multiplication identity; both products equal 1, and this remains valid in the zero ring.

For step 4 I reread the ordinary localization universal-property statement. The image f(t) has a global inverse by hypothesis and hence a section inverse over every U. That is precisely its required hypothesis. Its fraction formula gives g_U; naturality is proved by comparing two actual ring homomorphisms to D(V) on every r/1, not by assuming a sectionwise lift glues automatically. This uses only the theorem's stated extensionality, not anything in its proof.

For step 5 I checked that the sheafification factorization is in rings and that D is already a sheaf. The normalization of the internal structure is the statement of `det-def-sfb-ring-object-sheaf`. Existence follows from the sheafification definition; uniqueness first identifies h sigma objectwise by the cited ordinary universal property, and only then uses sheafification uniqueness. Thus an internal factorization is tested in exactly the same morphism category, with no hidden enough-points or local-surjectivity assertion.

Step 6 is elementary uniqueness of universal objects: gamma and delta each have their displayed composites with the two units, and both composites are shown to be identities by the corresponding established universal properties. It cites no new lemma and adds no hypothesis. I checked the order of both compositions and the uniqueness condition gamma eta = j.

Small-case checks: t=1 gives the original sheaf by the same universal property; t=0 makes each fraction ring the zero ring and only permits target sheaves in which 0=1; a nilpotent t behaves the same (for example Z/4 and t=2). A zero ring is permitted in every ordinary localization step. On the empty site the compatible families and natural transformations have the required vacuous unique values. The proof also applies without a terminal site object and never invokes a point or a stalk. Every non-elementary step cites the facts it uses; the longest is 1215 characters, so none exceeds the long-step threshold. I checked B1–B10, C1–C8, D1–D5 and E1–E7 of delivery-errors against the actual node and its sources: no new statement-only-node, duplicate, weak Mathlib match or relabelled clause is introduced, and the proof explicitly carries the omitted 0EMC argument. I corrected the Stacks tag numbers and removed repeated definition dependencies introduced by draft regeneration.

## Unfinished work

None in the stage-1 split. Independent maintainer review remains part of the project delivery process.
