# Q21 stage-1 delivery: lem-sf-finite-proetale-pushforward-constructible

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-finite-proetale-pushforward-constructible.json`: statement node, split in five steps; not a Mathlib leaf. Its statement, statement dependencies, provenance and blueprint ancestry are preserved. Five fresh searches are appended to the inherited searches.
- `citations.json`: ten entries, one per cited node per proof step, with literal substrings of the cited statements.
- `report.md`: this report. `searches.jsonl` is produced by the required msearch command.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is not the key node of its unit.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the exact item id, intrinsic constructibility, finite-ring origin and bounded-constructible direct image. `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar` in `SixFunctors/ProEtale/FiniteCoefficient/Derived/Stability.lean:155` proves the separated case: the surrounding variables explicitly include `[IsSeparated f]`. It also starts with the etale-origin predicate, so it does not itself give the full intrinsic origin and canonical-comparison clauses. It is not an attachment to this nonseparated item. The existing finite-ring intrinsic-origin theorem belongs to its already present node, not to this item. No Lean was written, compiled or built.

## WANTED

None. All sources used are available in the repository.

## Findings and corrections

The starting item was unsplit and its source already prescribed exactly the appropriate route. Its statement is mathematically sound; no STATEMENT-DISPUTED or statement correction is needed. In particular arbitrary finite commutative B is retained, the annihilator is allowed to be composite, and neither finite Tor amplitude nor separatedness has been introduced.

The proof now supplies the missing qcqs check and specifies the actual comparison arrow. It obtains an input marking alpha: nu_X^*L -> C and defines the displayed output map as Rf_proet,*(alpha) after the specified comparison mate. It does not substitute an arbitrary isomorphism between the same objects. The forward direction of the same finite-ring equivalence then supplies intrinsic output constructibility and boundedness. It does not infer constructibility from an etale-origin definition alone.

The main-20261015 ordinary/compact cohomology definition, the chapter record and the unit `sk-def-sf-admissible` were read. The unit is a definition with no proof steps. The parent `lem-sf-integral-direct-image-constructible`, step 4, explicitly needs this finite-ring comparison/constructibility result. The split realizes that need and the ordinary direct-image codomain of `def-weil-ordinary-compact-cohomology`. I did not change a unit or chapter route. The nonseparated etale theorem is already a node; repeating its finite affine-cover proof here would duplicate its work.

## Searches and reuse

I searched the whole DAG for Stacks 09AK, 09AL, 09A6 and constructible direct images, read the statements of the resulting comparison/origin candidates, and used the existing general finite-ring node instead of the narrower coefficient-stage node `lem-sf-proetale-constructible-origin`. Blueprint searches with `tools/blueprint_refs.py` included `constructible direct image`, `09AL`, `09A6`, `proetale constructible`, and `finite-type constructibility`; none states all clauses of this item. The inherited `blueprint.from` place and via list remain applicable and `same_as` is empty. No new nodes were created, so there are no new/existing duplicate pairs requiring resolution.

Five Mathlib searches ran through msearch.py and are logged: two different LeanFinder phrasings, LeanSearch, Loogle and grep. Every service answered. The first semantic search found small-etale site definitions and Chevalley's constructible-image theorem, concerning subsets rather than sheaves. The second found ordinary module sheaf pushforward and its adjunction, not a derived constructibility theorem. LeanSearch found etale algebra and site definitions; Loogle gave no hits. The grep hits were read in Mathlib's Sites/Proetale.lean and Sites/ElladicCohomology.lean and Morphisms/FinitePresentation.lean: they define the sites, the ell-adic coefficient sheaf/cohomology and Chevalley's theorem; none states the item or specializes to it in one line. The original source-node search records are retained rather than represented as new Q21 searches.

## Review by Q21

I read delivery-errors B through E in full against the actual item and its proposed dependencies. There are no new nodes, hence no statement-only-node, hollow definition, Mathlib-leaf, or duplicate-node issue. Each proof step is below 2000 characters (the longest is the explicit mate step, under 1000), and no elementary derived or geometric fact has been turned into another node.

For the item's sources I read Stacks proetale.tex at `lemma-morphism-comparison` (09A6), `lemma-compare-constructible` (09AK), and `lemma-compare-constructible-derived` (09AL), including their proofs. I also read Bhatt--Scholze Theorem 6.7.1 and Lemma 6.7.2 on page 55 of the PDF. The latter's argument uses finite-coefficient etale finiteness and site comparison; its completed coefficients are not silently substituted for our finite constant coefficients. The assembly is honestly marked proof_origin.by=agent, because the present all-finite-ring, bounded and nonseparated formulation combines existing nodes. For etale finiteness I read the exact current statement of `thm-dg-finite-type-constructibility`, its main-20261015 blueprint statement and proof, and its blueprint_update. That statement explicitly allows nonseparated morphisms and an arbitrary finite ring with an invertible annihilator. It is exactly the named input of this item's source.

Step 1 uses the statement of `lem-weil-pbc-finite-type-over-noetherian`, not a claim about etale cohomological dimension. I checked Stacks 01T6, `morphisms.tex:lemma-finite-type-noetherian`, and the Noetherian definitions in properties.tex (01OV). The field spectrum meets the base hypothesis: the field has only two ideals and its spectrum is one point. It follows that X is Noetherian. The statement of `lem-weil-pbc-noetherian-open-subscheme-noetherian` explicitly says each open subscheme is quasi-compact; I checked its sources 01OW, `lemma-locally-Noetherian`, and 01OZ, `lemma-Noetherian-topology`, in properties.tex. I opened `pqf-def-locnoeth`, `def-weil-finite-type-morphism` and `def-weil-quasi-separated-morphism`: they respectively define local Noetherianity, the affine inverse-image qc test, and the same test for the diagonal. Every inverse image under f or Delta_f under discussion is open in X. Applying the open-subscheme statement to those opens proves both tests directly. No assertion that an affine-open intersection is affine, or that the diagonal is closed, is used.

Step 2 uses `lem-weil-pbc-finite-ring-constructible-derived-origin`. I read its full statement, including its arbitrary finite commutative ring clause, intrinsic essential image and preservation/reflection of each interval. These are precisely the hypotheses on C and B. Its essential image gives L and alpha, and interval reflection gives a lower bound on L. I did not cite the special A_{E,n} origin theorem for this arbitrary B. A finite ring is Noetherian (an increasing chain of ideals stabilizes because the underlying set is finite), as required in the Stacks comparison sources.

Step 3 uses only the statement of `thm-dg-finite-type-constructibility`, whose four relevant hypotheses (common ground field, finite-type schemes, finite coefficient ring, invertible annihilator) are all in force. It gives bounded constructibility, not any Tor bound. No separability, perfection, algebraic closure or finite cohomological dimension assumption on the field is added.

Step 4 uses `lem-weil-pbc-comparison-direct-image-canonical-mate`. I opened that node and read its statement, which defines b as the specified adjoint transpose, asserts its invertibility and gives its counit normalization. I also read its source blueprint `prop-weil-pbc-comparison-direct-image.md` in full, including the paragraph checking the named map. This is a qcqs comparison for finite constant coefficients on bounded-below inputs; step 1 gives qcqs and step 2 gives bounded below. Thus it applies to f and L. The written composite with Rf(alpha) has exactly the displayed source and target; the inverse is obtained by composing the two inverses in reverse order. There is no unspecified base-change or unrelated coefficient equivalence in this step.

Step 5 applies the other direction of the same finite-ring derived equivalence at Y to the bounded constructible etale N of step 3. That node explicitly gives intrinsic pro-etale constructibility and interval preservation, not just classical cohomology. I read `def-weil-proetale-constructible-sheaf` to check that its stratifications, local constant module models and finite stalks agree with the item's wording. Composing local trivializations with the isomorphism of cohomology sheaves proves isomorphism invariance directly. No further unpublished preservation statement is used.

I tested the proof on the empty source, C=0, the identity morphism, a nonzero shift, and the doubled-origin line mapping to the affine line (a genuinely nonseparated finite-type map). The qcqs argument holds in the last case and never asserts separatedness. For B=Z/4 with C the constant Z/2 sheaf in degree zero, which need not have finite Tor amplitude over B, the steps still apply. Composite annihilators and product coefficient rings also cause no change. If m=1, B is the zero ring and every input/output module is zero. Empty schemes permit a trivial finite interval and the empty stratum. These cases expose no added or missing hypothesis.

I traversed the statement/proof dependency closures of all five theorem tools before writing: none reaches this item, so their reuse creates no cycle. Every step/node pair has a literal statement quote in citations.json. All non-elementary assertions in the steps are accounted for by these cited statements. Off-unit theorem tools are declared with specific reasons in split_report.tool_uses; they implement the exact comparison/finiteness route prescribed by the parent and no same-unit general replacement was found. No SGA source is used.

## Unfinished work

None in this one-level split. The mathematical proofs of existing cited unsplit/sorried dependencies remain their own items, as required by stage 1. Delivery is subject to the required server dry run and the maintainer's independent review.

## Dry-run repairs

The first dry run rejected the step-1 finite-type-over-Noetherian quote because the conclusion alone was below the 40-character minimum. I replaced it by the complete hypothesis-and-conclusion sentence from that node. The proof was unchanged.
