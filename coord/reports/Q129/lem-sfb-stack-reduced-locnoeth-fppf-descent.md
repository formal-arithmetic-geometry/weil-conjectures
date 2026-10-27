# Stage 1 delivery: lem-sfb-stack-reduced-locnoeth-fppf-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-reduced-locnoeth-fppf-descent.json: unchanged statement, four-step proof, audited dependencies, retained ancestry and earlier searches, plus genuine new searches and the split report.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-locnoeth-fppf-descent.json: statement, unsplit; no Mathlib match. Local Noetherianity descends along a surjective flat locally finitely presented scheme morphism. This is a generic scheme descent theorem, with no reducedness or stack hypothesis.
- citations.json: one verbatim statement quotation for every dependency of every proof step.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, algebraic-stack terminology, reducedness and fppf descent, and local Noetherianity. No declaration states the item. The related scheme results in the project and Mathlib do not provide a completed algebraic-stack proof. No Lean was written or compiled.

## WANTED

None. The source needed here is present as Stacks TeX.

## Audit of the original item and route

The statement is true as written and was retained verbatim. Its source correctly points to Stacks 04YF (stacks-properties.tex, lemma-type-property), whose proof chooses scheme charts on a stack fibre product, and 06MP (lemma-unique-point-better), whose proof of (2) implies (1) descends local Noetherianity from the pullback of a smooth atlas. Read both complete proofs. Also read descent.tex 034C (lemma-Noetherian-local-fppf), 034E (lemma-reduced-local-smooth), and 06QM (lemma-descend-reduced), and spaces-descent.tex 06MI and 06MJ. The latter explain the space-valued version; the delivered proof refines to a scheme chart and therefore uses scheme descent, avoiding a new algebraic-space ascent theorem.

In particular, reducedness is smooth local, not stable under arbitrary fppf ascent. The proof never pulls reducedness up along p. It pulls it up along the other projection, which is smooth, and descends it along the fppf projection. No global Noetherian hypothesis on S, quasi-compactness of a cover, separatedness of an atlas, or smoothness of p is introduced.

The existing chapter and unit records were read, followed by the current latest blueprint chapter/unit context and det-thm-sf-ctf-stability-direct-images proof (3). The item is a supporting residual-substack input in the existing imported alteration route. The unit record is historical relative to latest; no unit/chapter field is changed. tools/blueprint_refs.py ancestor prints None for this existing chain; the new node preserves that computed ancestry with the item prepended to via, rather than inventing an ancestor.

## Searches and Mathlib verdict

All new searches were run with the prescribed msearch.py command; searches.jsonl is its untouched log, and search-*.txt files preserve actual outputs. The new node records LeanFinder, LeanSearch, Loogle and grep, including the second semantic phrasing “Local Noetherianity is an fppf local property of schemes faithfully flat descent”. Read the hits: IsLocallyNoetherian, isLocallyNoetherian_iff_openCover and isLocallyNoetherian_of_affine_cover concern Zariski descent, while LocallyOfFiniteType.isLocallyNoetherian is ascent in the opposite direction. Read Mathlib/AlgebraicGeometry/Noetherian.lean and the project's extension WeilConjectures/Mathlib/AlgebraicGeometry/Noetherian.lean. Neither states fppf descent. The generic morphism-property descent hits assume the relevant descent theorem, so they are not a one-line specialization proving this object property.

For the item, a second stack-atlas phrasing and an AlgebraicStack name search yielded scheme smoothness and generic morphism-property tools, with no algebraic-stack theorem. Further reducedness searches found IsSchemeTheoreticallyDominant.isReduced; read its statement in Morphisms/SchemeTheoreticallyDominant.lean: it requires quasi-compactness and scheme-theoretic dominance, so it does not directly cover the arbitrary atlas projection. Existing faithful-flat local algebra suffices, and no reducedness node was created.

## Not duplicates

lem-sfb-scheme-locnoeth-fppf-descent vs lem-trf-etale-local-noetherian-descent: the existing theorem descends through etale scheme covers; the new theorem allows ramified flat locally finitely presented covers, which need not admit an etale refinement.
lem-sfb-scheme-locnoeth-fppf-descent vs lem-trf-log-tower-effective-center-descent: the existing theorem assumes a locally Noetherian log base and descends a specified saturated blowup tower; it does not descend local Noetherianity from an arbitrary fppf source.
lem-sfb-scheme-locnoeth-fppf-descent vs lem-trf-polarized-fine-log-etale-descent: the existing theorem is effective descent of polarized fine log schemes with etale descent data, not local Noetherianity along flat scheme maps.
lem-sfb-scheme-locnoeth-fppf-descent vs lem-trf-log-structure-fixed-scheme-enhancement: the existing local Noetherian conclusion uses an etale cover with fine-log enhancement data; the new result applies to arbitrary fppf scheme morphisms with no log data.
lem-sfb-scheme-locnoeth-fppf-descent vs lem-sfb-noetherian-space-finite-scheme-cover: the existing result assumes a separated Noetherian space over a field and constructs a finite scheme cover; it does not descend local Noetherianity from an fppf cover.
lem-sfb-scheme-locnoeth-fppf-descent vs lem-sfb-space-finite-cover-structure-support: the existing result assumes local Noetherianity of its target and proves finiteness/coherence/support consequences, not descent of that assumption.
lem-sfb-scheme-locnoeth-fppf-descent vs lem-sfb-stack-reduced-locnoeth-fppf-descent: the item constructs a smooth atlas of a stack with both reducedness and local Noetherianity; the new lemma only descends local Noetherianity between schemes. The nontrivial common-atlas construction and reducedness argument remain in the item's proof.
lem-sfb-scheme-locnoeth-fppf-descent vs lem-weil-pbc-faithfully-flat-descent-noetherian: the latter is a ring theorem; passing from a possibly non-quasi-compact fppf scheme cover to affine faithfully flat algebra requires the affine-refinement argument of 034C. This is not an elementary one-line specialization.

Searches of all DAG nodes by 034C, 06MI, 06MJ, 06QM, labels and statement keywords, plus blueprint_refs.py searches for reduced, Noetherian, fppf, faithfully flat, locally Noetherian, descend-reduced and Noetherian-local-fppf, found no existing node stating the new theorem. The smooth-reduced-dense-pullback and space-smooth-reduced-locality nodes concern ascent or descent under smooth maps; b need not be smooth.

## Review by Q129

I read the item against Stacks 04YF and 06MP, not merely their tag descriptions. I read the complete statement of every cited DAG node. Step 1 uses def-trf-algebraic-space exactly for existence of a surjective representable etale scheme chart of P; representability of p makes P a space already by the item's hypothesis. The other citation is lem-sfb-stack-chartwise-smooth-etale-calculus: its statement explicitly includes arbitrary base change and composition, etale implies smooth, smooth implies flat and locally finitely presented, and stability of surjectivity. The maps P to V and P to W are base changes of q and p respectively, so all those hypotheses apply. The atlas is representable by spaces, as required by the algebraic-stack convention. The final maps a and b have scheme source and target, so the scheme properties agree with the chartwise properties. I checked the atlas existence and scheme chart are choices allowed by the definitions, with the existing size convention, including the empty case.

Step 2 cites only the first assertion of lem-trf-smooth-reduced-dense-pullback: a is smooth, its base V is reduced and locally Noetherian, and that node explicitly requires no surjectivity. No density or generic-point conclusion is used. This generic scheme tool is from another unit and is declared in split_report.tool_uses.

Step 3 uses def-weil-flat-morphism for the flat local ring map at a chosen preimage point. Surjectivity of b from step 1 supplies that point. Both local rings have the correct direction, O(W,w) to O(T,t). The statement of lem-weil-pbc-flat-local-hom-faithfully-flat supplies faithful flatness for exactly this flat local homomorphism. The statement of lem-weil-pbc-faithfully-flat-ideal-contraction explicitly supplies injectivity at I=0. The remaining argument is written out: the image of a nilpotent vanishes because T is reduced, then injectivity kills the original element. def-pc-reduced-scheme identifies the resulting stalk condition with reducedness of W. These two generic algebra tools are declared in split_report.tool_uses. This avoids hiding reducedness descent in a tag citation or creating an elementary node.

Step 4 uses the new scheme descent statement with X=T and Y=W. Flatness, local finite presentation and surjectivity were all obtained in step 1, and local Noetherianity in step 2. The selected q remains the smooth surjective atlas throughout, so the conclusion is exactly the original existence assertion. I copied the full relevant statements verbatim into citations.json rather than substituting a stronger quotation.

For the new node I read descent.tex 034C in full: locality means both ascent and descent for fppf covers, and its descent implication applies to the singleton covering {f}. The statement introduces both schemes and their map, names each definition, and has no proof, proof dependency or inline proof sketch. The argument reserved for its future split is the source's affine reduction using fppf affine refinements and faithfully flat Noetherian ring descent, not a new axiom. This is a smaller independently reusable scheme theorem, not the original stack-atlas conclusion renamed.

I tested identity covers, the empty cover of the empty scheme, an infinite disjoint union of field schemes over a field (showing no quasi-compactness may be silently assumed), and the fppf ramified cover Spec(k[e]/e^2) to Spec(k). The new lemma correctly allows the last nonreduced source: it concerns local Noetherianity alone. For the item, V empty forces the atlas empty by surjectivity; W=V with p the identity reduces to the known case. The nonreduced-base case Spec(k[e]/e^2) cannot have a reduced flat surjective scheme cover, precisely because the stalk map would be injective. For a reduced source over a non-Noetherian S the proof still uses only V and the two projections. No step exceeds 2000 characters and no comparison lemma is hidden in a long step.

I checked delivery-errors B through E point by point against the actual files: the sole new node is self-contained statement-only TeX with a correct tag/label and real logged searches; statements support every citation; the item's argument stays in the item; properties are applied in the correct directions and with all hypotheses; neither a cycle nor a statement weakening is introduced by the new node. The local exploratory reachability pass encountered an unrelated missing live-clone dependency (def-weil-pbc-ideal-module-product-stalk); the authoritative server checks decide the actual delivery tree. No checker was run locally.

## Unfinished work

Only the new scheme local-Noetherian fppf descent node remains unsplit, as required for one-level stage 1. No mathematical clause of the item is left unexplained. No attachment, WANTED source, statement dispute, Lean edit, compiler invocation or repository write is part of this delivery.

## Validation

Server review_split and the required delivery dry run are run after preparation; final results are recorded below before pushing.
