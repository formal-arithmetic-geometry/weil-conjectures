# Worker report: lem-sfb-arithmetic-stable-isom-finite

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-arithmetic-stable-isom-finite.json: statement, split; eight proof steps, no new nodes, no new Mathlib leaves. The statement and statement dependencies are unchanged.
- citations.json: all 24 step/node occurrences, with verbatim statements read from the live DAG.
- searches.jsonl: searches run by the mandated msearch.py command; existing inherited searches remain in the item, with the new logged searches appended.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and stable-curve, stable-moduli and Isom terminology. No declaration states this theorem. The source library has general scheme-morphism results, but none for this moduli problem. No Lean was written and nothing was compiled.

## WANTED

None for this split. The proof uses local Stacks sources and existing DAG statements. The cited trait-extension node itself records its agent-written extension of the smooth-generic-fibre source; this delivery uses its actual stronger statement, without attributing that stronger statement to Tag 0E97.

## What changed and why

The item was unsplit, with source tags pointing to the arithmetic stable diagonal but no argument. The nearby lem-sfb-stable-isom-finite-unramified assumes a field base, and lem-sfb-stable-pointed-isom-finite assumes a finite-type scheme over a field. Neither can be applied to Spec Z or arbitrary bases. The existing labelled Isom theorem and labelled trait-extension theorem instead assume only a locally Noetherian base. Those are sufficient after descending each pair of curves locally to a Noetherian integer stage.

The potentially delicate passage is step 2. A descended proper flat curve is not automatically stable. I use the existing arithmetic stable-open theorem to restrict the descended stage to the intersection of the two stable genus-g loci. The original affine base factors through this intersection by the theorem's arbitrary-test characterization. This avoids any unstated eventual-stability lemma and permits the intermediate base to be nonaffine: the labelled Isom and DVR properness theorems require only locally Noetherian. This construction does not presume field characteristic, reducedness, normality, or finite type of the original base.

The proof follows the stated stable-diagonal route at node level. No source or target statement is disputed. The latest blueprint's direct-images proof, paragraph (3), was read: it is the direct-image preservation clause served by the inherited alteration/stable-moduli auxiliary chain. The current auxiliary item is not itself an imported blueprint theorem. Its inherited blueprint.from.node is null (the ancestor command prints None); the exact existing from.place and via chain are preserved. Whole-blueprint searches for arithmetic stable Isom, stable, and approximation found no theorem of the required arithmetic Isom scope. No new blueprint node or source file was written.

## Not duplicates

No new nodes. Existing lem-sfb-stable-isom-finite-unramified and lem-sfb-stable-pointed-isom-finite are limited to field bases; lem-sfb-labelled-stable-isom-unramified is only the separated finite-type unramified part over locally Noetherian bases, and its missing properness is proved using a separate existing extension statement. None of these was cloned or relabelled.

## Mathlib searches

Read all msearch.py outputs and the resulting searches.jsonl. Both semantic phrasings for noetherian spreading produced generic finite-type/base-change and affine-limit results, not a stable-moduli theorem. The direct Isom phrasing returned IsFinite, FormallyUnramified and scheme etale definitions. The second direct formulation, finite unramified stable diagonal over the integers, returned the formal-unramified diagonal characterization. Loogle searches for StableCurve and for IsFinite with FormallyUnramified returned zero hits. The AlgebraicGeometry source grep for stable curve/family/moduli returned zero hits. None gives this stable-curve statement or a one-line specialization. There are no unavailable searches in this run. The exploratory spreading queries are retained honestly even though no new spreading node was needed.

## Review by Q68

I read coord/delivery-errors.md B through E and checked the completed node against each category. B: no new unsplit nodes need statements, definitions, provenance or searches. The item remains self-contained and in single-escaped TeX; its original statement, genus bound, universal-point clause and arbitrary test-scheme scope are preserved. C: I opened every cited node and read its statement, not only its proof. citations.json records every occurrence. D: the eight steps actually construct and verify the representative; no argument is hidden by moving the conclusion into a new node. E: the required hypotheses are established before each application, as follows.

For step 1 I read Quot Tag 0D55, lemma-curves-limits, and the existing curve-limit-preservation statement. Its essential-surjectivity clause gives both proper flat finitely presented algebraic-space families after a common stage, not stable families. Projective-bundle properness is supplied by lem-trf-projective-bundle-proper (Morphisms Tag 01WC, with the adjacent projectivity conventions); flatness and finite presentation are in def-sfb-stable-pointed-curve. The affine approximation node gives exactly the finite-type integer subalgebras and limit; the indexing set is small because these are subsets of the given ring. Its separate stage and limit isomorphisms are retained for step 5.

For step 2 I read Moduli of Curves Tags 0E76 and 0E78, together with the statement of lem-sfb-arithmetic-stable-open-bounded. That statement explicitly applies to the algebraic-space families obtained in step 1, gives a base-change-compatible stable locus, and identifies its families with the project's scheme/projective-bundle convention. Taking the intersection is elementary; factorization is an actual morphism through the open by the stated characterization, rather than a claim based on points. Finite type over Z gives a Noetherian stage by lem-weil-pbc-finite-type-over-noetherian, and pqf-def-locnoeth explicitly includes openness of local Noetherianity. Thus the restricted common base S is locally Noetherian even if it is not affine.

For step 3 I read the statements of lem-sfb-labelled-stable-isom-unramified, lem-sfb-stable-labelled-isom-trait-extension, and lem-sfb-noetherian-dvr-properness, and Limits Tag 0208, lemma-Noetherian-dvr-valuative-proper. The first theorem includes arbitrary tests, naturality, finite type, separation and unramifiedness, and explicitly allows n=0. The second includes all DVRs, possibly singular generic fibres, arbitrary generic base image, and the specified generic isomorphism, so every valuative square for J has exactly one lift. The first supplies the finite-type hypothesis and step 2 supplies the locally Noetherian hypothesis of the third. I read Moduli of Curves Tag 0E9A and the statement and proof of 0E97: 0E97 itself assumes a smooth generic curve and cannot replace the stronger cited trait-extension node. The proof states this distinction explicitly. No generic smoothness, excellence or normality is silently used.

For step 4 I read Morphisms Tag 02V5, lemma-unramified-quasi-finite, and More on Morphisms Tag 02LS, lemma-characterize-finite. The node lem-weil-pbc-unramified-quasi-finite-at-points concludes local quasi-finiteness in exactly the convention of the proper+lqf Mathlib leaf. Properness was proved in step 3. The finite and unramified permanence nodes both state arbitrary base change, so the factorization U -> S of step 2 is sufficient regardless of its flatness or finite type.

For step 5 I checked the fibre-product universal property in def-pc-fibre-product and the full natural representing bijections in the labelled Isom statement. Their composition, conjugated by the fixed curve-identification isomorphisms, is the displayed bijection on every U-test. This is a short elementary application of those statements, rather than a new lemma. It imposes no finiteness on a test scheme.

For step 6 I checked that lem-galois-yoneda-fully-faithful gives precisely the morphism/natural-transformation bijection used for the overlap comparisons. No general Hom(h_A,F) Yoneda formula is being taken from it. Identity transformations and their inverses give inverse maps and faithfulness gives the triple cocycle. The actual overlaps may be nonaffine. I read the full scheme-gluing and morphism-gluing statements: their hypotheses are exactly the open overlap identifications with this cocycle, and they give the glued scheme and structural map.

For step 7 I checked morphism gluing both on C_V and on D_V, and separately on the test V. Gluing both directions and checking the composites locally proves an isomorphism, rather than merely a morphism. Uniqueness supplies both the inverse bijection and pullback compatibility. Thus representability is valid on disconnected and nonreduced tests, not just affine tests or field-valued points.

For step 8 I read the target-local finiteness statement, the explicit chartwise criterion of lem-sfb-scheme-unramified-etale-locality, and the open-immersion-etale statement. These prove global finiteness and unramifiedness without an unrecorded locality theorem. The fibre-product universal property then supplies arbitrary base change, and evaluating the established bijection at the identity of I supplies the universal isomorphism. The desired universal-point clause follows from naturality. On the empty base the empty cover glues to the empty representative; genus 2 and empty markings are permitted throughout. No rank-constancy or flatness of the Isom scheme is claimed, so nonisomorphic fibres and positive-characteristic changes of automorphisms cause no problem.

All eight proof steps are below 2000 characters. There is no hidden long lemma to extract. The only off-unit nonclosed/non-Mathlib tools are projective-bundle properness and unramified implies locally quasi-finite; their specific uses are declared in split_report.tool_uses, not a top-level tool_uses field. The intermediate stable-open node is independent of the Isom finiteness assertion and presently statement-only; no atlas depending on this item is cited. All new mathematical work in this delivery is in the item's proof; zero new nodes remain to split.

## Unfinished work

None in the stage-1 split. Existing cited open statements remain existing DAG obligations. Server dry-run and final push results are reported by deliver.py.
