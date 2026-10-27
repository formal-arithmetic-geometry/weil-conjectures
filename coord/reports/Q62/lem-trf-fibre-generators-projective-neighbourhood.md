# Stage-1 report: lem-trf-fibre-generators-projective-neighbourhood

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibre-generators-projective-neighbourhood.json`: item split, statement unchanged; not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for every node used in each of the five steps.
- `report.md`: this report. The required msearch command wrote `searches.jsonl`.

There are 0 new nodes and 0 new Mathlib leaves. No unit, chapter, Lean, repository, or launcher file was changed.

## Attachments

None. Searching `lean/WeilConjectures/` by the exact blueprint id and by fibre/fiber generation found no declaration covering the whole item. `InvertibleGeneratingSectionsFibre.lean`, `Modules/GeneratesFibre.lean`, and `ProperFibreGeneratorPullbackLocus.lean` concern a generation criterion or more specialized triviality assertions; they do not state this finite-tuple projective-space construction, properness and fibre comparison together.

## WANTED

None. All source passages needed here are in the read-only Stacks checkout.

## Problems and corrections

The item was statement-only with no proof. Its statement is correct, including without a Noetherian hypothesis. Stacks 0D2N assumes a Noetherian base for the earlier lifting of sections; after sections have already been given, its closed-image shrinking and projective-space construction use only properness. No statement was weakened, and no hypothesis was added.

The inherited blueprint provenance points through the fibre-ampleness/projectivity auxiliary chain below `lem-trf-local-term-locality`. I retained that chain and read the latest blueprint ancestor and the chapter/unit records. The current ancestor proof quotes the contracting-correspondence theorem; it does not itself supply a second statement of this scheme-theoretic auxiliary lemma. Blueprint searches for generating sections, nonvanishing, generators/fibre, and projective/neighbourhood found no duplicate of the item. This split follows its already selected 0D2N route and does not change a unit or chapter.

## Unfinished

Nothing in this one-level split. Existing cited nodes retain their current statuses and are not claimed proved here.

## Not duplicates

No new-node/existing-node pairs: no new nodes were created. I reused the existing nodes for 01CY nonvanishing, its pullback behavior, the generating-sections fibre criterion, affine-open bases, projective-space classification/charts/properness, base change of proper maps, and 01W6 proper-over-separated cancellation. In particular I did not create nodes for either the closed-image complement argument or the elementary fibre-product reassociation.

## Mathlib searches

The inherited searches were retained. I ran the required msearch command for this item with LeanFinder twice, with Loogle, with grep in AlgebraicGeometry, and with LeanSearch. All five current searches returned successfully and their exact tools/queries and actual hit names are recorded in both the command log and the item. The second LeanFinder phrasing tested the more general line-quotient/projective-space interpretation. The source at Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:443 defines `AlgebraicGeometry.Proj.fromOfGlobalSections` using a graded ring map to structure-sheaf sections; it is not a map arising from arbitrary invertible-module sections and does not prove the shrinking or twist/fibre assertions. Other hits were Proj properness/away maps, manifold local frames, or abstract sheaf generating sections. None states the whole item or specializes to it in one line.

## Review by Q62

I read `coherent.tex`, Tag 0D2N (`lemma-ample-in-neighbourhood`), from the nonvanishing opens through the construction of phi and the identification of its fibre. I also read `modules.tex`, Tag 01CY (`lemma-s-open`) and `remark-pullback-s-open`; `constructions.tex`, Tag 01NE (`lemma-projective-space`), `definition-projective-space` and its following paragraph, Tag 01NG (`lemma-standard-covering-projective-space`), and Tag 01NH (`lemma-projective-space-separated`); `morphisms.tex`, the properness definition and Tag 01W6 (`lemma-image-proper-scheme-closed`); and `schemes.tex`, Tag 01IT (`lemma-basis-affine-opens`). There are no new nodes requiring a further source review.

For step 1 I opened the four original cited statements: the nonvanishing-section lemma explicitly says the locus is open; the nonvanishing tensor-pullback statement gives the inverse-image equality; the invertible generating-sections criterion applies to the particular finite tuple, not merely all global sections; the scheme-fibre definition includes the underlying homeomorphism onto f^{-1}(s). I added `lem-weil-pbc-invertible-pullback-tensor` explicitly for invertibility after pullback. Thus the criterion is applied to an invertible sheaf on the fibre and the union really covers every point of that fibre.

For step 2 the properness definition itself gives closedness of f on the closed set C by choosing the identity base change. Its image avoids s by step 1. The complement and inverse-image inclusions are written out. The affine-open-basis statement gives an affine U inside that particular complement, not an arbitrary affine neighborhood. Pullback stability and the same nonvanishing/finite-tuple criterion give generation on Z_U. This is an elementary assembly of the cited facts, with no claim about the support of a coherent cokernel or a Noetherian scheme hidden inside it.

For step 3 I checked that the projective-space functor-of-points statement includes both the coordinate-compatible O(1) isomorphism and pullback naturality. The morphism-by-sections definition supplies the two specified projections over U. The standard-chart statement defines the relative twist as the second projection's pullback and supplies affine chart rings and coordinate ratios. The module-pullback definition and the invertible pullback/tensor lemma give composite pullback and compatibility with section units. The affine chart gluing argument is written explicitly: chart coordinate maps preserve ratios, and the frames have exactly the transition rule of `def-pc-projective-space-twist`. Thus the polynomial-Proj twist and the base-change projective-space twist are identified with their coordinates, not just as unspecified line bundles.

For step 4 the proper-base-change statement has no extra hypotheses on the base map, so it applies to U -> S. The projective-space properness statement applies to the finite set {0,...,r}, with r >= 0; hence the target is separated. The proper-over-separated statement exactly takes the triangle q phi = f_U. It is not a claim that every map with proper target is proper. Each hypothesis is supplied before applying it.

For step 5 the fibre-product statement gives uniqueness with both projections. I wrote the universal-property identification of the target fibre with projective space over kappa(s), rather than treating the fibre of a scheme as a residue ring quotient. The functor-of-points statement explicitly includes naturality under arbitrary pullback of the domain, giving the second projection; the morphism-by-sections definition fixes the first. The section-compatible composite pullback statement identifies the twist and sends each coordinate to the corresponding pulled-back section. Uniqueness of the isomorphism is checked on the generating opens. The original definition `def-pc-module-pullback` states composition isomorphisms, while the additional invertible-pullback lemma explicitly says these isomorphisms preserve section units; I added the latter citation in this audit so that compatibility is not assumed from a bare object isomorphism.

I checked delivery-errors B through E point by point against these files. No new-node schema, undefined object, uncited Stacks lemma, relabelled clause, hidden subclaim, or changed statement remains. All non-elementary facts are named nodes whose statements I opened, and `citations.json` quotes their statements verbatim for each use. Off-unit generic inputs are declared in split_report.tool_uses, with their purposes; no alternate unit route was substituted. The longest proof step has fewer than 1300 characters, so none meets the 2000-character long-step threshold.

I tested the small cases: for an empty fibre, the cover assertion is vacuous but the closed image f(C) still avoids s and the chosen neighborhood removes any nongenerating points; for r=0 a single generating section trivializes the line bundle and the resulting map is the proper structure map to P^0_U = U; zero members of a larger tuple cause no problem because only the union of nonvanishing loci is used; a nonreduced base or source does not change the residue criterion or any cited hypothesis. Nonempty fibres, field assumptions on S, Noetherianity, and coherence of a cokernel were never used.

## Validation

The required remote dry run exited successfully: `OK (not pushed)` at 9f7cd30dbfb, with server preflight passed. This includes the required DAG and split checks. The final delivery command reruns preflight before pushing. No Lean compiler or build tool was run.
