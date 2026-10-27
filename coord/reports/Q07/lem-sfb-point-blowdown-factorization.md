# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-point-blowdown-factorization.json`: item split into five steps; original statement retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-point-blowup-functions.json`: one new statement-only node; unsplit, no Mathlib match.
- `citations.json`: nine exact quotations, one for every step/node pair.
- `searches.jsonl`: actual msearch records for both statements. The item retains its imported NH search history as well.

## Attachments

None. Searched the live `lean/WeilConjectures/` tree for the blueprint tag, blowdown, factor-through-contraction, exceptional curves, and the blowup sources. No project declaration states the item. Blowup complement/properness declarations are already attached to existing nodes and are reused, not duplicated. No Lean was written or compiled.

## Wanted literature

None. The sources needed here are present in `literature/stacks-project/`.

## Source and proof

I read resolve.tex Tag 0C5J (`lemma-factor-through-contraction`), including the paragraph before it defining contraction, and its entire proof. The proof first identifies the quotient topology and the direct image of the structure sheaf, then descends the morphism of ringed spaces and checks locality. That is the route of the delivered split. I also read resolve.tex Tags 0AGQ (`lemma-blowup`) and 0AGS (`lemma-cohomology-of-blowup`), especially (4) at n=0 and its proof, and coherent.tex Tag 02KH (`lemma-flat-base-change-cohomology`). The item is a prerequisite of common-nodal-model step 4, which descends the second projection after removing the last bad point blowup. Its ancestor, unit and chapter records were read; no alteration, coefficient, or chapter route was changed.

The new lemma isolates only the regular-functions input. A future split of that lemma can check the canonical sheaf map on stalks: away from x the blowup is an isomorphism; at x, flat base change to Spec(O_T,x) identifies the target stalk with the global functions on the local blowup. Properness gives the qcqs hypothesis for 02KH, and the structure sheaf is quasi-coherent. In local dimension two, 0AGS(4), n=0 gives A itself, by the canonical pullback. In dimension one, the regular local ring is a DVR (00PD, algebra.tex lemma-characterize-dvr, equivalence (1), (3), (4)); its maximal ideal is invertible, so the blowup is an isomorphism. In dimension zero the regular local ring is a field, and the blowup of its zero maximal ideal is empty. Flat base change would make E empty, contrary to the new lemma's explicit nonempty-fibre hypothesis. The global dimension bound is used only to restrict these local cases. These are proof notes in this report; the new unsplit node contains no proof or proof dependencies.

## What needed attention

The node was unsplit. There was no existing proof to preserve. Its source calls x a regular point of local dimension two, while the imported item only assumes T is regular of global dimension two. I did not silently equate those hypotheses or add pure dimension, integrality, or a dimension hypothesis on x. The new lemma includes the lower local-dimensional cases as above. Thus this is not a statement correction or a statement dispute. The premise f(E) is one point means exactly a singleton, not 'at most one point', and supplies E nonempty.

No target separatedness or finite-type hypothesis is added. In particular the uniqueness proof uses the isomorphism on sheaves, not equality on a dense open into a separated target.

## Searches and duplicate audit

Before creating the new node I searched the whole DAG by 0AGS, blowup/structure-sheaf and birational/direct-image terminology; searched blueprint_refs for contraction, blowup, blow-up, 0AGS, and blowup structure; and read the live project blowup declarations. The ancestor command returns blueprint.from.node=None along the existing created-item chain. I preserved that ancestor and inherited the via chain, adding this item in front for the new node. There is no blueprint node giving the new regular-functions statement. No new definition node was needed: all its notions have existing definition nodes.

The msearch log includes LeanFinder, LeanSearch, Loogle and grep for the item, with two semantic phrasings. For the new lemma the four queries are: the canonical structure-sheaf map along a regular point blowup; preservation of regular functions; Loogle names AlgebraicGeometry/blow/push; and grep `blow.?up|blowing` in AlgebraicGeometry. I read the hits. They concern ordinary stalk/localization maps; none is a blowup theorem. Valuative uniqueness, normalization hom_ext, and separated-target dense-open equality do not state the item. Both grep searches and the Loogle blowup queries returned no hits. All records describe searches actually run; there is no fabricated search or Mathlib attachment.

## Not duplicates

lem-sfb-regular-point-blowup-functions vs lem-per-regular-point-blowup-acyclic: the existing node uses 0AGS(2) and concludes R^1 b_* O=0 plus regularity/properness; it never concludes O_T -> b_* O_W is an isomorphism. The new node uses 0AGS(4) at n=0, includes nonintegral regular schemes and possible lower local dimensions, and asserts only the canonical degree-zero structure-sheaf isomorphism.

lem-sfb-regular-point-blowup-functions vs lem-per-regular-surface-rational: the existing statement says a Nagata regular local ring of dimension two has a rational singularity. It does not state the canonical structure-sheaf isomorphism for an arbitrary regular point blowup; its occurrence of 0AGS is in the auxiliary acyclicity route.

## Review by Q07

I reread the five steps with resolve.tex 0C5J and every cited node open. Step 1 takes the actual complement isomorphism from thm-nagata-global-blowup-complement, properness for finite-type quasi-coherent centres from lemma-nagata-blowup-proper, closedness directly from the universal-closedness clause of def-weil-proper-morphism, and exactly the isomorphism beta from the new functions node. No node is cited for a stronger conclusion than its statement. The reduced closed-point ideal is quasi-coherent and finite type on the Noetherian scheme; singleton f(E) gives a point above x, so surjectivity follows from the complement isomorphism. Step 1 is non-elementary because it invokes the geometric statements.

Step 2 proves continuity rather than invoking an uncited quotient theorem: the complement of g^{-1}(V) is the image of the closed complement of f^{-1}(V). This uses only the established closedness and surjectivity. Its uniqueness assertion is set-theoretic surjectivity. Step 3 uses the explicit on-opens isomorphism in the new node and the sheaf-map/composition definitions in def-weil-locally-ringed-space-morphism. The formula beta^{-1} f-sharp is restriction compatible and its composite with beta is f-sharp; no sheaf inverse-image adjunction is smuggled in. Step 4 uses precisely that definition's local-stalk-map criterion. Choosing w above every t is justified by step 1. If g-sharp(a) were a unit its pullback would be a unit, contradicting locality of f; nonunits in a local ring form its maximal ideal. This checks locality at all points, including x, without assuming a stalk isomorphism for b. Step 5 cancels beta on each open after surjectivity has identified the underlying maps. Those four steps are elementary from the formulas and the cited definitions/isomorphisms.

I checked the new statement against 0AGS(4), its global localization justification 02KH, and the lower-dimensional cases described above. It introduces T, x, W, b, the dimension bound, the nonempty fibre and the canonical map; it has definition dependencies, one-backslash TeX, no proof in its statement and no circular dependence on the item. It is smaller than factorization: no arbitrary target Z or morphism f appears, and the item still constructs the topology, sheaf map, locality and uniqueness. The two same-tag nodes were read and compared above. No existing node gives the needed degree-zero map, and I did not use their proofs as statements.

Small cases checked: blowing up the origin of an affine plane (the usual exceptional P^1 and unchanged regular functions); a closed point on a dimension-one regular component of a dimension-two disconnected scheme (invertible centre and identity blowup); a zero-dimensional field component (empty exceptional fibre, excluded by the explicit nonemptiness premise); a nonclosed point z of an arbitrary nonseparated target (the topological and sheaf arguments need only singleton image). Empty open sets cause no exception to beta or its inverse. The locality proof is valid for all local rings and uses no residue-field isomorphism.

Corrections made during self-review: I retained the lower-dimensional cases in the new auxiliary statement instead of using the dimension-two local calculation without justification, and used the direct on-opens sheaf formula so no additional adjunction lemma is hidden. The item statement is unchanged. All five steps are below 2000 characters; none hides a standard comparison or separate geometric lemma. I checked B1--B10, C1--C8, D1--D5 and E1--E7: one genuine new non-elementary input, all other external facts cited, no cycle through the parent, no illicit off-unit proof replacement, and no use of SGA.

## Unfinished work

Only the newly stated regular-functions lemma remains for a later stage-1 worker, as intended for a one-level split. The present item has a complete proof conditional on that smaller node. Server dry run and push results are recorded below when available.

## Existing citation error

The existing lem-sc-regular-dim1-dvr node records external Tag 00DV, but the local tags map and algebra.tex identify 00DV as lemma-NAK. The DVR characterization is 00PD (lemma-characterize-dvr), which I opened and read, including the regular-local-dimension-one equivalence. I corrected my report to use 00PD; the existing node was not edited or used as a proof dependency. This is a citation error in that node, not a dispute of its mathematical statement.

## Validation

The server review_split check passed. The first full deliver.py --no-push exited 0 and printed OK at 9dfa8b05f91. After the report citation correction, the required final dry run is repeated before push.
