# Stage-1 report: lem-sfb-finite-branch-ample-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-branch-ample-descent.json: item, statement, split in seven proof steps. Mathlib verdict: no match; both semantic services, Loogle, and source grep were run. Existing 2026-10-22 searches retained; new 2026-10-23 searches recorded from searches.jsonl.
- citations.json: one verbatim statement quotation for every node citation of every proof step.
- report.md: this report. No new nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, finite-branch, pinching, ample descent, and relevant ampleness declarations. CurveBranches concerns ring-theoretic branches; field-extension coordinate descent and AmpleReduced concern different morphisms. No declaration gives all clauses here. AmpleIso supplies only the existing generic isomorphism-invariance tool, not the item.

## Wanted literature

None. All arguments use the locally available Stacks source. No SGA source was used.

## Findings and changes

The item was unsplit and no earlier sandbox item/report/search log existed. Its mathematical statement is valid as written and is unchanged, including the nonclosed-point and empty cases. The old proof and proof-dependency arrays were empty. The ancestor query returns null; I retained the exact inherited blueprint.from and via chain and documented how these proof steps serve the old pinching steps 6--8. Searches of the whole blueprint with blueprint_refs.py (finite-branch, ample descent, glue-sheaves) found no identical blueprint item. I read the latest blueprint unit and its direct-images proof (3); it gives the ancestral direct-image context, not a separate line-bundle descent theorem. The serialized unit record describes an older statement; I did not change a unit or substitute a route.

The given affine open U is essential to obtaining one section simultaneously nonzero at all branches. Pointwise trivializations cannot simply be united into one trivialization over their union. Instead the existing finite-set section lemma on U supplies a single section, and the finite closed-image shrinking argument produces a saturated neighbourhood. The quotient need not be flat, so no fpqc descent theorem is invoked. In the final argument I use a finite projective-space immersion and prove it closed; a projective-bundle conclusion alone would not meet def-kun-projective.

## Not duplicates

No new nodes. Existing lem-sfb-affine-invertible-finite-set-section covers the affine specialization of 0F20; lem-weil-pbc-nonvanishing-section-trivializes covers 01CY; lem-weil-pbc-glue-sheaves-of-modules covers sheaves 00AL/00AM/04TN; lem-trf-finite-surjective-ample-reflection covers 0B5V; lem-weil-pbc-ample-very-ample-immersion-affine-base covers 01VT. These were reused rather than restated. lem-sfb-finite-trivialize-invertible-upstairs only trivializes above one target point at a time and is not silently upgraded to simultaneous trivialization along T.

## Generic tools outside the unit

The item's split_report.tool_uses declares the existing sheaf/module pullback and gluing tools, nonvanishing trivialization, ample-isomorphism invariance, finite-surjective ampleness reflection, and the affine-base ample immersion theorem. They are generic tools for the prescribed pinching route; the direct-image unit has no replacement argument for any of them. Mathlib leaves and definitions are also cited in the relevant steps. No top-level tool_uses or reviewer record was edited.

## Review by Q53

I read delivery-errors B--E in both recorded copies and checked the actual source statements rather than treating tags as proofs. For the item I read properties.tex Tag 0F20 (lemma-quasi-affine-invertible-nonvanishing-section, lines 5327 onward), modules.tex Tag 01CY (lemma-s-open, lines 4360 onward), the sheaves.tex gluing lemmas (04TN, 00AL, 00AM at lines 5078, 5192, 5253), coherent.tex Tag 0B5V (lemma-surjective-finite-morphism-ample, line 4548), morphisms.tex 01VT (lemma-finite-type-over-affine-ample-very-ample, line 9518) and 01W6 (lemma-image-proper-scheme-closed, line 9949), and constructions.tex 01NH (lemma-projective-space-separated, line 2889). I checked tag/label correspondences in the tag table. There are no new-node sources to audit.

In step 1 I opened lem-sfb-affine-invertible-finite-set-section and lem-weil-pbc-nonvanishing-section-trivializes: the former expressly allows nonclosed points and gives a section on any affine scheme, the latter gives both the open nonvanishing locus and its trivialization. The hypotheses hold on the supplied affine U; ampleness is not needed yet. In step 2 I opened lem-weil-pbc-finite-closed-map-finite-fibres, whose statement really gives closed images for a finite morphism. The rest is the written set-theoretic argument: the fibre over a point of T is contained in |Z|, so none of its points lies in C. No surjectivity or closedness of individual branch points is smuggled into that shrinking argument. This is why step 2 is marked elementary while still citing the closed-map input.

In step 3 I opened the full module gluing statement, including all-index cocycle compatibility and the chart equality it provides, and the definition of invertibility. The local modules are O_W and the transported L on D. Their transition is the actual chosen section trivialization, with the reverse transition its inverse; hence all two-index and triple-overlap conditions hold. M is locally O, so its local free presentations are also local quasi-coherent presentations. This checks the quasi-coherence and rank-one parts of def-sc-invertible-module, not only the existence of a sheaf of modules.

In step 4 I opened def-pc-module-pullback, lem-pc-module-pullback-identity-composition, and lem-weil-pbc-open-immersion-module-pullback-restriction. They state the tensor pullback, composition identifications, and restriction comparison actually used. Pulling back a ring sheaf is the tensor-unit identity, not a flatness assertion. For transport along b I use its inverse and the identity/composition pullback isomorphisms. I wrote the overlap equality c_D = alpha c_W, checked that alpha pulls back to tau_W, and invoked clause (1) of the gluing node for both maps and their inverses. Thus the global a^*M isomorphism follows from agreement of the same local maps, with no unstated effective descent along a.

In step 5 I opened lem-sc-ample-iso and lem-trf-finite-surjective-ample-reflection. The former transports ampleness under the proved module isomorphism; the latter requires exactly a Noetherian base ring, both schemes proper over it, a finite surjective morphism, and an invertible module on the target. I verified all of these and wrote the source/target substitution explicitly to avoid reversing the lemma. No normality, connectedness, or flatness is required.

In step 6 I opened def-weil-proper-morphism and lem-weil-pbc-ample-very-ample-immersion-affine-base. Properness supplies finite type and the target is the single affine Spec R, so a global finite-dimensional projective-space immersion is available. I did not replace this with the weaker arbitrary projective-bundle result. In step 7 I opened lem-weil-pbc-projective-space-proj-separated, lemma-nagata-proper-to-separated-target, lem-weil-pbc-proper-immersion-closed, and def-kun-projective. Their conclusions successively give separated target, properness of i, closed immersion, and the exact finite-projective-space convention required.

Small cases: T empty forces Z empty; conversely Z empty forces T empty by surjectivity. Then b is a global isomorphism and the construction reduces to transporting L, with an empty trivializing open permitted. If X is empty, surjectivity also makes Y empty, and its immersion into P^0_S is closed. For a finite set containing specialization-related points the finite-set section theorem expressly applies; no Chinese remainder argument assuming maximal ideals is inserted. Nilpotents and disconnected components are harmless because every local gluing and pullback assertion is sheaf-theoretic and the finite-surjective reflection theorem imposes no reducedness. Finite T is not assumed to be etale, and no group action appears.

All seven steps are shorter than 2000 characters. They expose the neighbourhood construction, transition map, inverse-map gluing, and separate ampleness/projectivity implications, with no hidden long-step lemma. Every uses entry has a complete verbatim node statement in citations.json. No dependencies are taken from cited nodes' proofs. The item is not relabelled as one or more new copies of its own clauses: the argument is carried by its steps, using only existing generic lemmas. There are no new statements whose small cases or Mathlib matches could be unverified.

## Unfinished work

None in the proposed split; independent maintainer review remains the delivery workflow's next stage.
