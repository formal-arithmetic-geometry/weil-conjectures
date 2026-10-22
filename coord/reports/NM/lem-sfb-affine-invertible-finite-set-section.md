# Stage-1 report: lem-sfb-affine-invertible-finite-set-section

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-invertible-finite-set-section.json`: statement, split; no Mathlib match. The statement and statement dependencies are unchanged. Six proof steps replace the empty proof.
- `citations.json`: seven citations, each quoting verbatim the statement that the corresponding step uses.
- `report.md`: this report. `searches.jsonl` contains the actual Mathlib searches; `write_split.py` is sandbox-only preparation, not a delivery node.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project library by the exact blueprint tag and by nonvanishing, finite sets, invertible sheaves and sections. The project has the global-generation nonvanishing cover and the nonvanishing-locus trivialization, but these do not choose a single section for an arbitrary finite set. They are reused as proper sub-results. No exact complete project declaration was found.

## WANTED

None. All sources needed here are present.

## Issues and changes

The imported item is correct, including its explicitly allowed nonclosed points. Its original proof was empty. No statement correction or dispute is necessary. The original seven Mathlib searches are retained and their reported hits were read. Six additional searches were run through the required msearch command and appended verbatim by tool and query. They cover two semantic phrasings (sheaf and ring-module), Loogle, LeanSearch, and two source greps. Mathlib's `Module.Invertible.exists_finset_free_localization` (PicardGroup.lean:380), `Module.Invertible.exists_linearEquiv_ideal` (:901), and `Module.FinitePresentation.exists_basis_localizedModule_powers` (Localization/Free.lean:41) were read: local freeness on a cover, realization as an ideal, and extension of a chosen localized basis do not state simultaneous finite-set nonvanishing and do not specialize to it in one line. The scalar evaluation hits concern functions rather than arbitrary invertible sheaves.

The blueprint ancestor command prints `None`; the item already has a null ancestor and a long explicit auxiliary norm-construction route through Divisors 0BUT and 0BCY. That inherited metadata is preserved, not replaced with a guessed blueprint node. Blueprint searches for nonvanishing, invertible sheaves, global generation, and finite sets of points found no equivalent statement; `same_as` remains empty. The chapter and unit records were read and not edited. This is an auxiliary algebraic-geometric tool below their fixed route.

## Unfinished work

None for the stage-1 split. Existing cited nodes retain their existing stage status; no Lean was written and no compiler or build was run.

## Not duplicates

No new nodes were created. Whole-DAG searches found and reused affine global generation, the nonvanishing cover, openness of the nonvanishing locus and affine stalk localization. Thus there are no new/existing same-tag pairs to distinguish.

## Review by NM

I read Stacks Properties Tag 0F20, `lemma-quasi-affine-invertible-nonvanishing-section`, including its entire base case and induction. I also read the direct affine global-section argument in Divisors Tag 0BUT, `lemma-finite-trivialize-invertible-upstairs`, Schemes 01HV (1),(6) and 01IB, and Modules 01AM and 01CY. The proof follows the 0F20 induction, specialized to affine X and W=X. In that specialization an explicit product of separating ring elements supplies the correcting section; no quasi-affine affine-open refinement or affine-nonvanishing-locus conclusion is needed by this item.

Step 1 uses `def-weil-affine-spectrum` for the prime-ideal coordinates and Zariski topology and `lem-weil-pbc-affine-open-stalk-localization` for the actual germ map as prime localization, with U=X. I opened both statements. The latter supplies unit denominators, fractional representations, the zero criterion and the local-ring isomorphism, not merely an abstract ring isomorphism. The argument proves the scalar-residue criterion explicitly: an element outside the prime has unit germ; an inverse to the germ of an element inside the prime would force a product of two elements outside the prime into it. No field-inclusion or closed-point assumption is used.

Step 2 uses the quasi-coherence clause of `def-sc-invertible-module`, the precise conclusion of `lem-weil-pbc-affine-algebra-module-generators`, and the full arbitrary-family statement of `lem-sc-global-generation-nonvanishing-cover`. I opened all three. Set S=X, A=O_X with the identity map and U=X in the generator theorem: X is affine by hypothesis and identity restriction of scalars leaves the quasi-coherent sheaf L unchanged. The nonvanishing cover applies to an arbitrary generating family, so this does not misapply one of the existing finite-family criteria. It supplies a section nonzero at any chosen point, not at a finite set; the remaining steps do the latter work.

Step 3 uses exactly the openness clause of `lem-weil-pbc-nonvanishing-section-trivializes`; I opened the statement and read Modules 01CY. An open containing a specialization contains every generalization, so it is the more general point x that is removed when x specializes to y. Strong induction on cardinality is explicitly stated, and removal strictly decreases cardinality. No inference goes in the opposite specialization direction.

Step 4 uses only the established induction hypothesis for F and the one-point conclusion of step 2. If the old section is already nonzero at z, it finishes; otherwise its residue at z is exactly zero. This isolates the possible cancellation issue before choosing the correction. The empty F case works both by taking the one-point section and by the empty-product convention.

Step 5 cites the spectrum definition, and the necessary argument about its Zariski topology is written out: inclusion of primes means inclusion in every closed V(I), hence specialization. No-specialization therefore gives an element of p_x outside p_z for every earlier point. The finite product is in each earlier prime and outside the new prime by primality. The scalar-residue identification proved in step 1 supplies precisely the zero and nonzero scalar values required. This product argument is an elementary part of the proof, not a new prime-avoidance lemma or a restatement of a clause of the item.

Step 6 calculates the residue of s+ft at every relevant point. At an earlier point the correction is zero, and at the new point the old term is zero; the surviving product is nonzero because its scalar has an inverse in the residue field. This uses only module and quotient operations. It completes the induction, rather than citing the item or a renamed finite-set selection assertion.

I checked all seven step/node pairs against the cited node statements and included their exact text in citations.json. The three generic off-unit theorem uses are declared with explanations in split_report.tool_uses; they supply affine sheaf tools and do not change the six-functor route. I checked B through E of delivery-errors: no new self-containment or duplicate obligations; definitions are cited or spelled out; statements use single-escaped TeX; all proof steps have a Boolean elementary flag and proof_deps is exactly their union; no hidden non-elementary theorem is used for prime avoidance, CRT, closed-point lifting or global-section exactness. No new node restates the item. Each proof step is below 2000 characters (maximum 829), and none hides a comparison lemma.

The edge checks were E empty (zero section), X empty or the zero ring (necessarily E empty), a singleton, two comparable points including a generic point and its specialization, incomparable nonclosed points, finite residue fields (the construction never chooses a generic scalar), and nilpotents/nonreduced affine schemes (only prime ideals and the germ-localization criterion are used). In particular the method does not assume the points are maximal, that X is Noetherian, that the coefficient fields are infinite, or that L is globally trivial. No statement or hypothesis was weakened.
