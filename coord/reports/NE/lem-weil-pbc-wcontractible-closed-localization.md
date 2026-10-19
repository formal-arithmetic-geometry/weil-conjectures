## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-wcontractible-closed-localization.json: statement, split; no whole-item Mathlib match.
- citations.json: verbatim statements for every proof-step citation.
- No new nodes or Mathlib leaves created.

## Attachments

None. I searched the exact blueprint tag/id and the notions in WeilConjectures of the read-only slopmaster2 source. WContractible.lean gives retractions for ind-etale covers of its structurally defined w-contractible rings, not all clauses of this item or its stated weakly-etale retraction hypothesis. WLocalization/Basic.lean gives related generalization localization facts, not the whole assertion. Upstream master is reference material only.

## WANTED

None: all proof sources are in literature/stacks-project.

## Findings and corrections

The statement is correct as imported. I retained its finite-list hypothesis, the allowance r=0, and its explicit retraction definition of w-contractible. The source's B in the proof of 0987 means the arbitrary covering algebra, whereas this item's B denotes the closed localization; I named the arbitrary algebra D to avoid that collision. The generalization localization of 096V is not the blueprint retained w-localization R_[T], which has pairs of primes as points. I did not identify them.

The original proof was empty. The seven steps now carry the argument. I initially considered a general localization-spectrum Mathlib leaf, but the full DAG search revealed lem-weil-pbc-localization-prime-residue-field-iso part (1). I reused that node and proved the topology from the basic-open basis instead of creating a duplicate. I also reused lem-weil-pbc-wcontractible-cover-section instead of creating a child that would restate the contractibility clause.

Searches ran through msearch.py: LeanFinder, Loogle, grep, and LeanSearch. LeanSearch returned Internal Server Error and is recorded unavailable. The two whole-item semantic phrasings yielded formal-etaleness/locality and projective-spectrum results, not the combined item. The localized-spectrum hits were read in Mathlib/RingTheory/Spectrum/Prime/Topology.lean at 344-376 and Localization/Ideal.lean at 242; they were not turned into a redundant new node. DAG keyword/tag/declaration searches and blueprint_refs searches for localization, primes localization, proper ideal, multiplicative and localization weakly found no blueprint node stating this whole item. The existing retained-localization blueprint statement is different. The item preserves its nearest ancestor thm-weil-pbc-qbar and its complete via chain; same_as is empty. Its unit record is unchanged because this is not the unit's key node.

## Unfinished work

None in the stage-1 split. No Lean files were written, and no compiler, Lake, or build command was run. The sandbox is for a fresh second reader, not a delivery push.

## Review by NE

I read proetale.tex Tag 096V (lemma-localization), Tag 0987 (lemma-localization-w-contractible), and Tag 09AH (lemma-ses-associated-to-open), including their proofs. I also read algebra.tex Tag 00E3 (lemma-spec-localization). The first two source lemmas permit arbitrary rings and arbitrary ideals; finite generators of the closed support are only needed for the finite complement covering. There are no new node sources to review. The chapter and unit retain the proper-base-change route; this node is the auxiliary closed-neighborhood construction below the descended-coefficient branch.

Step 1 uses exactly part (1) of localization-prime-residue-field-iso, not the narrower primes-of-localization node (which is restricted to a prime localization and its principal localization). I checked the multiplicative-subset hypotheses against S and the fraction construction. The proper-ideal-contained-in-maximal statement supplies a containing maximal ideal for p+I. The elementary equalities 1=g+h and ts+i=1 establish both directions of the specialization criterion; no Jacobson or Noetherian hypothesis enters.

Step 2 uses the basic-open node's basis clause for both R and B. The fraction denominator is a unit, so the image of D(a/s) is precisely H intersect D(a). This proves the claimed subspace topology with no appeal to an uncited inverse-limit theorem. Step 3 constructs both quotient maps and checks fraction equality, surjectivity and the kernel explicitly; no non-elementary quotient/localization lemma is hidden.

Step 4 reads localization-flat, localization-base-change, localization-units-or-zero, and flat-ring-map-iff-flat-affine as their statements say. Base change applies with D=L and arbitrary denominators T; every image denominator is a unit in L, so multiplication is inverse to the resulting localization isomorphism. This verifies flat diagonal rather than confusing formal etaleness with weak etaleness. The definition node weakly-etale-morphism supplies the flat-plus-flat-diagonal convention. The basic-open node gives each R_f image. Morphism-affine-schemes-affine gives affineness over every affine open, which is needed to verify the full proetale-covering definition. Joint surjectivity alone was not taken as that definition.

Step 5 uses the faithfully-flat-surjective-spectrum statement for B to D, the weakly-etale composition statement for the composite over R, and the ind-etale-algebra node only for its explicit ring/scheme weakly-etale convention, not for a nonexistent ind-etale assumption. Affineness and the covering definition verify the replacement family. The cover-section node has exactly the supplied retraction hypothesis, and states an actual scheme section of the coproduct, not merely a section after another cover. The rings and the finite family fit a common universe; there is no smallness gap.

Step 6 uses scheme-coproduct-family for its explicit open-and-closed summand property. Localization-prime-residue-field-iso identifies the primes as extensions and gives the needed points; inclusion pB contained in qB is elementary ideal monotonicity. I checked that the specialization stays inside Spec B because q containing I cannot meet S. The clopen argument works in both directions of specialization. The open-immersion definition allows restricting the morphism's space and sheaf maps to the summand. It does not use the invalid inference that a pointwise contained map factors through an arbitrary closed subscheme.

Step 7 uses affine-spectrum's full faithfulness and contravariant functoriality to get an R-algebra homomorphism. Agreement on R forces agreement on every fraction and proves the B-algebra retraction identity. The units-or-zero node justifies the I=R edge case. I tested R=0, I=R, I=0, nilpotent I with r=0, a nonzero field, and a finite product of fields with a proper component ideal. With r=0 the hypothesis forces V(I)=Spec R and all primes remain; no complement summands are needed. With empty V(I), I=R and B=0, while the complement basic opens cover. A field with I=0 gives B=R and the retraction assertion tautologically specializes correctly. A product of fields gives the expected component localization and clopen decomposition.

Against delivery-errors B-E: no new statements, proofs, or clause-restatement children were created; every non-elementary fact is a cited statement, with its verbatim full statement in citations.json. The only off-unit non-leaf tool is the general localization prime correspondence and is reported here for the maintainer to record as a tool use (C8). The dependency traversal found no path from a cited node back to the item. No statement dispute, changed coefficient category, or altered base-change morphism is involved.

## Second reading by NE

- Item statement: checked against proetale.tex Tags 096V, 0987, 09AH and algebra.tex Tag 00E3; all hypotheses (finite list including r=0, multiplicative closed localization, covering, and retraction conclusion) agree.
- Step 1: checked the localization prime correspondence and the specialization criterion against the cited node statements; the maximal-ideal argument and fraction identities are explicit, with no hidden Noetherian or Jacobson hypothesis.
- Step 2: checked the basic-open topology argument against the cited basis statement; the image and inverse-image descriptions establish the subspace homeomorphism.
- Step 3: checked the quotient map and kernel computation directly from fraction equality; the zero quotient and surjectivity edge cases are covered.
- Step 4: checked flatness, tensor localization, diagonal flatness, weakly-etale status, affine maps, and the fpqc covering definition against every cited statement; finite basic-open coverage is explicit.
- Step 5: checked faithful-flat spectral surjectivity, weakly-etale composition, replacement of the localization member, and the w-contractible section theorem against their statements; no ind-etale assumption is imported.
- Step 6: checked the coproduct summand, specialization, clopen preservation, and open-subscheme restriction against the cited statements; factorization is through an open-and-closed summand.
- Step 7: checked affine-spectrum full faithfulness and the fraction calculation for the retraction; the R=0, I=R, I=0, r=0, field, nilpotent, and product-of-fields cases were tested.
- New nodes: none; therefore B1–B7, duplicate checks, and Mathlib-leaf checks introduce no new-node obligations. Existing localization and cover-section nodes were searched and cited.

Changes made in this second reading: removed worker-written `split_report.tool_uses`, which C8 reserves to the maintainer; the off-unit localization prime correspondence is reported above with its justification. Preserved the existing node’s original creation provenance. No mathematical statement or proof step required alteration. The documented delivery command rejects a trailing dot, so the supported command without that argument is used.
