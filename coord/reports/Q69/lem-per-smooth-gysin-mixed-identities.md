# Q69 stage-1 delivery: lem-per-smooth-gysin-mixed-identities

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-smooth-gysin-mixed-identities.json — existing statement node, now split into ten explicit steps; not a Mathlib leaf.
- citations.json — a verbatim statement quote for every step/node citation.
- report.md — this report. The sandbox also retains the previous searches.jsonl and source-read extracts, and a local write_split.py used to serialize the split.

No new DAG nodes, definitions, or Mathlib leaves. No unit changes: the item is not the unit's key node. No Lean written and no compilation performed.

## Attachments

None. Read-only searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact item/tag and for Gysin/gysin and mixed identities returned no matching declaration. The existing SmoothDuality module concerns unoriented duality and cannot attach this item.

## WANTED

None: the needed source texts and blueprint proofs are present locally.

## Corrections and route

The imported item had no proof. Its statement is preserved, including arbitrary Noetherian bases, prime-power coefficients, ordinary etale categories, supported classes, and the specified DNC orientation. No STATEMENT-DISPUTED correction is needed.

The narrower existing lem-per-smooth-immersion-interchange has the same two conclusions only for regular affine excellent schemes and F_ell coefficients. It cannot prove the present statement, and some downstream regular Gysin nodes depend on this item's ancestor; those are not used. Its explicit adjunction calculation provided a useful comparison, but this delivery cites the existing prime-power class calculus and general-Noetherian orientation statements at every place where their larger scope is necessary.

The source XVI 2.5.7 invokes a classical smooth trace, which is outside the permitted route. Steps 3–5 replace that input by the canonical counit-defined exceptional mate and naturality. XVI 2.5.8 reduces to a field; Steps 6–10 instead use smooth section charts over the original base and the ordinary finite-ring projective-line adjunction. No classical trace theorem is an input. The Kummer-normalized projective-line counit is the affine/diagonal lecture-notes construction authorized by the route.

The existing lem-sc-connective-single-hom is not cited: its general statement is stronger than the needed degree-zero full faithfulness. The correct generic tool here is lem-weil-pbc-derived-single-fully-faithful (Stacks 06XS). No change to that other node is made.

The item statement's references to proper morphisms and compactifiability are retained as the imported conventions. New proof dependencies are actual structural tools used in the displayed computations, with off-unit explanations in split_report.tool_uses.

## Mathlib and duplicate searches

Read all five records in the sandbox searches.jsonl and the detailed search output already recorded on the current repository item. Those records include two LeanFinder phrasings (interchange, then section cancellation), Loogle, grep, and LeanSearch. The hits concern scheme pullbacks, cotangent linear maps, or unrelated group sections, not supported etale fundamental classes and DNC orientation identities. The grep hits are unrelated strings including Thom in personal names and castHom. No search is newly fabricated or repeated. The item itself retains its original exact searches, results, and dates.

Searched the whole DAG by Gysin, Kummer, mixed identities and section deformation, and ran blueprint_refs.py ancestor plus whole-blueprint searches for Gysin, interchange and section cancellation. Existing nodes provide every required input, so no new node needs an absence verdict or a duplicate-pair exemption. same_as remains []: none of the blueprint nodes states the present arbitrary-Noetherian mixed identities.

## Review by Q69

I read the item's source in the retained Gabber extract, Expose XVI 2.5.7–2.5.10 (printed pages 240–241), and Scholze Theorem 7.19 with its proof. I read the current blueprint's DNC proof, orientation-charts proof Steps 1–4, affine-space/zero-section proof passages, and the nearest ancestor's proof Step 3. The unit and chapter records were read: this item is a general duality input below that ancestor, not a replacement of the Fourier-exactness unit route. I opened and read the statement of every node cited below; citations.json quotes those statements literally. No new nodes have a source to audit.

Step 1 uses smooth dimension permanence and smooth flatness to meet the flat-pair hypothesis in the prime-power regular-immersion calculus. That statement actually asserts supported-class flat base change and fixes its Kummer sign; it is not merely a definition of a class. The Tate-pullback statement supplies the canonical twist identifications. No excellence or ambient regularity was introduced.

Step 2 reads the orientation's actual diagonal/DNC chain against the finite-ring section-deformation statement's coordinate normalization x_j=t u_j. That statement identifies the affine-space orientation with the adjoint of the Kummer coordinate-tower counit, precisely the counit defined by lem-amb-affine-space-top-trace. Applied to diagonal difference coordinates, it fixes the comparison used later on affine space. This is not equality inferred from isomorphic rank-one objects.

Step 3 uses the prime-power orientation's base-change clause, the exceptional mate's counit characterization from prop-asd-smooth-base-change, compact-support exchange on D+, and mate-pasting. It writes the counit equation explicitly and substitutes gamma compatibility into it. Thus the trace compatibility used in Step 4 has been derived rather than imported from a disallowed trace construction.

Step 4 verifies the closed-supported endpoints before using full faithfulness. lem-kun-04ca supplies full faithfulness and i^{-1}i_*=id; the supported-kernel node supplies exactness. Exact inverse image preserves the derived adjunction, including its invertible counit; carrying module actions through these same maps gives the constant-ring module assertion. The proper projection formula is used for j, a closed immersion, only to move the rank-one Tate line through its pushforward. The identity-open compactification and coherent compact-support composition give the two endpoint identifications. All compact-support exchange inputs are constants with shifts/twists and exact closed direct images, hence bounded below.

Step 5 applies counit naturality to the supported map c_i and writes the two paths with their common source and target. The composite-adjunction node explicitly says its Hom bijection is successive transposition, giving the two displayed star products. The target twist is c-r and the shift 2(c-r), as in the item's definitions. The tensor-defined smooth comparison supplies the twisted version. This is a few-line categorical calculation from Steps 1–4, marked elementary, not a new theorem node.

Step 6 uses the arbitrary-Noetherian section-deformation statement for regularity of the section, and the separate smooth-pair local-coordinate statement (Stacks 0FUE, more-morphisms.tex lemma-etale-local-structure). I read that lemma and divisors.tex lemma-immersion-smooth-into-smooth-regular-immersion (067U). Taking the smooth source of the immersion to be S gives a=0, since it is etale over S itself, and b=r. Shrinking the base makes the whole section lie in the chart. Affine source charts make the etale map separated. Noetherian permanence and Nagata check that all chart maps needed by the exceptional formulas are in scope.

Step 7 uses the definition of a divisor line bundle as the dual ideal and computes its two-chart transition, rather than quoting an uncited divisor-degree assertion. The supported Kummer statement gives c u=+c_1(O(D)); the ordinary finite-ring P1 adjunction gives exactly t h=1 for h=c_1(O(1)), with no field restriction. The composite-unit formula proves that the supported map after projection is h, fixing the sign.

Step 8 applies open restriction of the supported map and the composite affine-line adjunction specified in the affine-space counit node. The composite-counit formula identifies its zero-section evaluation with the projective-line evaluation of Step 7. Step 2 identifies its transpose with the chosen DNC orientation. The regular-immersion calculus identifies the section class with this supported Kummer transpose.

Step 9 is induction with the dimension-zero base, the last-coordinate projection, and its zero section written explicitly. Both class nodes assert exactly the composition laws used. The tower base A^{d-1}_T is still Noetherian and ell is still invertible. Associativity is the coherent composition/composite-adjunction formula, so this induction hides no independent orientation-comparison lemma. It is marked elementary because each induction step is substitution of those formulas and the preceding rank-one evaluation.

Step 10 uses the already proved interchange for the etale chart e and zero section, where the pulled-back smooth edge is the identity because the centre square is Cartesian scheme-theoretically. The smooth class composition law and etale dimension-zero normalization then reduce the composite to Step 9. Etale adjoint locality and the class restriction clauses relate this chart to the original pair. The two final maps are endomorphisms of Lambda_S[0]; degree-zero full faithfulness reduces them to sheaf maps, and the sheaf axiom proves equality from the Zariski cover. This avoids the false principle that arbitrary derived maps can be checked locally.

Small cases checked: empty schemes, c=0, r=0, identity immersions, an etale map with a clopen section, the affine-line zero section over a nonreduced Noetherian base, and n>1. None requires Lambda to be a field; the positive Kummer divisor class gives +1, and all shift permutations are even. No inverse of a regular-immersion class was used, so no absolute-purity hypothesis on singular ambient schemes is hidden. All ten steps have fewer than 2000 characters; the proof contains no long concealed lemma.

Against delivery-errors B–E: no statement-only child was turned into a proof, no new elementary or duplicate node was created, no item clause was relabelled as a child, no extra hypothesis was assumed, no unsupported class was substituted for a supported one, and every non-elementary input is cited at its use. Existing statement and import/blueprint metadata are retained. The citations and dependency union are serialized from the actual uses lists.

## Unfinished work

None in the one-level split. The cited unsplit inputs remain separate DAG items, as required by stage 1.
