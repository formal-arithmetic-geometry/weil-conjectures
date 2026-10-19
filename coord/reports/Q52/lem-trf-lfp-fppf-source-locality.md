## Files written

- dag/nodes/sec-trace-formula/lem-trf-lfp-fppf-source-locality.json — statement, split into eight steps; original statement unchanged.
- dag/nodes/sec-trace-formula/lem-trf-finite-presentation-fppf-source-algebra.json — statement-only algebra input, unsplit; no Mathlib match, but an existing project theorem is recorded for attachment and independent transitive audit.
- citations.json — sixteen step/node pairs with verbatim statement quotations.

## Attachments

Algebra.FinitePresentation.of_finitePresentation_of_faithfullyFlat belongs to lem-trf-finite-presentation-fppf-source-algebra, WeilConjectures/Mathlib/RingTheory/Finiteness/Descent.lean:231-265. Its proof has no sorry. The historical full sorry map has no entry for this declaration, so I have not asserted a closed transitive audit. The node remains statement-only with audit state none and the declaration recorded, allowing the maintainer to verify its dependencies. Its explicit scalar-tower hypotheses merely express that R → B is the composite; arbitrary ring maps supply these algebra structures. The three rings in the natural-language statement can be placed in their maximum universe.

No project declaration found by the item tag or notion states the complete family equivalence. AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective, WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:127, proves only the converse for a single surjective map. I read that file in full and did not claim it attaches the item.

## WANTED

None.

## Findings and corrections

The item was statement-only. Its statement agrees with Stacks Tag 036N, including arbitrary jointly surjective fppf families. No statement dispute or correction was necessary. I expanded the affine-family reduction that Tag 036N delegates to Tag 036H; the latter's proof says “Details omitted.” The expansion uses the finite affine-image selection of Tag 02KL, with the family indices retained. I did not turn that omitted argument or the singleton converse into a new node restating the item.

Initially I considered introducing a general source-locality criterion. That is unnecessary: the existing affine-basis, openness, coproduct, affine criteria and faithful-flatness nodes carry the geometric reduction. The only new node is the genuinely algebraic input, Tag 02KK.

I searched the whole DAG by 036N, 036H, 02KK, 01TQ, 01TR, the ring-tower wording and the full project declaration; read the relevant statements; and ran blueprint_refs.py ancestor and searches for finite presentation, finite-presentation, faithfully flat, 036H, 02KK and fppf local on the source. None states the new algebra theorem. Existing Mathlib tensor-product descent is target base-change descent and cannot be silently substituted for source precomposition. The recorded Mathlib queries are the actual msearch commands; I read their output and the candidate source. Both natural-language phrasings return composition/cancellation results, not the desired algebra source descent. Existing item searches were read and retained, including the creator's distinction between source descent and base-change descent.

## Not duplicates

No existing node carries Tag 02KK. The following are the nearby statements explicitly compared:

lem-trf-finite-presentation-fppf-source-algebra vs lem-a1-finite-type-fppf-source-algebra: the latter assumes and concludes finite type over R; this node assumes and concludes finite presentation over R.

lem-trf-finite-presentation-fppf-source-algebra vs lem-weil-pbc-finite-presentation-descends-faithfully-flat: the latter is descent of a fixed algebra after faithfully flat base change, whereas this node cancels a faithfully flat finitely presented map A → B in the tower R → A → B.

lem-trf-finite-presentation-fppf-source-algebra vs lem-weil-pbc-fpqc-descend-locally-finite-presentation: the latter descends a scheme morphism after a cover of its target; this is a ring source-precomposition theorem and needs finite presentation of A → B.

## What remains

No part of the item's natural-language proof remains unfinished. The new algebra node is not recursively split, as required. Its existing project declaration awaits the maintainer's independent transitive audit; this delivery does not claim completion of that audit.

## Review by Q52

I read descent.tex Tag 036N (lemma-locally-finite-presentation-fppf-local-source), the full statement and omitted-details proof of Tag 036H (lemma-properties-morphisms-local-source), the proof of Tag 02KL (lemma-flat-finitely-presented-permanence), and the statement and full proof of Tag 02KK (lemma-flat-finitely-presented-permanence-algebra). For the finite-presentation criteria I read morphisms.tex Tag 01TQ (lemma-locally-finite-presentation-characterize), including its arbitrary affine-pair clause and open restriction clause, and Tag 01TR (lemma-composition-finite-presentation). The item's chapter and unit were read: this is a general scheme-theoretic tool in the recorded historical semistable auxiliary branch, and does not replace any unit-level trace argument. No unit or chapter was edited, and no SGA source is used.

Step 1 uses exactly the statement of lem-sbc-locally-finite-presentation-composition, with both maps locally finitely presented; this proves the forward implication without flatness. Step 2 uses the affine-open basis statement twice, and the pointwise definition of local finite presentation to specify precisely what must be proved. I checked that W is chosen inside f inverse(V), and that the T_{i,alpha} are affine opens of the original U_i, not assumed-affine intersections.

Step 3 reads the statements of lem-weil-pbc-flat-morphism-affine-criterion and lem-weil-pbc-lfp-affine-opens-finite-presentation literally: each gives exactly the ring property for the affine pair to which it is applied. The hypotheses flat h_i, lfp h_i and lfp(f h_i) are all present. In particular I did not cite the definition of flatness for an affine sections theorem.

Step 4 uses the explicit open-map conclusion of lem-weil-pbc-flat-lfp-open, and only the quasi-compactness clause of lem-weil-pbc-affine-scheme-qcqs. Joint surjectivity lifts a point into one U_i; its affine-basis cover then supplies an image containing it. The open images therefore form an actual covering of W. Finite extraction is just the definition of quasi-compactness. Neither the family, its members, nor h_i is assumed quasi-compact.

Step 5 uses both the universal property and the open disjoint component assertion in lem-weil-pbc-scheme-coproduct-family. The finite-affine-coproduct-spectrum statement supplies the affine identification with Spec(product B_j), with its component maps, not merely an unrelated abstract isomorphism. This explicitly fixes the tower used later. Step 6 is elementary from the pointwise definitions: the local rings are unchanged on open neighbourhoods, and each point lies on one affine component whose ring presentations were already obtained in Step 3. It proves flatness of q and local finite presentation of q and p without invoking a hidden finite-product algebra theorem.

Step 7 again uses the affine-pair criteria, now for whole affine schemes, and the exact converse-to-surjectivity statement of lem-weil-pbc-flat-surjective-spectrum-faithfully-flat. Its ring-flatness hypothesis was established before applying it. Surjectivity of the scheme map is surjectivity of prime contraction under the specified affine identifications. Step 8 uses precisely the new ring-tower statement: R → B finitely presented, A → B faithfully flat and finitely presented. The pointwise lfp definition then finishes the argument for every x. Every node cited in all eight steps was opened and its statement read; citations.json quotes those statements verbatim, not their proofs.

The new algebra statement agrees hypothesis by hypothesis with 02KK and the complete project declaration at lines 231-265, which I read. It contains no proof sketch and no steps; it names the existing definitions of finite presentation and faithful flatness, has precise blueprint ancestry and no same_as match, and records actual searches. It is strictly smaller than the scheme-family equivalence: affine ring source descent is the algebra input, while finite refinement and both implications remain in the item.

I tested the zero-ring and empty-scheme cases. If X is empty, lfp is vacuous, including the empty family. If X is nonempty, a chosen point forces a nonempty affine W and the selected images cover it. The finite-coproduct assertion also permits an empty finite set. In 02KK, A = B is immediate, and if B = 0, faithful flatness forces A = 0; the conclusion is then valid. Dropping finite presentation of A → B would be invalid and was not done. No Noetherian, separation or global quasi-compactness hypothesis entered the argument. All steps have fewer than 2000 characters; none hides an inline independent comparison lemma. This is the worker's self-review, with the maintainer's independent review still to follow.
