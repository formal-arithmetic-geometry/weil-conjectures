# Q22: lem-sfb-lft-group-etale-component-quotient

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-lft-group-etale-component-quotient.json: item, statement; split in eleven steps. Mathlib searches found no match for the complete assertion. No new nodes and no new Mathlib leaves.
- citations.json: one entry for every step/node citation, quoting the exact complete statement of the cited node, including its hypotheses.
- report.md: this report. searches.jsonl contains the five actual new search calls; assemble.py is sandbox-only preparation, not a delivered project file.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, component quotient, identity component and group-scheme terminology. The group-scheme Basic.lean identity-component declarations cover only parts of the input and impose additional quasi-compactness assumptions; they do not supply the quotient, arbitrary-base universal property and compatibility. No exact sorry-free project declaration was found. Mathlib declarations are not treated as project attachments.

## WANTED

None. The Stacks sources needed for the assembly are present locally. No SGA route is used.

## Corrections and route

The original item was unsplit. Its statement is retained in full, with no new hypothesis and no removed clause. No statement dispute was needed. In particular finite presentation, not merely local finite presentation, and arbitrary schemes B and arbitrary etale targets Z are proved. The live item's prior source, provenance, blueprint chain and searches are retained.

Read GOAL.md, the worker contract, the open stage-1 contract, SETUP.md's three levels, the chapter and unit records, and delivery-errors B through E. The inherited auxiliary belongs to the field-fibre input to the trait effectivity argument along the recorded ancestry of the direct-images stability unit. blueprint_refs ancestor returned the inherited null ancestor and via chain. Whole current-blueprint searches for component quotient, the etale component quotient, and 0B7R found no separate duplicate. No unit realization is changed: this item is not the key node of the unit. The five generic off-unit statements are explained individually in split_report.tool_uses; the rest are definitions, Mathlib leaves, or existing statements of this unit.

The first draft of the argument could have silently used rational points over an algebraically closed field or the false principle that maps equal on points are equal on a nonreduced scheme. The delivered argument avoids both gaps: step 8 chooses a point with its actual residue field and descends connectedness along a surjective field base change; step 9 uses the open diagonal and hence the actual open equalizer. Likewise it does not assume that the identity-component input already states normality; step 1 proves it with its given scalar-extension equality and open factorization. Finite presentation is not taken from the free quotient lemma, which gives only local finite presentation.

## Unfinished work

None at stage 1. No Lean is written and no compiler, Lake or build is run. The existing prerequisite nodes remain the stage-1 dependencies; this delivery does not claim they are all formally proved.

## Not duplicates

No new nodes were created. All ingredients are reused from the existing DAG, so there are no new/existing same-tag pairs to distinguish.

## Review by Q22

I read Stacks groupoids.tex, proposition-connected-component (Tag 0B7R), bootstrap.tex, lemma-quotient-free-action (Tag 06PH), stacks-morphisms.tex, lemma-quotient-etale (Tag 0DU1), and spaces-over-fields.tex, lemma-locally-quasi-finite-over-field (Tag 06S0). These are the item's actual construction sources. The source's general neutral component becomes the clopen open-subscheme component in the already reviewed input lem-sfb-lft-field-group-neutral-component. I opened every cited DAG statement and compared the clause used, including the actual full Yoneda lemma, the chart meanings of space properties, the covering hypotheses for descent, and the local-equality clause of sheafification. There are no new nodes requiring independent source or search records. The following checks explain the mathematics of each step rather than only its syntax.

1. The neutral-component node states finite type, geometric irreducibility and equality after every field extension, without perfectness or quasi-compactness. It does not state normality. At a point of H times C, its residue field gives two field-valued coordinates; conjugation fixes the identity component after that extension. The cited open-factorization node promotes the resulting set-theoretic containment to a scheme morphism into C. This is why the original nilpotents are retained and normality holds on all test schemes.

2. The flat-over-a-field node applies to arbitrary schemes, so it applies to both H and C. A field is Noetherian directly from its two ideals and the cited local-Noetherian definition. The locally-Noetherian-base LFT-to-LFP Mathlib node applies with that base, both to the assumed LFT H and to finite-type C. The scheme-as-algebraic-space definition uses the actual representable sheaf, so the subsequent quotient is not a different functor.

3. Cancellation verifies the free-action hypothesis of 06PH; flatness and LFP were established in step 2. Its statement supplies all of the space quotient, local sections and exact kernel-pair isomorphism used here. The inverse formula xy^{-1},y verifies the open relation, using the open-factorization node rather than an unspecified representability claim. The 0DU1 node applies to H over Spec k because that structural map is flat LFP and the relation really is an open immersion; it identifies its quotient with the same orbit sheaf.

4. The etale-space node supplies chartwise local quasi-finiteness, not just the scheme case. Each chart is etale over the reduced field, so the etale-reduced statement proves reducedness in exactly the atlas sense in the field-decomposition node. That node does not assume separatedness or quasi-compactness and permits an infinite disjoint union. The identity chart then verifies ordinary scheme etaleness; the chart-test node explicitly identifies scheme and space flat/LFP properties. No circular reliance on separatedness of E is needed for representability.

5. Normality makes orbit classes a presheaf of groups. The cited local-representative and local-equality theorem makes multiplying locally chosen classes independent of all refinements and representatives. Thus group laws hold as sheaf equalities. The full Yoneda node, whose statement is Hom(h_X,F)=F(X), gives the actual representing morphisms; def-sc-group-scheme identifies those laws with a group scheme. The field-group separatedness theorem has no smoothness or finite-type hypothesis, so it applies to this E.

6. The space covering-calculus node turns q into an fppf singleton covering and agrees with the scheme topology. Its base change of q is C times H to H by the exact relation already proved. The finite-type base-change node applies because C/k is finite type; finite-type target-local descent is precisely one of the four properties in the cited descent node. Hence q is quasi-compact. Separated cancellation uses the assumed separated composite H/k, and separated-implies-quasi-separated supplies the remaining condition in the cited finite-presentation definition. No claim that H is quasi-compact occurs.

7. Arbitrary B is allowed by the covering-calculus base-change statement. The base-changed relation is an isomorphism of representable sheaves by the fibre-product universal property. Local lifts exist because q_B is an fppf covering; equality of two lifts is equivalent to the unique ratio in C_B. The sheafification node then identifies the quotient on every B-test, with no restriction that B be a field or reduced. The fibre over the identity is exactly the actual subgroup scheme C_B, as the relation formula with second coordinate identity shows.

8. Etale base change and the cited fibre theorem show that E over an algebraically closed extension is a discrete union of copies of that field. The fibres of q are consequently clopen. Nonempty fibres are torsors; choosing any point and its residue field trivializes the torsor after that extension using the explicit relation. Geometric irreducibility of C from step 1 makes that trivialization connected. Surjective-base-change, whose statement allows all scheme maps, makes F_L to F surjective. A clopen separation cannot survive this surjection from a connected space. Thus the clopen fibres are precisely maximal connected components, including their induced open structure.

9. The etale and unramified definitions give an open diagonal even for nonseparated Z/B. Its pullback is the open equalizer W. On each geometric fibre over h, C is connected by step 1 while the cited etale-fibre theorem, after the cited etale base change, makes Z a discrete union of Spec Omega. A map into the selected Spec Omega is the unique Omega-morphism, so the equality holds as a morphism on that fibre. Every point of R lifts to such a geometric point. Hence W contains every point; the open subscheme on the full underlying open is R itself. This proves actual equality of the two maps without inferring equality of maps merely from pointwise equality.

10. The fppf-to-fpqc node supplies exactly the covering hypothesis of representable descent. Both source E_B and target Z are schemes, already proved, so the descent node gives the claimed unique scheme morphism. Applying uniqueness once more with target B proves it is over B. This gives both existence and injectivity of the Hom bijection. The quotient identifications commute with further base change because they agree on all locally lifting sections, rather than because arbitrary base change was presumed to commute with sheafification.

11. The etale-base-change node supplies etale targets E_i over the common B, even though the two fields need not embed into one another. The Hom bijection just proved constructs both maps and makes their composites identities. Local lifts along q_1 verify multiplication, identity and inverse for the induced isomorphism, using the sheaf equality axiom. The same uniqueness forces identity, composition and further-pullback compatibility. No new non-elementary lemma is hidden in this use of a universal property.

I checked the statement against Spec k and connected groups (E=Spec k), finite etale and infinite constant groups (C is the identity point and E=H), products of an infinite constant group with a connected group (q is quasi-compact despite H being non-quasi-compact), infinitesimal groups such as alpha_p (their nilpotents are retained), and inseparable field extensions. For arbitrary B I checked empty and nonreduced bases and an etale doubled-origin target: the open equalizer argument still works without assuming the diagonal closed. Every non-elementary input is a cited node or an earlier proved step; all eleven step texts are below 2000 characters, and no step is a restatement of an item clause delegated to a fresh node. I compared the delivery-error checklist for completeness, duplicate creation, C1 hidden inputs, C4 mismatched hypotheses, unjustified topology change, nilpotent structure, and the full arbitrary-base scope. The item statement and all previous provenance are unchanged.
