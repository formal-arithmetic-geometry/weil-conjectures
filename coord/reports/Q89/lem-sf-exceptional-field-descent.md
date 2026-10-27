# Worker report: lem-sf-exceptional-field-descent

## Files written

- dag/nodes/sec-six-functors/lem-sf-exceptional-field-descent.json: split into nine steps; original statement, statement dependencies, source and maintenance metadata retained. No new nodes; no new Mathlib leaves.
- citations.json: verbatim statement passages for every cited node in every step.

## Attachments

None. Searches by blueprint tag and exceptional/rational/common-field notions found no project declaration giving all clauses. BoundedConstructibleUpperShriek.lean:179–228 supplies rational upper-shriek constructions and a proper-case adjunction, but does not establish the nonproper construction, normalized scalar comparisons and common-stage adjunction of this item. These partial declarations are not an attachment.

## Wanted literature

None.

## Findings and corrections

The fresh sandbox contained only dispatcher markers. I used the current live unsplit node. There is no released repair note for this item. Its three assigned old proof steps are preserved verbatim below from the Q154 parent report. Their arguments are retained and expanded, rather than moved into newly named copies of the item.

The key domain hazard is absolute separatedness: lem-pur-rational-lattice-adic-domain and lem-sf-package-qbar-adjunction-map-descent assume separated source and target schemes. Neither applies to this item. The existing lem-coef-integral-residue-tor allows an arbitrary scheme and identifies the actual integral category with the finite-Tor category. Generic pair descent then works without a geometric separatedness hypothesis. This avoids introducing a duplicate nonseparated version of either specialized statement.

The parent-generated blueprint ancestor chain is broken: tools/blueprint_refs.py ancestor lem-sf-exceptional-field-descent prints None. I preserved blueprint.from (including its exact tensor–Hom place and via list); I did not edit created metadata or invent an ancestor. The report's blueprint entry explains the actual source route.

The rational-left normalization is a choice of the supplied prescribed integral-left identification, not a new theorem about arbitrary isomorphic functors. Step 3 gives both the literal normalized presentation and the formula using the original u_R. Its counit changes by precomposition with the inverse left identification. Thus localization is never used to erase the integral-left realization. Step 4 explicitly sends h/varpi_E^r to T(h) times the inverse image of varpi_E^r; replacing it by a denominator varpi_L^r would be wrong for a ramified extension.

The new proof adds explicit right mate coherence and the unit equation before descending Hom bijections. Step 7 checks enlargement in both directions, rather than asserting that Hom bijections automatically pass to a colimit. There is no claim that an adjunction bijection preserves arbitrary composition as a functor: the two naturality equations are what is needed. The operation actions preserve identities and composition, as required.

## Searches and existing tools

I searched the whole DAG by titles and statement concepts for rational adjunctions, scalar localization, common-field functors, mate pasting and integral Tor domains; read each selected statement in full; and searched the entire blueprint with blueprint_refs.py for field descent, scalar localization, common-stage and residue Tor. Existing generic tools cover every supporting fact, so no new node is needed. No Stacks-tag-based new node was created.

Actual msearch.py queries are recorded in searches.jsonl and appended to the item's older searches. Both semantic phrasings were read. LeanFinder and LeanSearch returned CategoryTheory.Adjunction.localization, localization component formulas and module scalar-extension tools; Loogle returned an Ext linear-equivalence theorem, whose reported MapAdjunction module is absent from this pinned Mathlib checkout. It cannot establish this item's full construction. The grep returned bicategorical mapAdjunction declarations. I read Mathlib/CategoryTheory/Localization/Adjunction.lean:89,118,125; its genuine generic adjunction transport is already represented by lem-sfb-adjunction-localization, so it does not warrant a new leaf or an attachment. The proof instead uses the explicit Hom formulas and the existing natural-bijection node. No query that was not run has been added.

Off-unit citations are generic tools, declared individually in split_report.tool_uses: residue Tor, semilinear localization, formal mate pasting/unit compatibility, pair-category descent and reconstruction from natural Hom bijections. The other off-unit citations are the definitions of precisely the published categories and left functors. None replaces the six-functor unit route by a different geometric theorem.

## Not duplicates

No new nodes. In particular I reused lem-coef-integral-residue-tor, lem-pur-semilinear-scalar-localization, lem-weil-pbc-mate-pasting, lem-pur-mate-unit-compatibility, lem-sbc-coherent-pair-functor-descent and lem-weil-pbc-adjunction-of-natural-bijection instead of making specializations.

## Review by Q89

I read the exceptional inverse-image coefficient paragraph in the main-20261015 blueprint, the sk-thm-sf-tensor-hom third Hom bijection and compatibility conclusion, the current six-functor chapter and compatibility unit, and the Q154 allocation of returned steps 17–19. I read Zheng Propositions 2.23, 2.29, 3.16 and Section 5, especially Lemma 5.22 and Proposition 5.24, from the available PDF. These justify the ordinary etale/system background taken as input here. They are not asserted to state this precise ordinary pro-etale raw-localization/common-field construction. This proof is therefore labelled agent-written. The three coefficient definitions and the existing generic supporting statements supply the more precise interfaces. There is no SGA citation or alternate purity route.

Step 1 uses exactly the equality and uniform residue Tor interval stated by lem-coef-integral-residue-tor. I checked its hypotheses: the prime differs from the characteristic, R is the finite-extension DVR, and K is in the actual derived-complete category. Its X is an arbitrary scheme, not an absolutely separated one. The rationalization definition then has exactly those integral objects.

Step 2 applies the semilinear localization statement with identical source and target rings. That statement explicitly preserves exactness, shift maps, natural transformations, whiskering and equations. It supplies more than an underived localization universal property. The two Hom maps are given in formulas and their inverse equations follow from the actual integral triangles. The natural-bijection theorem explicitly identifies unit and counit by the images of identity maps, so it gives the same localized adjunction rather than an unrelated right adjoint.

Step 3 uses the compact-support definition for the specified tower P_R and its rationalization, and the rationalization definition for the unchanged objects. The supplied integral-left identification is retained as Q u_R when the transported presentation is used. Precomposing the counit with its inverse is the elementary adjunction transport formula: its Hom map sends v to the old transpose of v u_R, and its inverse sends w to the old inverse transpose followed by u_R inverse. This explains the normalization rather than treating a definition as a theorem of independence of compactification.

Step 4 uses the semilinear statement with the actual map R_E to R_L. The required invertibility of the image of varpi_E holds since it is a unit times varpi_L^e. I checked the fraction formula against the actual rationalization definition. That definition uses precisely completed integral scalar extension, and the semilinear theorem states naturality and equation preservation also for localized fractions. All q,b components and shift equations therefore remain the prescribed ones.

Step 5 cites the full mate-pasting statement: part (1) gives pasting along the coefficient functors and part (4) gives identities. Its square is alpha=q inverse, which is the correct direction for the assumed right b. The mate-unit statement gives the displayed unit equation with that same alpha. Invertibility of b is an input, not inferred from invertibility of q.

Step 6 uses the pair-descent theorem's actual formula b_target inverse Phi(h) b_source, not a construction hidden in its proof. I verified its small directed finite-field index, additive transitions, canonical associators, identity transitions, pentagon and comparison tower laws. These are the common-stage category data and balanced coherence from steps 4–5. I use only its pair assertion, not its optional extension to Karoubi envelopes.

Step 7 uses the common-field definition's explicit equivalence relation on representatives. Its natural-bijection citation states both naturality equations and both identity formulas for unit/counit. The displayed enlargement calculation uses naturality of b and the unit equation; the inverse calculation uses the counit equation. These are already proved for the actual comparisons, so no filtered-colimit exactness assertion or new representability lemma is silently invoked. At a common field the recipes are the original inverse maps, and this proves bijectivity and naturality for all represented arrows.

Step 8 uses the transformation clause of pair descent for the shift maps, and the common-field definition's representation of every distinguished triangle over a finite field up to isomorphism. Exactness is checked on that finite representative. This does not claim an exactness theorem from the additive part of pair descent. Step 9 is elementary once step 7 gives the actual adjunction: both sides of each inclusion comparison are the same pair, and the counit is represented by the same finite-field counit. The transpose of the identity left comparison is the identity right comparison by the finite adjunction triangle. The compact-support definition explicitly gives the same pair for the closed left functor.

For B–E I checked every node citation against the statement itself; citations.json contains actual verbatim passages. No non-elementary fact is assigned to a definition alone. No node is created, no clause is renamed as a supporting lemma, and no supporting dependency reaches the item. Every new step is under 1100 characters, so there is no long step hiding an additional lemma. All source hypotheses are preserved, notably relative separatedness only, characteristic distinct from ell, positive reduction indices, raw categories with unchanged objects and common finite fields. The item statement is unchanged, so there is no statement dispute.

I tested zero objects and the empty scheme (all Hom maps and adjunction equations are zero/identity equations), f equal to the identity (the scalar comparisons give the actual unitors), E=L and repeated fields (mate identity and normalized associators give identity), ramified E inside L (the denominator is the image of varpi_E and becomes a unit), and a varpi-power-torsion integral representative (it is still a permitted object even when its rational image is zero). I also tested representatives defined over different fields and equal maps whose equality only appears after enlargement: step 7 explicitly uses that later common field. No finite coefficient reduction on the closed category or unrestricted ambient exceptional adjunction is introduced.

## Unfinished work

None for this one-level split. The general supporting nodes already exist and retain their own statuses.

## Retained returned steps 17–19 (verbatim)

Old step 17: By the residue-Tor theorem every integral constructible representative belongs to the integral finite-Tor category. Localize the $R_E$-linear operations, natural transformations and adjunction Hom bijections at $\varpi_E$. The inverse localized Hom maps remain inverse because localization preserves the equations for their composites; the resulting unit, counit and triangles are their images. Raw scalar localization has the same objects and localized Hom modules, with exact localization functor. Hence the localized adjunction acts on exactly the published rational categories, and its operations and coefficient maps are exact with the induced shifts. Choose its left functor to be the published rational compact support and its rationalLeft realization to be the identity identification. This does not require a Karoubi completion.

Cited nodes: lem-coef-integral-residue-tor, def-weil-rationalization-karoubi, lem-weil-linear-scalar-localization-triangulated, lem-weil-pbc-adjunction-of-natural-bijection, def-weil-integral-rational-qbar-compact-support.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Raw rational localization of the integral adjunction; blueprint coefficient construction."}

Old step 18: For integral-to-rational comparison take $q$ to be the localization of integralLeft followed by the inverse of rationalLeft. Take $b$ to be the identity comparison on the localized integral-right object, transported along those choices. The counit equation is the image of the integral one, so it has the required transpose normalization. For a rational embedding $E\to L$, define $q,b$ by localizing their integral versions on the same object representatives. On a morphism $h/\varpi_E^r$ use its localized image; the integral maps are linear and natural, so this is independent of representatives and natural. This gives exactly rationalization_normalized and rational_normalized: the left maps are the raw images of the indicated integral maps. The scalar-extension theorem and localized derived structures give the required endpoint shifts, and the comparisons preserve them.

Cited nodes: def-weil-rationalization-karoubi, lem-weil-scalar-extension-exact-triangulated, lem-weil-pbc-commshift-nattrans-comp-whisker.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Rationalization and rational coefficient comparisons, on the prescribed integral representatives."}

Old step 19: Define the closed-stage operations on a pair $(E,K)$ by $(E,F_EK)$ and $(E,G_EK)$. For a map represented over $L$ use its image under $F_L$ or $G_L$, conjugated by the scalar comparisons. The left transition identities follow from canonical tensor associativity and proper/open mate pasting of Step 16. For the right transitions, take the inverse transposes of the two composites: substitution of the counit equations reduces equality to the left transition identity. Injectivity gives equality. Therefore passage to a larger common field preserves these represented maps, composition and identities. Likewise the Hom bijections commute with transition maps, so inverse natural bijections pass to the directed colimit defining the closed coefficient category. Use them for the adjunction. Distinguished triangles and shifts are represented over one finite field, which gives exactness. On the inclusion of a finite common field take $q$ to be the identity on $(E,F_EK)$; take $b$ to be its counit transpose. This is the identity on $(E,G_E L)$ by the finite-field adjunction. These choices give common_normalized and the required shifts.

Cited nodes: def-weil-algebraically-closed-coefficients, lem-weil-scalar-extension-composition, lem-weil-pbc-mate-pasting, lem-weil-pbc-adjunction-of-natural-bijection.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md", "place": "Common finite-field construction and third Hom bijection of sk-thm-sf-tensor-hom."}

