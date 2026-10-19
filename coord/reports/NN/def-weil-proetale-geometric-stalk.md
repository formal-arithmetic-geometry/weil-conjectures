# Stage-1 worker report: def-weil-proetale-geometric-stalk

## Files written

- dag/nodes/sec-nagata-compactification/def-weil-proetale-geometric-stalk.json: definition, split; no exact Mathlib match. The pointed category, opposite restriction diagram, size convention, set quotient and module interpretation are explicit. Four elementary verification steps retain and establish the original filteredness assertion and the colimit models.
- citations.json: one verbatim statement quote for every step citation.
- report.md: this handover. No new nodes and no new Mathlib leaves.

## Attachments

None. Searches by the item id and pro-etale stalk terminology in WeilConjectures found no declaration stating the whole item. The upstream master is reference material only; no master declaration is treated as finished. Project weakly-etale site definitions supply only part of the construction, not this stalk.

## Wanted sources

None. I read the ancestor's last sentence, Stacks proetale.tex Tag 0F6B (lemma-cofinal-etale) with the preceding definition of neighbourhood, etale-cohomology.tex Tags 03PQ (lemma-cofinal-etale) and 040R (definition-stalk), more-morphisms.tex Tags 094T (lemma-composition-weakly-etale), 094U (lemma-base-change-weakly-etale) and 0951 (lemma-weakly-etale-permanence), categories.tex Tags 002F (definition-colimit) and 002V (definition-directed), and sites-modules.tex Definition 03CV (definition-sheaf-modules).

## Corrections and route

The original statement is mathematically sound, but its justification suppressed the construction of the equalizer and omitted the universe bound required by its colimit. I supplied the existing size convention without imposing a geometric finiteness hypothesis. The larger-universe category of lifts over the chosen skeleton is small; finite scheme constructions stay in the bound and can be transported to representatives.

The phrase "of modules" did not specify the category of the diagram. I made both interpretations explicit: for fixed coefficients use the module colimit; for a varying ring sheaf use underlying-set stalks and define the stalk-ring action by common refinements. This avoids incorrectly regarding semilinear restrictions as maps over a fixed section ring. It does not identify these ordinary set/module stalks with condensed coefficients.

The ancestor is a definitions collector, although filed under the compactification sketch. This split realizes only its last sentence and changes no chapter, unit, or compactification route. The generic between-objects theorem lem-trf-weakly-etale-between-objects is declared as a tool use. The composition/base-change theorem is already a Mathlib leaf. I did not cite the qcqs finite-limits theorem for arbitrary neighbourhoods: its hypotheses would not apply.

Because the imported definition already contains filteredness, its elementary verification is retained as steps on the item. I did not manufacture a new theorem restating that clause. The item has real quotient data rather than choosing an unspecified object. No new unsplit lemma or proof sketch is delivered. The category axioms for pointed objects follow immediately by composing the specified lift equations; the restriction diagram follows from contravariant functoriality.

## Mathlib searches

All fresh records are exactly the queries run through msearch.py, copied from searches.jsonl. LeanSearch returned Internal Server Error and is recorded unavailable. Two LeanFinder phrasings, Loogle and source grep were read. TopCat.Presheaf.stalk and its stalk functor concern topological opens. Mathlib AlgebraicGeometry/Sites/Etale.lean:97 defines geometricFiber for the big etale topology. Mathlib CategoryTheory/Sites/Point/Basic.lean:96 defines presheafFiber as a category-of-elements colimit for an already supplied point. The pro-etale site file:52 defines the big pro-etale precoverage. None is an exact match or a one-line specialization constructing our pointed small pro-etale stalk, so no leaf is claimed.

## Unfinished work

No unfinished part of this one-level split. Existing dependency nodes are reused and left unchanged. A fresh second reader must read and deliver; the worker runs only --no-push.

## Review by NN

I compared the last sentence of def-weil-scheme-morphism-properties with the full neighbourhood definition preceding Stacks 0F6B. In particular, the lifts use the same field Omega and are actual maps over Y, not merely chosen points of the topological fibres. The Stacks proof sends one to 03PQ; I read that proof and reconstructed its pullback equalizer with weakly-etale stability substituted as 0F6B instructs.

In step 1, def-weil-weakly-etale-morphism defines exactly flatness of a map and its diagonal; the identity satisfies both. The site and size definitions permit Y and transport to its skeleton representative. In step 2, def-pc-fibre-product supplies existence and the pair of lifts, and lem-weil-pbc-weakly-etale-composition-base-change states exactly the stability properties needed for the projection and composite. In step 3, the same node makes Q and E weakly etale. The opened statement of lem-trf-weakly-etale-between-objects applies to U and Q over Y, so it gives weak etaleness of (h1,h2); it does not require separation. The pullback equation proves that its projection equalizes the original arrows. The category-colimit node explicitly gives the three filtered-category conditions, which are now met after reversing arrows.

In step 4, the sites node defines sheaves as contravariant functors, and the colimit node supplies the universal property, not an existence theorem. I therefore wrote actual quotient constructions and checked their universal properties rather than inferring colimit existence from its definition. The module-sheaf statement says restrictions are semilinear and preserve the group laws; that is exactly what the common-refinement operation check uses. No theorem asserting exactness, conservativity, or preservation of colimits by stalks is smuggled in.

I tested an empty base (there is then no geometric point, so no instance of the definition), a geometric point over Spec of an algebraically closed field (the identity neighbourhood exists), the empty set sheaf (its quotient is empty), the zero module sheaf (its module quotient is zero), and h1=h2 (the equalizer construction still carries the lift). Non-quasi-compact or nonseparated neighbourhoods remain allowed; the argument uses neither condition. I checked B–E: no new node could duplicate a clause or existing node, each used statement was opened, every non-elementary input is cited, quoted text is copied verbatim, and no dependency reaches back through this item. The proof is a finite sequence of elementary constructions from those statements, not an appeal to a tag without a node. No Lean file, compiler, Lake command, live project or launcher was changed.

## Dry run

The worker dry run printed OK (not pushed), with preflight passed. The source citation uses Categories Tag 002V, whose label is the directed-category definition.

## Second reading by NN

- Node statement: checked against the ancestor's last sentence and Stacks proetale.tex Tag 0F6B (pro-etale neighbourhood and cofilteredness), etale-cohomology.tex Tag 040R (stalk colimit model), and Categories Definition 002V (filtered categories); verdict: faithful and self-contained.
- Step 1: checked identity neighbourhood, weakly etale definition, site size convention, and skeleton transport; verdict: elementary and valid.
- Step 2: checked fibre-product projections and lift against the fibre-product universal property and weakly-etale composition/base-change node; verdict: elementary and valid, with no hidden separation or finiteness hypothesis.
- Step 3: checked the equalizing pullback $E=U\times_{V\times_YV}V$, its pointed lift, and the opposite-category orientation against Tag 0F6B and the cited stability nodes; verdict: valid and establishes the parallel-arrow condition.
- Step 4: checked the set quotient and module direct-sum quotient against the colimit definition, site functoriality, size convention, and sheaf-module restrictions; verdict: elementary universal-property verification and valid for both fixed and varying coefficients.
- Mathlib searches: checked every recorded query in searches.jsonl; verdict: semantic hits concern topological stalks or generic site fibres and are not exact matches, with LeanSearch correctly recorded unavailable.

Changes: corrected the report's source-label note to reflect that Categories Tag 002V is the directed-category definition, and recorded this second reading. No node or citation changes were needed.
