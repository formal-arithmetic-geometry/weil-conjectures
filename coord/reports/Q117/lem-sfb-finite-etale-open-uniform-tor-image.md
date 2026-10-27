# Worker report: lem-sfb-finite-etale-open-uniform-tor-image

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-etale-open-uniform-tor-image.json`: existing statement, split into six steps using seven existing nodes (including the dimension definition). Statement and statement dependencies retained verbatim. No new nodes and no new Mathlib leaves.
- `citations.json`: eight step/node citation records, copied verbatim from the cited statements.
- `searches.jsonl`: actual searches recorded by msearch.py. Earlier searches in the repository item were preserved; six distinct current queries were run, with two semantic phrasings and two source patterns.
- `report.md`: this report and the signed review below.

## Attachments

None. Searched the project library for the exact blueprint tag and for uniform Tor, direct-image, finite-constant projection and residue-test terminology. `DirectImageTorAmplitude.lean` contains a finite-constant projection theorem and a Tor bound with shift twice the source dimension; `DirectImageAmplitude.lean` has the corresponding cohomological bound. These do not state the item's exact relative cd(j) bound together with its constructibility clause. The existing `Sheaf/Paper/OpenTorBoundFiniteConstantTests.lean` and `OpenTorBoundStalkFilteredExtension.lean` implement two reused DAG lemmas, not the whole item. No attachment claimed from a partial match or a Mathlib declaration.

## WANTED

None: the current blueprint, relevant earlier blueprint nodes and Stacks sources were present.

## Findings and changes

The item was statement-only, with no sandbox attempt to continue. Its arbitrary-field formulation is correct. In particular, relative torsion cohomological dimension is finite for a morphism of finite-type schemes over any field by Stacks 0F10(1); 0F10(2)'s absolute field-cd hypothesis is unnecessary here. Its finite-coefficient constant projection formula also does not require constant modules to be perfect.

Rather than introducing copies of the relative-dimension, projection or Tor-test facts, the split reuses `lem-kun-0f10`, `lem-sf-projection-finite-constant`, `lem-sf-open-tor-bound-finite-constant-tests` and `lem-sf-open-tor-bound-stalk-filtered-extension`, together with the module/abelian comparison and arbitrary-finite-coefficient constructibility corollary. All proof dependencies were opened and their transitive statement/proof dependencies searched: none reaches the item. The seven actual dependency nodes are unmerged. The two appearances of `def-kun-cd` explain the eight citation records.

Blueprint searches used `tools/blueprint_refs.py search` with `Tor amplitude`, `open immersion`, `finite constant`, `uniform Tor`, and `finite cohomological dimension`, as well as DAG searches for 0F10 and relevant names. The imported open-Tor node `det-cor-sf-direct-image-ctf-open-tor` assumes a separably closed field, and is not substituted for the arbitrary-field assertion. `det-geo-open-finiteness-ii-amplitude` addresses cohomological bounds and pro-etale comparison, not this item's full projection, constructibility and Tor statement. Thus neither is an exact equivalent requiring same_as. No new node was needed.

The assigned item is not the unit's key node, so the unit record is not edited. Its pre-existing blueprint ancestor chain resolves to None; the existing from.node and via metadata are retained, and the concrete paragraph-(3) place and split_report.blueprint explain the realization. Off-unit generic tool uses are declared in split_report.tool_uses for the maintainer's route review. No chapter/unit route, target, or imported statement was changed.

## Unfinished work

None within this stage-1 split. Existing cited nodes retain their current implementation/proof status; this delivery neither claims they are all axiom-free Lean proofs nor modifies them.

## Not duplicates

There are no new nodes. The duplicate search led to reuse of the existing finite-constant-tests and stalk-filtered-extension statements instead of creating fresh general-ring Tor tests or a special-case open-image theorem.

## Review by Q117

I read the item, the six-functors-basics chapter, the sk-thm-sf-ctf-stability unit, and paragraph (3) of the current main-20261015 direct-images proof. The split realizes its finite-A open-immersion assertion. I also read Stacks etale-cohomology.tex, definition-cd-f and lemma-finite-cd (0F10), the actual module/abelian agreement and higher-image texts in sites-cohomology.tex (03FD and 072W), and lemma-unbounded-right-derived (07K7) in derived.tex. For projection and constructibility I read the complete earlier blueprint .md files, including their embedded proofs, and compared the revised current DAG statements. For the passage to all sheaves I read the complete proofs of the two existing finite-test/stalk-extension nodes and the corresponding landed Sheaf theorem statements. These supply the generic facts below; no proof of a new source lemma is being concealed in an item's step.

Step 1 uses only clause (1) of lem-kun-0f10, whose statement says cd(f) is finite for morphisms of finite-type schemes over a field. Both U and X meet that hypothesis over the same k. The definition node explicitly defines cd(j) as the least nonnegative bound for all torsion abelian sheaves, so the result is the coefficient-independent integer requested. I did not use the separably closed clause (2), and did not infer an absolute cohomological bound for X or k.

Step 2 uses that same definition and the exact statement of lem-sbc-higher-direct-image-forget-comparison. The latter compares module higher direct images with cohomology of the abelian derived direct image for every ring and every morphism, including the zero ring. Multiplication by ell^n kills every underlying abelian sheaf because it kills 1_A. Therefore the torsion hypothesis is actually verified; zero underlying abelian sheaf forces zero module sheaf directly from the definition. I checked that this comparison does not impose properness or separable closedness. The source label was corrected during self-review to lemma-cohomology-modules-abelian-agree (03FD).

Step 3 uses the statement, not the proof, of lem-sf-projection-finite-constant. Its hypotheses are a Noetherian commutative ring, a uniform higher-image bound for every module sheaf, bounded-above K, and a finitely presented module. Finiteness gives the first and last by the explicit ideal/kernel arguments written in the step; these are elementary algebra, so no new nodes were created. The previous step gives the bound with N=d_j and bounded constructibility makes L bounded above. The cited node's formula and counit-mate description are exactly the canonical map of this item, including its unbounded ordinary derived convention. No finite projective dimension is assumed.

Step 4 uses lem-sf-open-tor-bound-finite-constant-tests. I checked its full statement: it allows any positive-characteristic field, a finite ell-primary commutative ring, a qc open immersion of finite-type schemes, L in D^+, an input Tor interval, an arbitrary supplied all-sheaf higher-image bound e, and the supplied finite projection isomorphisms. Our bounded L is in D^+, a<=b is given, and steps 2--3 verify the two additional hypotheses. Its actual conclusion is the finite-constant cohomological vanishing with endpoints a,b+e, so substituting e=d_j is legitimate and proves exactly the assertion used next. The relative bound is retained without replacing it by 2 dim(U).

Step 5 uses lem-sf-open-tor-bound-stalk-filtered-extension. Its statement requires only a finite commutative ring, a scheme, an arbitrary derived object and the finite-constant vanishings; it concludes Tor amplitude against every module sheaf. Step 4 supplies precisely those vanishings. Its proof first takes geometric stalks, then uses exact filtered colimits of modules and the fact that a finitely generated module over a finite ring is finite, and finally uses conservative geometric stalks. It takes no colimit through Rj_*, assumes no absolute cd bound, and assumes no constructibility of arbitrary test sheaves. Thus the distinction between finite constant tests and the item's all-sheaf amplitude is fully accounted for by an existing generic lemma.

Step 6 uses cor-fin-deligne-open-finite-coefficients. I checked its statement explicitly allows any field, any finite ring of invertible annihilator, an open immersion of finite-type schemes, and every bounded constructible complex in ordinary derived categories. Here ell^n is invertible because char(k)=p differs from ell, and annihilates A by hypothesis. Its conclusion is the required bounded constructibility. It does not impose the narrower quotient-DVR coefficients of lem-exc-residue-tor-test, so that lemma was deliberately not used.

I checked delivery-errors B--E against these files. There are no new nodes whose self-containedness, source, search verdict, blueprint reference or Mathlib-leaf line needs acceptance. The item and all new text use ordinary, single-escaped TeX in decoded JSON. Every non-elementary argument is the statement of the corresponding cited node, with a verbatim contextual quote in citations.json; no hidden statement is taken from a cited proof. The six steps have lengths 452, 524, 706, 544, 478 and 530 characters, so none conceals a long-step sublemma. The new step dependencies are their exact union and none is merged or cyclic through the item.

For small cases I checked A=0, zero complexes, empty U, empty X (forcing U empty), and j the identity, where cd(j)=0. The finite-ring ideal and presentation arguments still work at A=0. A nonregular coefficient example A=F_ell[epsilon]/(epsilon^2) with M=A/(epsilon) has an infinite projective resolution; the projection citation expressly permits this case, so there is no unjustified perfect-coefficient shortcut. The input interval may have negative endpoints or length zero, and d_j>=0 ensures a<=b+d_j. I also checked the entire argument keeps k arbitrary even when its absolute torsion cohomological dimension is unbounded: each invoked theorem is relative or field-independent.

All current Mathlib searches actually ran via msearch.py. The services returned scheme-etaleness/open-immersion declarations and standard derived t-structure bounds, rather than the etale derived projection and constructible Tor statement. Both grep patterns and the Loogle query gave zero hits; the two semantic phrasings were read and are logged. No unrun search was added and the repository's prior query records were retained. The preliminary server review_split returned PASS, with zero new nodes and the declared tool uses; its note that the unit has no realization recorded is pre-existing and this non-key item cannot fill that unit-wide record.
