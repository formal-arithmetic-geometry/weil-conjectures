# Worker report: lem-per-etale-supported-ideal-principalization

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-etale-supported-ideal-principalization.json: statement; split using existing nodes; no Mathlib match for the item.
- citations.json: one verbatim statement quotation for each of the fifteen proof-step citations.
- report.md: this report. searches.jsonl is the unmodified log created by msearch.py.

New nodes: 0. New Mathlib leaves: 0. Only the sandbox is written. No Lean, compiler, Lake, local preflight script or repository git command was used.

## Attachments

None. I searched lean/WeilConjectures for the blueprint id, principalization, flattening and strict-transform terminology, then read the relevant Blowup/Compactification search results. Existing principalization of the centre on its own blowup is a different assertion; it does not principalize an ideal on an arbitrary etale source by modifying the base. No completed project declaration states this item.

## Literature wanted

None. The proof uses available Stacks sources, not an unprovided ILO assertion.

## Findings and changes

The statement is unchanged. There was no earlier sandbox node, proof or report to preserve, and no released repair note. The live item is unsplit. Its source carefully flags that flattening alone does not supply the comparison between strict transform and extended ideal. The proof now supplies that comparison: the pullback-to-ideal map is injective off the exceptional locus, and any exceptional-supported section has zero image because the ambient structure sheaf injects into its restriction away from the pulled-back Cartier boundary. Its kernel therefore equals the defining strict-transform kernel.

The source's other omitted consequence, rank one, is also proved rather than assumed. Relative flatness does not itself imply invertibility. Finite presentation comes from 0815, local freeness comes from 080Q and the field local rings of etale fibres, and the actual rank is determined over a nonzero localization away from the regular boundary equation. This avoids any unjustified claim that finite-type flat modules are automatically locally free on an arbitrary non-Noetherian scheme.

The proof is marked agent-written because it assembles these documented general results and supplies the comparison and rank calculation, rather than claiming a source states this exact corollary verbatim. No SGA source is used. I read the current latest blueprint chapter, unit and ancestor proof; this descendant supplies the same completion-rigidity auxiliary input specified in its inherited provenance. Neither the unit nor chapter is modified.

## Searches and reuse

Five msearch.py commands were run and their results read: LeanFinder for the supported-ideal assertion, Loogle for Etale/Ideal/IsInvertible, grep for admissible blowup/principalization/flattening/invertible ideal terminology, LeanSearch for principalization by a base blowup, and LeanFinder with a second phrasing about Raynaud--Gruson module flattening. All services responded. Hits concerned etale base change/localizations, flatness tests and fractional or invertible ideals, without the requested existence theorem. The original item's Q107 searches remain, followed by the exact Q108 queries and logged summaries. No query was invented or recorded as run when unavailable.

Whole-DAG searches were made by source tags 0815 and 080D--080F, by titles/statements concerning strict transforms, Cartier pullbacks, local freeness, etale fibres, base change, and invertible ideals. Blueprint searches included strict transform, principalization, supported ideal, invertible ideal, etale morphisms and etale base change. The existing module flattening theorem, strict-transform definition, Cartier-support lemma, ideal pullback epimorphism, fibre description, base-change theorems and local freeness criterion suffice. No proposed new node survived these searches.

## Not duplicates

No new nodes are created. In particular, the item uses lem-trf-flattening-module-by-admissible-blowup rather than creating another Tag 0815 node, and uses lem-trf-flat-fibre-free-neighbourhood rather than creating an etale specialization of Tag 080Q. It uses lem-pur-ideal-tensor-pullback-comparison for the extended-ideal image, and the existing def-trf-module-strict-transform for the quotient. The item's existence assertion is not a duplicate of thm-nagata-blowup-principalizes-center: that theorem principalizes the centre on the same scheme, whereas the present ideal lives on V and the blowup modifies S.

## Review by Q108

I read flat.tex Tag 0815 (theorem-flatten-module), including all five hypotheses and its finite-presentation conclusion. I read divisors.tex Tag 080D (definition-strict-transform), Tag 080F (lemma-strict-transform-flat, with its power-torsion proof), Tag 0809 (lemma-blow-up-pullback-effective-Cartier and its chart calculation), and the complement and exceptional-divisor assertions in lemma-blowing-up-gives-effective-Cartier-divisor. I read morphisms.tex Tag 02GO (lemma-base-change-etale) and Tag 02GL (lemma-etale-over-field), and more-morphisms.tex Tag 080Q (lemma-flat-and-free-at-point-fibre), including its proof. I also read the latest blueprint proof for lemma-nagata-cartier-total-transform-blowup, which gives the same regular-element chart calculation as 0809. There are no new nodes needing a separate source review.

For step 1 I opened the statements of lem-trf-flattening-module-by-admissible-blowup and def-weil-etale-morphism. The former provides exactly the admissible blowup, relative flatness and finite presentation. Its hypotheses hold: S is qcqs, V is quasi-compact, e is locally finitely presented, K is finite-type quasi-coherent, and its restriction over U is the structure module. The latter definition explicitly includes flatness, so the structure module is relatively flat over U. Global finite presentation of K is not assumed.

For step 2 I read lem-weil-pbc-etale-scheme-base-change and lem-weil-pbc-qcqs-morphism-permanence, especially clause (3), which explicitly preserves finite presentation under arbitrary base change. I used the original finite-presentation hypothesis on e, not merely its etaleness. The definition of etale supplies flatness of g. The statement of lemma-nagata-cartier-total-transform-blowup explicitly says an effective Cartier ideal remains effective Cartier under an arbitrary blowup; flatness of b is not assumed. I then applied the actual statement of lem-trf-relative-flat-cartier-support with base S_1, divisor D_1 and module O_Y. It gives sectionwise injectivity of restriction on every open, exactly what the next step requires.

For step 3 I read lem-pur-ideal-tensor-pullback-comparison. Its epimorphism onto the extended ideal is available for an arbitrary scheme morphism; only its isomorphism clause requires flatness, which is not used for p. This corrects a potential identification gap, because def-nagata-extended-ideal defines an ideal using a kernel and does not itself state the tensor-pullback image theorem. thm-nagata-global-blowup-complement states the precise complement isomorphism. def-trf-module-strict-transform states the quotient by sections vanishing off the exceptional closed subset. The two kernel inclusions are proved in the item, rather than being attributed to any cited node. The centre is supported inside D because its ideal is the unit ideal over U, so W is disjoint from the exceptional locus. The ambient restriction injectivity from step 2 kills the image of every exceptional-supported section. No flatness of the nonflat projection p is used. This is a few-line kernel argument from the cited statements and definitions, marked elementary.

For step 4 I opened lem-weil-pbc-etale-fibre-discrete-separable-points: it gives the fibre as a disjoint union of field spectra, hence its local ring at any fibre point is a field. The flatness of a vector space is justified by splitting exact sequences. I checked both separate flatness assumptions of lem-trf-flat-fibre-free-neighbourhood, and checked that finite presentation applies to both g and the module. The cited criterion concludes freeness on a neighbourhood, not merely stalk flatness.

For step 5 I used precisely the regular-power injectivity clause of lem-trf-relative-flat-cartier-support. A nonempty affine trivialization has nonzero ring B, and d regular implies B_d is nonzero; this is shown in the step. The unit-ideal hypothesis then identifies the localized free module with B_d. Passing to a residue field gives rank one by vector-space dimension. def-nagata-invertible-ideal defines precisely locally free rank one with its specified inclusion. The nonzerodivisor conclusion is proved from that inclusion: multiplication by a generator is the injective composite of the free-rank-one identification with the ideal inclusion. No separate regular-generator claim is hidden in the definition. This rank and generator argument is elementary once the cited freeness and boundary injectivity have been established.

I checked delivery-errors B--E point by point: all statement notions retain their definition dependencies, there are no statement changes, new-node proof sketches or duplicate nodes, and each uses entry is backed by a verbatim statement quote in citations.json. The non-elementary steps cite actual results rather than only definitions. The comparison and rank steps contain their full elementary arguments. No step exceeds 2000 characters. The off-unit general geometric results are explicitly declared in split_report.tool_uses; they supply tools for the inherited finite-stage-principalization input, not a replacement for the perverse unit's route.

Small cases checked: empty S or V gives a vacuous local assertion; D empty forces K to be the unit ideal everywhere, consistent with rank one; K=O has the identity strict transform; V need not surject onto S, since all local calculations take place at existing points of Y. For S=Spec k[x,y], D=V(x), V=S and K=(x,y), blowing up (x,y) supplies the familiar principal ideal on each chart, and the boundary equation x remains regular. For nonreduced S=Spec(k[e]/(e^2)[t]) and D=V(t), the argument uses regularity of t and works without reducedness. In contrast an arbitrary pullback of K can have exceptional torsion: the proof removes it and identifies the resulting quotient with the image ideal, and never assumes that p*K embeds in O_Y. No Noetherian, coherence or excellence hypothesis has entered.

## Unfinished work

None in the stage-1 split. The existing dependency nodes retain their own statuses and future proof work. Server validation and direct delivery are performed with the required delivery command.
