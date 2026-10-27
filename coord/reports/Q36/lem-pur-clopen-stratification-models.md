# Q36: lem-pur-clopen-stratification-models

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-clopen-stratification-models.json: statement, split into six steps; no exact Mathlib match.
- citations.json: twelve step/node citations, each quoting the cited statement verbatim.
- searches.jsonl: actual searches run by msearch.py; retained without rewriting.

New nodes: 0. New Mathlib leaves: 0. The statement and its statement dependencies are unchanged.

## Attachments

None. Searching WeilConjectures for the item tag and clopen/stratification/constructibility found no project declaration establishing the whole item. The existing Stratification.pullback declaration in WeilConjectures/ConstructibleSheaf/Pullback.lean supplies only the geometric pullback construction and is reused through its existing node lemma-constructible-pullback-stratification. Its source was read at lines 174 onward. The etale finite-locally-constant upperStar theorem nearby does not establish the required pro-etale chosen-model assertions.

## WANTED

None. All sources used are available locally.

## Findings and corrections

The unsplit item is a genuine combination of topological constructibility, immersed scheme structures, and pro-etale module models. It cannot be replaced by a statement merely about subsets. In particular the return direction needs retrocompactness of the component open even without Noetherianity: being closed supplies it. Constructibility is defined using finite geometric stalks whereas the middle assertion stipulates finite local models. The proof now cites existing results for both directions of that conversion instead of silently treating them as identical definitions.

No STATEMENT-DISPUTED: no correction to the statement was necessary. No route departure: this is the finite-clopen finite-level constructibility argument under the section invariant's varying-dimension proof, not another proof of smooth purity. No SGA source is used.

## Existing-node and blueprint searches

Searched the entire DAG for 005J, 09YD, clopen, constructible strata, finite local models, immersion base change/composition, and pro-etale coefficient comparisons. Read every cited statement. blueprint_refs.py searches included constructible (589 hits), clopen stratification (0), locally constant pullback (0), finite module (7), constructible open (0), and constructible stratification (1). The one last hit concerns coefficient change in the trace formula, not this clopen-strata theorem. The nearest blueprint ancestor is def-pur-section-invariant. Its current main-20261015 statement and the finite-torsion constructibility definition were read. Existing nodes cover every subsidiary fact; there is no need to create nodes for elementary union, retrocompactness, or immersion composition arguments.

The item searches were actually run with msearch.py, in addition to preserving its inherited searches. They used leanfinder with two phrasings, loogle, grep, and leansearch. Loogle supplied only the clopen singleton in a quasi-finite fibre. LeanSearch returned scheme structure-sheaf modules, generic finite type module-sheaf predicates, and constructible finite unions; these do not concern the small pro-etale fixed constant-ring category. The first finder phrasing returned scheme site/covering infrastructure and clopen partitions; the second returned locally constant module functors on compact spaces and generic module-sheaf finiteness notions. None proves all clauses or gives a one-line specialization. No service failure is recorded as absence.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Reused the existing 005J, 09YD, immersed pullback, and finite-model lemmas rather than introducing duplicates.

## Review by Q36

I read topology.tex at lemma-open-immersion-constructible-inverse-image (005J) and lemma-quasi-compact-open-immersion-constructible-image (09YD), and their proofs. The first allows any open; the second specifically needs a retrocompact open. Step 1 cites the former for the constructible trace and the existing immersed stratification pullback node for the actual scheme fibre products, image preimages, disjointness and cover. The open immersion definition justifies identifying the component with its image. The pullback node states this conclusion, so its proof is not being mined for an additional assertion.

Step 2 gives the return immersion explicitly: a closed immersion into V open in X_i remains the same closed immersion into V, and V is open in X with the restricted structure sheaf. This uses the actual definitions of open immersion and immersion. It does not replace a stratum by its reduced subscheme. The finite union is disjoint because the component images are disjoint. The proof of retrocompactness is written out using a finite subcover in W, and only then is the 09YD node applied. Thus the non-Noetherian case is covered. This is a short elementary assembly from the cited statements and definitions, not a hidden new lemma.

For step 3 I read sites-modules.tex lemma-push-pull-composition-modules (03D8). The cited ordinary pro-etale module comparison definition states the needed natural isomorphism for arbitrary scheme maps with coefficient identifications. I also read the entire statement of lem-trf-constant-coefficient-composition: its equation identifies the canonical ring map of a composite with the composite of the canonical ring maps, exactly what this step requires. The square sa=j_i b therefore gives an A_T-linear comparison, and the other comparison is A_S-linear. No derived, completed, etale-only, or changed-ring operation is substituted.

For step 4 I read sites-modules.tex lemma-pullback-locally-constant (093R) and the stronger explicit-cover statement of lem-exc-proetale-pullback-locally-constant. The node applies to any scheme morphism and finite ring and states both the base-changed covering and the identical M_j models; these are the exact assertions used. No properness, finite type or Noetherian hypothesis is needed. Step 5 is just composition of the already displayed module isomorphism with each stipulated trivialization. The stratum scheme is identical, so the original covers and models are retained without a new descent assertion.

For step 6 I read proetale.tex lemma-compare-locally-constant (099Y), the blueprint's current finite-torsion constructibility definition, and the statements of lem-sf-proetale-lisse-finite-models and lem-weil-pbc-proetale-finite-model-stalks. The former gives the covers with finite models from locally constant finite geometric stalks for an arbitrary scheme and finite ring. The latter gives finite geometric stalks from finite models, with no Noetherian or finite-field assumption. The proof uses each exactly in that direction. Their full statements, not just titles, are in citations.json. The finite-model conversion is delegated to these existing nodes; no omitted comparison argument is asserted elementary here.

Small cases checked: a single identity component preserves the given schemes, covers and modules; a disjoint union of two points reproduces the two component stratifications; nonreduced strata retain their entire structure sheaves; an infinite disjoint union of points shows why no quasi-compactness of X is assumed or used (the partition itself remains finite); an empty component produces empty pullback strata; I empty forces X empty. The sheaf condition on the empty site makes the zero-model empty stratum a witness for the positive-stratum convention. A clopen component need not itself be quasi-compact, but its intersection with a quasi-compact open is closed there and hence quasi-compact, which is precisely the hypothesis needed in step 2.

All six steps are shorter than 2000 characters. Every non-elementary fact is an existing cited node; the union, immersion factorization, isomorphism composition, finite index union and empty-case arguments are written out. Generic off-unit tools are declared in split_report.tool_uses. The statement, its original provenance and blueprint ancestry are preserved.

## Unfinished work

None in this one-level split. Existing subsidiary nodes may still require their own splits or formal proofs; no claim is made here that those proofs are finished.
