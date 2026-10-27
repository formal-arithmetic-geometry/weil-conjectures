# Stage-1 delivery: lem-sfb-relative-differentials-stalk

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-differentials-stalk.json: statement, split into five proof steps. Mathlib searches find ingredients, not the full stalk comparison with its formula for the universal derivation.
- citations.json: a verbatim statement quote for every cited node in each numbered proof step.
- No new DAG nodes and no new Mathlib leaves. The search log and prepare.py are sandbox research material, not proposed repository changes.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, relative differentials, and both orders of differential/stalk terminology. Modules/Differentials.lean supplies the relative differential sheaf and its affine comparison, not the local-ring stalk comparison in this item. Hom.relativeDifferentialsRestrictFromSpecIso is an affine-chart comparison and does not alone prove the present statement; no ATTACH claim is made. The Mathlib hits similarly concern presheaf values, ring localization, and germ maps.

## WANTED

None: every source used is present in literature/stacks-project/.

## Corrections and route

The item statement is unchanged and is true without finiteness hypotheses. The empty proof is replaced by an affine verification of Stacks Tag 08TE (modules.tex, lemma-stalk-module-differentials). Its source also gives a sheafification/colimit proof; we use the already recorded affine definition of scheme differentials instead of creating general sheaf-differential or filtered-colimit nodes. The actual computation is morphisms.tex Tag 01UT (lemma-differentials-affine), schemes.tex Tag 01HV (lemma-spec-sheaves, parts (6) and (7)), and algebra.tex Tag 00RT (lemma-differentials-localize). Part (1) of 00RT is written out rather than asserted to follow from the existing localization node: that node states only part (2).

The superficially related lem-trf-affine-chart-stalk-differentials assumes locally finite presentation and cannot prove this arbitrary-morphism statement. It is not cited. The existing differential-sheaf definition explicitly includes the affine associated-module description and compatibility of the derivations; this is the statement used, not a theorem inferred from a bare universal-property definition. No SGA source is used.

The inherited blueprint.from.node is null. The prescribed blueprint_refs.py ancestor command also returns None for this new-target chain; it is preserved, as are the inherited via and exact from.place. The latest blueprint proof det-thm-sf-ctf-stability-direct-images (3) now states the compactification/direct-image argument; the inherited place records the longer alteration/moduli prerequisite chain in which this tangent-space input was introduced. The split supplies that prerequisite and changes no chapter or unit route. Searches of the whole imported blueprint for differentials, stalk differentials, 031G, 08TD and 00RT found no alternative blueprint statement of this item. No new blueprint nodes are proposed.

## Not duplicates

No new nodes. Reuse lem-weil-pbc-spec-tilde-stalk-localization, lem-weil-pbc-affine-open-stalk-localization and lem-weil-pbc-kahler-differentials-localization rather than copying their contents to new nodes.

## Review by Q04

I read modules.tex Tag 08TE and its two proposed proofs, including the referenced sheafification description 08TD and directed-colimit formula 031G; I also read morphisms.tex Definition 01UQ and Lemma 01UT, schemes.tex Lemma 01HV (6)--(7), and both the statement and proof of algebra.tex 00RT. The affine proof below is the scheme specialization of those calculations. There are no new-node sources to audit.

Step 1 uses the scheme/spectrum definitions, the definition of a locally ringed-space morphism, and the two affine-open chart/stalk statements. These introduce an arbitrary pair of affine charts and identify their ring germs with localizations. The stalk map is the map of germs defined by the sheaf morphism, not an unrelated localization map. Locality of that map identifies the contracted prime and ensures every denominator from C outside p has invertible image in A. The existence of an affine open inside f^{-1}V is the elementary affine-basis consequence of the definition of a scheme: in an affine chart, restrict to a distinguished open inside the given open neighbourhood. No finite presentation is used.

Step 2 uses exactly the affine associated-module description in def-sc-relative-differential-sheaf, including compatibility with the derivation. The module-stalk definition supplies the representative and germ-equality rules; they prove directly that restricting to the chosen open does not change the stalk. The canonical affine chart node identifies U with Spec of its section ring, and the tilde-stalk node supplies M_q together with the formula m mapping to m/1. Its scalar map is the same germ map given by the affine-open stalk node. Thus this step takes no unsupported sheafification assertion from a definition.

Step 3 uses the precise conclusion of lem-weil-pbc-kahler-differentials-localization: localization in the algebra, over the unchanged base C, with its stated map on differentials. The multiplicative subset is B minus q and the localized algebra is A. This node is a Mathlib leaf, so its use raises no route issue. I read its Mathlib instance KaehlerDifferential.isLocalizedModule_map at Mathlib/RingTheory/Etale/Kaehler.lean:63, whose arguments indeed cover this arbitrary ring map and localization.

Step 4 uses the derivation rules and universal property stated by def-weil-pbc-kahler-differentials. I checked the potentially missing base-localization step explicitly: applying Leibniz to t times its inverse forces D(t inverse)=0 because t is a unit. Hence D kills every c/t from C_p. The maps provided by the two universal properties are inverse because they agree on the universal derivations. This is the two-line calculation of the source's 00RT (1), not a new non-elementary lemma or a claimed consequence of the node used in step 3.

Step 5 uses the module-stalk germ-equality rule, the compatible sheaf derivations of the affine differential-sheaf definition, and the presentation of ring differentials in the Kähler definition. For a section on an arbitrary neighbourhood, the local ring fraction a_z=b_z/t_z becomes ta=b after shrinking. Leibniz then gives the explicit quotient formula on both sides; this is why the proof covers every local section, not just sections of the initial affine chart. The generators db span M, and after localization their images still span, so the germ formula uniquely determines the comparison. This proves that changes of charts and fraction representatives cannot change the map. No unproved comparison is hidden in the word canonical.

For small cases I checked f=id_X (all differential modules are zero), an open immersion (again zero, with identical local rings), Spec k[t] over k (the stalk is free on dt), and Spec k[epsilon]/(epsilon^2) over k (the relation 2 epsilon d epsilon=0 persists, including characteristic 2). In particular no reducedness, field, smoothness, Noetherian or finite-type assumption entered the calculation. Empty X has no point z and creates no exception. The argument for killing base fractions also works for noninjective C to B.

I checked B--E point by point: all new-node obligations are vacuous; the unchanged statement introduces its objects; sources carry tags and labels; the proof cites every non-elementary ingredient by node statement; the citations file copies those statements verbatim; no cited node has a finiteness hypothesis absent here; there is no circular dependency, clause-renaming node, or source error. Each step is below 2000 characters. The elementary steps are the explicit inverse/Leibniz calculation and assembly on generators, while the genuine localization comparisons are marked non-elementary and cite their existing nodes. No off-unit unsplit theorem is used: the external ingredients are definitions or existing Mathlib leaves.

## Unfinished work

None in the mathematical split. Server dry-run and delivery results are recorded below when complete.

## Validation

Server review_split: PASS, 0 new nodes. Server check_dag: no finding introduced by the sandbox or on its nodes. Full deliver.py --no-push exited successfully: OK (not pushed), preflight passed, dry-run commit 29836d04074. Also checked that the item statement is byte-for-byte unchanged and all 15 step/node pairs have verbatim citations. The inherited unit has no realization recorded yet; this item is a supporting lemma, not its key statement.
