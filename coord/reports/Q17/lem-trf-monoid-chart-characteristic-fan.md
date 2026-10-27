## Worker report

Q17, stage 1, 2026-10-23. Item: lem-trf-monoid-chart-characteristic-fan.

Files written:
- dag/nodes/sec-trace-formula/lem-trf-monoid-chart-characteristic-fan.json: unchanged statement, six-step split.
- dag/nodes/sec-trace-formula/lem-trf-zariski-prelog-logification-comparison.json: new statement, unsplit, no Mathlib match.
- citations.json: one entry per cited node per step, quoting the opened statement verbatim.
- report.md and the required search command's searches.jsonl.

Attachments: none. The blueprint tag and searches for monoid charts, characteristic monoids, logarithmic structures, sharp monoids and monoid spectra found no declaration of WeilConjectures that states this item. The logarithmic declarations found under Sheaf are not eligible project-source attachments and were not treated as proofs.

WANTED: none. No Lean was written or compiled, no build tool was run, and the shared repository was only read.

## Source and route

I read ILO, Travaux de Gabber, arXiv:1207.3648, Expose VIII, opening of section 3 (printed p.97), 3.1.1--3.1.10 (pp.98--100), 3.3.2--3.3.4 (pp.106--107), and 3.3.12 (p.108). The source first constructs spectra and their sharpening; Lemma 3.1.8 constructs a monoidal-space map from global monoid sections; 3.3.2 describes association of Zariski and etale log structures; 3.3.12 states that sharpening a monoscheme chart is a fan chart. I also read Expose VI 1.1--1.6 (pp.69--70) to check the etale convention and the fs characteristic.

The item's inherited blueprint.from identifies the historical nearby-duality/alteration branch through lem-trf-log-fan-chart-blowup step 1. I read the current latest blueprint chapter, unit and local-term proof: they now use the contracting-correspondence route. This delivery only supplies the assigned fixed-chart foundational subargument below the inherited branch. It changes no chapter, unit, target or route. The nearest blueprint ancestor command returns lem-trf-local-term-locality; the new node has that ancestor and the complete intervening via list.

The source does not spell out a general theorem on logification of an arbitrary Zariski prelog sheaf. I isolated that omitted sheaf-theoretic construction in the new node, explicitly identifying its formulation as agent-supplied. It is not attributed to a nonexistent Stacks logarithmic tag. The underlying sheafification and germ inputs were checked in Stacks sheaves.tex: Tag 007Z, lemma-stalk-sheafification; Tag 008G, lemma-stalk-pullback-presheaf; Tag 008H, lemma-stalk-pullback. These serve as source checks, not uncited black boxes in the item's proof: step 5 writes the germ and local-lift argument. The new unsplit theorem must eventually supply its own sheaf-theoretic proof.

## New nodes

lem-trf-zariski-prelog-logification-comparison is a general change-of-site lemma for an arbitrary sheaf of commutative monoids with a structural map on the Zariski site. It gives sheafified logification, its universal property, the comparison after extending to the etale site, pushout stalk formulas and restriction compatibility. It assumes neither a fine/saturated monoid nor any fan. Its statement introduces all sheaves, the geometric morphism, the structural maps, the pushout relations and the quotient by units; it contains no proof sketch. It has empty proof and proof_deps and status unsplit.

The argument reserved for that future item is as follows. Sheafify the pushout of the inverse image of units with the sheaf of units. The unit axiom and the mapping property follow locally from the relation [pe,u]=[p,beta(e)u]. Inverse image preserves the relevant finite-limit data and colimits, and repeating logification only extends the units a second time, which gives the same pushout. At a germ, representatives and each finite chain of congruence relations occur on one neighborhood; inverses also occur on a neighborhood, so stalks are the displayed pushouts. The local map from an ordinary scheme stalk to a geometric etale stalk reflects units. For a nonunit its residue is zero in the residue field and remains zero at the geometric point; a unit carries its inverse. Restricting the same representatives to an open gives the claimed compatibility. None of this argument is hidden inside the item's use of a definition node.

## Searches

Before creating the new node I searched the whole DAG for sharpening, fs monoids, Zariski log structures, associated log structures, prelog structures, logification and changes of topology. I opened the existing statements listed below, including their dependencies where relevant. Whole-blueprint searches were run with tools/blueprint_refs.py for monoid, sharpening, log structure, associated log, Zariski log and logification. The broad monoid search gave 153 unrelated or more distant nodes; the sharpening search only found the much larger Fourier theorem; the specific logification and Zariski-log searches found no blueprint statement of this result.

All Mathlib queries were run through the required msearch.py command, and the actual records are preserved in searches.jsonl and copied into the respective mathlib_searches. The item has the new leanfinder, loogle, grep and leansearch queries as well as its retained imported searches. The new node has grep, loogle, leansearch and two differently phrased leanfinder searches. All services answered. I read the hits: ordinary scheme stalk localization, Spec/global-section equivalences, etale loci, general sheafification adjunctions, and module sheafification do not state logification or the comparison after adjoining units. The general sheafification matches are already represented by lem-trf-commutative-monoid-sheafification; they do not make the new logarithmic theorem a one-line Mathlib specialization. No Mathlib leaves are claimed.

## Not duplicates

lem-trf-zariski-prelog-logification-comparison vs lem-trf-associated-log-universal-stalks: the existing theorem starts with one global monoid and builds its associated structure on the etale site; it has neither Zariski logification nor change of site for a prelog sheaf.

lem-trf-zariski-prelog-logification-comparison vs lem-trf-etale-log-presentation-comparison: the existing theorem compares etale presentations and restricts to etale slices; it does not associate a Zariski log structure or compare the two topologies.

lem-trf-zariski-prelog-logification-comparison vs lem-trf-prelog-pushout-log-axiom: the existing theorem supplies the log axiom for an etale prelog presheaf; the new theorem needs change from the Zariski site and the ordinary/geometric stalk comparison.

lem-trf-zariski-prelog-logification-comparison vs lem-trf-filtered-ring-log-pushout: the existing theorem is a filtered-colimit algebra statement with a fixed monoid and a diagram of rings; it does not construct or compare sheaves on two sites.

lem-trf-zariski-prelog-logification-comparison vs lem-trf-chart-face-localization-logification: the existing statement is the algebra of a given geometric chart stalk and optional split coordinates; it does not establish Zariski association.

lem-trf-zariski-prelog-logification-comparison vs lem-trf-fine-log-structure-etale-descent: descent of structures and maps along an etale cover is different from logification of an arbitrary Zariski prelog sheaf.

lem-trf-zariski-prelog-logification-comparison vs lem-trf-strict-log-blowup-cartesian: the existing theorem assumes a Zariski log structure and a strict map, and concerns blowups and their Cartesian squares; the new theorem is the underlying construction before those hypotheses can be used.

lem-trf-zariski-prelog-logification-comparison vs lem-trf-monoid-chart-characteristic-fan: the new theorem neither constructs a map to a monoid spectrum nor identifies a characteristic with a face-localization quotient nor proves fs stalk properties. The item's steps supply all these chart-specific arguments.

## Review by Q17

I reopened the node files and ILO passages above for this review. The item retains its statement, including the global chart, locally Noetherian and fs hypotheses, the Zariski sheaf assertion, every geometric point, every restriction, and every stalk of the entire target fan. The pre-existing blueprint metadata, creation record and searches were retained. There is no statement dispute.

Step 1 uses the new comparison theorem specifically for its logification, topology-change and pushout-stalk assertions. It uses lem-trf-associated-log-universal-stalks for its final clause saying that a chart identifies the given log structure with the associated one. That clause really is in its statement. The constant sheaf of Q is used here, not the constant presheaf on disconnected opens; maps from it to a sheaf are precisely the compatible maps from the constant presheaf. This checks the interface between the two cited formulations.

Step 2 uses lem-trf-fs-face-sharpening for the units of Q_E and for saturated sharp quotients with finite free group completion, and lem-trf-affine-fan-localization-sections for the actual stalk and its localization maps. I checked both complete statements. The face hypothesis is proved from the fact that both factors of an invertible product are invertible. The step deliberately applies the same reasoning to every prime of Q, because the map from U need not cover the fan. It never assumes Q itself sharp or Q^gp torsion-free.

Step 3 takes the displayed raw pushout and quotient stalks from the new comparison node, then supplies the explicit inverse formulas relating them to Q_E/E^gp. The calculation kills E only after quotient by the ring units; it does not silently identify the original log stalk with its characteristic. It also checks the ordinary-to-geometric comparison on representatives. This step is elementary relative to those pushouts and Step 2; it introduces no separate lemma.

Step 4 takes the basic-open section formula and its restriction maps from lem-trf-affine-fan-localization-sections. The definition def-trf-fine-fan-blowup supplies the topology, localizations, sharpening and morphism conventions. I checked those clauses rather than taking a theorem about sharpening from the definition. The step writes the map q-na to the characteristic of q on the unit locus, checks the inclusion and intersection restrictions by localization, and glues these maps. I marked it non-elementary because it uses the cited section theorem; its additional basis construction is explicitly given.

Step 5 uses only the monoidal-space morphism conventions of def-trf-fine-fan-blowup and the isomorphisms already proved in steps 2--4. It explains the inverse-image stalk through representatives and proves the sheaf isomorphism by local lifting and uniqueness on germs. Hence it does not need an uncited general stalk-isomorphism theorem. An isomorphism between sharp stalks is local, exactly as the cited definition requires.

Step 6 uses the new comparison theorem only for its open-restriction clause. It explicitly checks that the faces agree, that q-na has the same image on the restricted unit locus, and that the pushout quotient sends [q,a] to the same q-class. Thus “compatible with restriction” is a checked formula, not a replacement for a missing comparison.

For the new node I read the opening of ILO VIII section 3 and 3.3.2 against every clause: the general prelog-sheaf form and all the construction details are agent-supplied, while those passages motivate precisely the same Zariski-to-etale association. No stronger source theorem is claimed. All objects and notions are introduced or have their defining dependencies. There is no fine, saturated, integral or nonzero assumption smuggled into its arbitrary prelog sheaf. I checked the universal property against the explicit relations, and the use of the same E at both stalks against locality/reflection of units.

Small cases checked: Q=0 gives the trivial characteristic and one-point zero fan; Q a finitely generated abelian group (including finite torsion) gives zero characteristic and shows why torsion in the original chart must be allowed; Q=N with beta(1) invertible gives E=Q and characteristic 0, while beta(1) noninvertible gives E={0} and characteristic N; Q=N^2 with exactly one coordinate invertible gives the corresponding rank-one face quotient. Empty U makes the map unique while the assertion about all fan stalks still follows from Step 2. Disconnected opens require the constant sheaf, as in Step 1. For the new lemma, the identity prelog O_X gives itself, a prelog sheaf all of whose structural images are units gives O_X^times, and no cancellation is used in its pushout statement.

Against delivery-errors B--E: there is one self-contained statement-only new node; the monoid conventions and sites are explicitly defined or cited; TeX was inspected after JSON decoding; every cited statement was opened and has a verbatim entry in citations.json; no source proof is used as a statement; no new node restates the fan comparison; the item contains the construction, inverse formulas and restriction calculation. Every step is below 1200 characters, so none meets the long-step threshold. I corrected the initial plan to avoid creating a new fs face-sharpening node after finding the existing exact theorem, and marked the basis construction non-elementary because it uses the existing affine-section theorem. No unfinished part of this stage-1 split remains; the one new node is intentionally unsplit for a later worker.
