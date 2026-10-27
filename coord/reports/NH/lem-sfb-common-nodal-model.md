# Worker report: lem-sfb-common-nodal-model

## Files written

All paths are relative to this sandbox. The item is
dag/nodes/sec-six-functors-basics/lem-sfb-common-nodal-model.json (statement,
split; not a Mathlib match). Its statement and statement dependencies are
unchanged.

Six new statement-only, unsplit nodes in the same directory:

- lem-sfb-persistent-node-normalization: normalize the persistent nodes of one family, with its finite etale conductor diagram; no Mathlib match.
- lem-sfb-nodal-trait-regularization: resolve a single smooth-generic nodal family by singular-point blowups; no Mathlib match.
- lem-sfb-common-regular-surface-resolution: the general regular-surface point-blowup common-resolution theorem; no Mathlib match.
- lem-sfb-point-blowdown-factorization: the universal property of undoing one regular point blowup; no Mathlib match.
- lem-sfb-trait-etale-branch-pinching: construct one projective nodal family from a finite etale double branch diagram; no Mathlib match.
- lem-sfb-point-blowup-fibre-defects: point-blowup multiplicities, inseparable exceptional fields, persistence, and the good smooth-centre case; no Mathlib match.

citations.json contains a verbatim statement quotation for every citation of
every item step. searches.jsonl is the search command's log. The search
transcripts and scripts are research aids; they are not DAG delivery files.

## Attachments

None. The whole project library was searched for the blueprint tag and the
common-nodal, common-semistable, nodal-model, and semistable notions.
CommonModification.lean constructs general modifications, without a nodal
source, and is not an attachment. Mathlib declarations are not attachments.

## WANTED

WANTED: Knudsen, The projectivity of the moduli space of stable curves II,
sections 1--2, the conductor-and-marking common-model reference requested by
the original item. The delivery does not claim to have read that absent
document or to follow its proof. Its proof_origin is agent, using the local
Stacks sources specified below.

## Corrections and limitations

The imported node had no proof. Its source already warned that 0C5S and
0CDE do not state the marked, persistently nodal conclusion. The split makes
that gap explicit rather than applying either theorem outside its hypotheses.
There is no statement dispute and no added hypothesis.

The common regular resolution need not initially be nodal: blowing up a
regular node xy=pi introduces a multiplicity-two component. Over an
imperfect residue field even a multiplicity-one exceptional line over an
inseparable closed point is not geometrically reduced. Both defects are
excluded by minimality, not silently ignored.

A second correction during self-review was that a finite etale algebra over
a nonhenselian DVR can be a semilocal domain, rather than a product of DVRs.
Step 6 therefore extends at its DVR local rings and explicitly spreads and
glues the maps. Step 7 uses the existing closed-immersion cancellation leaf
to embed the lifted branches; it does not assume etale descent of closed
immersions without citation.

The regular intermediate normalizations may be disconnected. Surface
arguments are applied componentwise; connectedness is proved only after
pinching. No excellence, completeness, stable polarization, separably closed
fraction field, or extension of the trait is used. The original null
blueprint ancestor is retained: blueprint_refs.py ancestor reports None
for this pre-existing chain. The exact inherited place and via chain are
retained and extended for each new node. There is no unit-key realization
to edit for this auxiliary item.

## Review by NH

I read the chapter and unit records, the three-level route rule in SETUP.md,
GOAL.md, stages/1-dag.md, and both copies of delivery-errors B--E.
This is a below-unit prerequisite for the stable-pointed rigidity input;
the common-model proof does not replace a unit or chapter route.

For the item I read resolve.tex 0C5S (lemma-birational-regular-surfaces)
and 0C5J (lemma-factor-through-contraction), models.tex 0CDD
(lemma-etale-local-at-worst-nodal), 0CDC (example-blowup), and 0CDE
(lemma-blowup-at-worst-nodal), and more-morphisms.tex 0E25
(proposition-pushout-along-closed-immersion-and-integral) and 0E26
(lemma-pushout-separated). The source is available; the synthesis extending
these facts to persistent nodes is explicitly an agent proof.

For each new node:

- Persistent normalization uses the xy=0 and xy=pi^m local alternatives in 0CDD and the etale local family model 0CBY. Splitting xy=0 is finite normalization; xy=pi^m is already normal. The horizontal singular locus and its branches are finite etale over the trait, including at nonsplit nodes. Reconstruction uses the fibre-product structure sheaf in 0E25. No general finiteness of normalization over a nonexcellent base is assumed.
- Regularization follows 0CDE and the decreasing-exponent charts of 0CDC. Only total-space singular closed points are blown up, so original smooth markings and conductor branches remain untouched. The exceptional geometric fibres are connected. This node also records the elementary dimension and regular-component consequences needed by the item.
- Common regular-surface resolution is exactly the given-birational-map version proved in 0C5S; its hypotheses are integral regular proper surfaces of dimension two over a Noetherian base. No reduced-fibre or marking conclusion is hidden in it.
- Point blowdown factorization is the specialization of 0C5J to a point blowup. The morphism to the other surface is genuinely constant on the exceptional curve before applying it.
- Trait branch pinching is a relative construction beyond the existing field-only pinching node. I read 0E25's affine-neighbourhood condition and fibre-product sheaf formula, and 0E26's separatedness assertion. Projectivity supplies the required affine neighbourhoods of finite branch sets. A relatively ample bundle can be trivialized along the finite semilocal branch schemes and descended through the conductor square; its finite pullback is ample. The split ring of a node is the fibre product of two smooth branch rings over R. These are identified as the assertions to split later, not attributed verbatim to 0E25.
- Fibre defects use 0AGQ (lemma-blowup) in resolve.tex and its regular-parameter Rees charts, with the n=1 case of 0CDC and the etale models of 0CDD. The exceptional coefficient is the maximal-ideal order of pi, not automatically one. Inseparability passes from l into every residue field on P1_l. The projectivity/flatness consequences concern a point blowup, not existence of a common model.

I opened every existing proof dependency and checked its statement. Here
is the clause-by-clause use in the final proof:

1. Persistent normalization supplies C_i, the smooth generic fibres, the conductor pushouts and the integral-closure description of B_i and N_i. Identifying integral elements in the generic algebras identifies the finite diagrams. The original smooth sections avoid the conductor.
2. Regularization supplies T_i and its integral regular surface components. Common regular-surface resolution supplies both blowup sequences for the prescribed generic identification. Properness forces all closed centres into the special fibre.
3. The fibre-defect blowup theorem ensures that even the arbitrary intermediate point blowups in the minimum-length problem preserve properness over the projective T_1, regularity and flatness. The proper-to-separated lemma applies to these proper S-models. The normal-modification codimension-one node explicitly covers points whose local rings are DVRs; the generic points of the regular T_2 special fibre have that property. Isomorphism there preserves both the uniformizer order and the component function field, ruling out domination by either kind of bad component.
4. Fibre defects supplies persistence and creation of a later bad component whenever a centre lies on a bad component. Taking the last bad creation leaves its curve untouched by every later blowup. The commutation of disjoint centres is explained by gluing the unchanged centre neighbourhood and its complement. Blowdown factorization then gives the second map on the shorter sequence, contrary to the explicitly defined minimum.
5. The defect theorem excludes node centres and inseparable smooth centres. Its good-centre and projectivity/flatness clauses give the induction. The connected-fibre statement for regularization and each good blowup applies, and composition is justified by the closed-surjection argument in step 10.
6. Proper separated valuation extension applies to every closed-point DVR of B and to R for the markings. The normalization node records that pi remains a uniformizer there. Finite presentation supplies finitely many generators and relations for the denominator argument. The dense-open equality node applies because B is flat over the trait and the targets are separated.
7. The etale local model node supplies xy=h. The newly arrived existing dvr-nodal-chart-blowup-calculus node states precisely that xy=pi^n is regular at its node only for n=1 and that this property passes through pointed etale charts; it supports the written generator calculation. Generic smoothness excludes h=0. Thus the unramified branch and section lifts cannot meet a node. Closed-immersion cancellation applies to B -> W -> C_1 with closed composite and separated second map.
8. The pinching node supplies projectivity, flatness, nodality, the universal map and generic-fibre compatibility. The normalization node supplies the generic conductor square. Proper-to-separated and valuative uniqueness give the proper maps and the identities on all markings. Projectivity implies properness by the existing projectivity lemma.
9. The codimension-one node gives the maximal isomorphism open, whose complement on a Noetherian regular surface is a finite closed set. Normalization plus pinching, on the isomorphic conductor diagrams, gives the desired isomorphism even at persistent horizontal nodes.
10. The regularization and good-blowup nodes give connected geometric fibres on the normalization. The pinching node identifies the two chosen branch points and gives the connected fibre over a persistent node. The final elementary closed-surjection argument proves connectedness over X_1; it assumes connectedness only of the given X_1 geometric fibres.

The complete supporting statement, not its proof or an invented paraphrase,
is quoted for each use in citations.json. Off-unit generic tools are declared
in split_report.tool_uses. No cited node depends on the item: new nodes have
only definition dependencies. They are all statement-only and unsplit.

Small cases checked: n=0; smooth generic fibre (B=N empty); a constant
irreducible nodal curve (normalization separates the persistent node and
pinching restores it); a nodal generic curve with several components;
xy=pi and xy=pi^m with m>1; nonsplit nodes; a blowup at a smooth point
with finite inseparable residue extension; and a nonhenselian DVR with a
connected semilocal finite etale algebra. The zero-length common sequence
is permitted. For xy=pi the exceptional multiplicity is two, so the
minimality step is essential. The new regularization has smooth generic
fibre as a hypothesis; it is applied only after persistent-node normalization.

I searched the whole DAG by source tag and by concept, searched the whole
blueprint with blueprint_refs.py, and searched the project Lean sources.
Mathlib searches used msearch.py for each prospective id: LeanFinder,
LeanSearch with a second phrasing, Loogle, and Mathlib grep. I read the hits.
Normalization.lean constructs relative normalization but does not supply
the conductor statement. The scheme pushout hits are gluing along opens
or ring/pullback statements, not closed-branch pinching. No new Mathlib
leaf was found. All services used here returned successfully.

Every item step is shorter than 2000 characters. The substantive local
blowup calculation, conductor construction and pinching construction have
their own new nodes; no long step hides one of them. No Lean file was
written, and no compiler, Lake or build command was run.

## Not duplicates

lem-sfb-persistent-node-normalization vs lem-trf-nodal-generic-component-closure: the existing node isolates one smooth generic component over a valuation ring with separably closed fraction field; the new node normalizes all persistent nodes over an arbitrary DVR and reconstructs the whole family.
lem-sfb-persistent-node-normalization vs lem-trf-valuation-smooth-branches-strict-chart: the existing node gives strict charts under separably closed valuation hypotheses; the new node is a global finite normalization and conductor pushout over an arbitrary DVR.
lem-sfb-persistent-node-normalization vs lem-trf-formal-local-structure-nodal-family: the existing node is a completed local equation at one split node; the new node constructs the global normalization and finite etale conductor.
lem-sfb-persistent-node-normalization vs lem-trf-ordered-nodal-branch-overlap: the existing node compares vertical ideals on overlaps for nonzero smoothing parameter; the new node separates horizontal nodes with zero smoothing parameter and reconstructs the family.
lem-sfb-persistent-node-normalization vs lem-trf-valuation-symmetric-nodal-blowup: the existing node blows up one nodal closure over a separably closed valuation field with smooth generic curve; the new node normalizes persistent generic nodes over an arbitrary DVR.
lem-sfb-persistent-node-normalization vs lem-trf-nodal-log-regularity: the existing node proves log regularity over a log regular pair with smooth complement; the new node is finite normalization and a conductor pushout, with no log structures.
lem-sfb-persistent-node-normalization vs lem-trf-relative-nodal-point-pinching: the existing node constructs pinching for a curve over an algebraically closed field; the new node extracts the conductor from an existing trait family and proves the resulting normalization has smooth generic fibre.
lem-sfb-persistent-node-normalization vs lem-trf-nodal-etale-chart: the existing node gives charts over a log regular pair with a smooth complement; the new node constructs a global conductor and normalization without a smooth-generic hypothesis.
lem-sfb-persistent-node-normalization vs lem-trf-nodal-family-etale-local-model: the existing node gives etale uv=h charts only; it does not construct the finite normalization, global persistent singular locus or conductor reconstruction.
lem-sfb-persistent-node-normalization vs lem-sfb-nodal-branch-double-cover: the existing node constructs an abstract branch double cover of the whole singular subscheme, including vertical nodes; it does not embed horizontal branches in a simultaneous normalization or give a conductor pushout over the trait.
lem-sfb-nodal-trait-regularization vs lem-sfb-common-nodal-model: the new node resolves one smooth-generic family at its total-space singularities; it does not compare two models, resolve a rational identification or handle persistent generic nodes.
lem-sfb-nodal-trait-regularization vs lem-sfb-nodal-log-dualizing-pullback: the existing node assumes a nodal modification and studies its dualizing morphism; the new node constructs a regularization of one family, with no dualizing objects.
lem-sfb-common-regular-surface-resolution vs lem-sfb-common-nodal-model: the new node is the general regular-surface theorem with no nodal or marking conclusion; its intermediate fibres may have multiplicities, which the item's minimality argument must remove.
lem-sfb-point-blowdown-factorization vs lem-sfb-common-nodal-model: the new node is the universal factorization property of a single existing point blowup, not existence or nodality of a common model.
lem-sfb-trait-etale-branch-pinching vs lem-trf-relative-nodal-point-pinching: the existing node concerns a curve over an algebraically closed field and absolute smooth points; the new node concerns relative branches finite etale over an arbitrary DVR, relative flatness and projectivity, and fibrewise compatibility.
lem-sfb-point-blowup-fibre-defects vs lem-sfb-nodal-log-dualizing-pullback: the existing node studies the log dualizing map for an assumed nodal modification; the new node calculates fibre multiplicities and inseparability defects of point blowups, including nonnodal results.
lem-sfb-point-blowup-fibre-defects vs lem-per-local-surface-maximal-blowup-geometry: the existing node gives regularity and the exceptional P1; it has no chosen trait parameter, its order, geometric-fibre defect persistence or good-centre criterion.
lem-sfb-point-blowup-fibre-defects vs lem-per-regular-point-blowup-acyclic: the existing node gives regularity, properness and R1 vanishing; it has no trait divisor, inseparable-fibre or defect-persistence assertion.
lem-sfb-point-blowup-fibre-defects vs lem-per-surface-point-blowup-geometry: the existing node assumes excellence and gives surface geometry/projectivity; it has no trait multiplicity or inseparability analysis. The new node does not assume excellence.
lem-sfb-persistent-node-normalization vs lem-sfb-dvr-nodal-chart-blowup-calculus: the existing node computes the nonzero-parameter local models xy=pi^n and their blowups; it does not separate persistent xy=0 nodes or construct a global finite normalization and conductor pushout.
lem-sfb-point-blowup-fibre-defects vs lem-sfb-dvr-nodal-chart-blowup-calculus: the existing node gives xy=pi^n charts and blowups for n>=2, with nodal exceptional fibres. The new node detects multiplicity two when blowing up a regular node n=1, inseparable smooth centres, and persistence of both defects through arbitrary later point blowups.
lem-sfb-point-blowup-fibre-defects vs lem-sfb-local-surface-maximal-blowup-geometry: the existing node gives regularity and the exceptional P1 in a local surface blowup, with no trait parameter, its divisor coefficient, or geometric-fibre defect persistence.
lem-sfb-point-blowup-fibre-defects vs lem-sfb-regular-point-blowup-geometry: the existing node gives regularity, properness, dimensions and the isomorphism complement; it has no trait divisor multiplicity, inseparability or good nodal-centre assertion.

The first delivery dry run detected these last four pairs after concurrent
landings updated the live DAG. I opened all three existing nodes, retained
the genuinely different statements, and reused the local chart calculus
in item step 7. No earlier search was represented as a search of a node
which had not yet arrived.

## Unfinished work

The six new supporting statements remain unsplit, as required for a
one-level split. There is no Lean claim. Independent maintainer review and
subsequent splits of these supporting facts are still required.
