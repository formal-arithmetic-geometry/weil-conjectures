## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-subgroup-conjugation-incidence-criterion.json`: split into nine steps using existing nodes; Mathlib verdict no match. The statement is unchanged.
- `citations.json`: 29 exact statement quotations, one per step/dependency pair.
- New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag and incidence, subgroup conjugation and fixed-coset vocabulary. No project declaration gives both clauses. Existing unrelated incidence-spreading and abstract conjugation declarations do not attach this item. No Lean was written or compiled.

## WANTED

None. Read Milne, Algebraic Groups, Lemma 17.32(a),(b), printed pp.361–362 (PDF pp.373–374), including the surrounding connected-group-variety convention. Its proof uses the closed incidence locus, the proper projection, fibre dimension (A.72), and constructibility (A.15). The DAG already has the required general geometry tools.

## Issues and corrections

The imported item was statement-only. Its rational-point formulation is already appropriate; I did not replace rational points by arbitrary scheme points. Milne suppresses the equality of incidence dimension with group dimension and the rational lifts needed to identify the image. Steps 2–5 supply them. The source's second clause begins with finitely many rational fixed cosets; step 7 explains why this implies a zero-dimensional scheme fibre, without assuming reducedness.

I initially considered applying the existing constructibility node directly to the incidence projection. Reading its statement showed that it assumes affine source and target. Step 9 instead applies it to the affine conjugation morphism, whose image agrees with the incidence image by step 2. Likewise the dimension-drop theorem requires an integral affine variety; step 8 explicitly uses the integral affine reduction of the group, with its unchanged topology. The local dimension in step 4 is topological local dimension, not the dimension of a local ring at a generic point.

Read the chapter and unit records, SETUP's three levels, GOAL, the worker brief and delivery-errors B–E. The latest blueprint direct-image proof (3) supplies the enclosing route; the long inherited supporting chain and `blueprint.from` are preserved. Searches of the imported blueprint and latest blueprint found no equivalent item (`same_as: []`). No new lemma replaces a unit step. Off-unit dimension, Jacobson, affine-product and constructibility inputs are explicitly declared in `split_report.tool_uses` as general tools. No SGA route is used.

## Mathlib and duplicate searches

Preserved all six inherited Q53 search records. Ran and read six additional searches via the required Q03 msearch command; their exact tool/query and raw audit records are in the item's `mathlib_searches` and `searches.jsonl`. These comprise LeanFinder with two phrasings, Loogle, LeanSearch, and two source grep searches. All services returned results normally. Read `Group.conjugatesOfSet` and its membership theorem at Subgroup/Basic.lean:561–566 and `Sylow.fixedPointsMulLeftCosetsEquivQuotient` at Sylow.lean:587. They concern abstract conjugation or a finite subgroup's common fixed points. The returned proper-action/topological-coset and finite-morphism fibre declarations do not state the algebraic incidence criterion. No exact match or one-line specialization exists among the hits.

Searched the whole DAG by conjugation/incidence, homogeneous quotients, Stacks dimension/constructibility vocabulary and product/flat-base-change vocabulary. Reused the quotient, identity-component, dimension, Jacobson and constructibility nodes rather than creating special cases. Blueprint-ref searches for the item concept and Lemma 17.32 found no same-statement imported node.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs.

## Review by Q03

I checked the unchanged statement against Milne Lemma 17.32: algebraically closed base, smooth connected finite-type affine G and smooth connected closed H are exactly the group-variety setting. X is separated finite type, and its rational quotient description is provided by the cited homogeneous quotient node. Properness occurs only in clause (a). Clause (b) asks for the fixed points of one element, not common fixed points of all H. There are no new nodes whose statements need a separate source audit.

Step 1 uses the actual separatedness definition (closed diagonal), the fibre-product universal property, and the closed-immersion base-change clause of proper-fp permanence. That node also says a closed immersion is proper, hence finite type. The finite-type composition/base-change node supplies the product and fibre finiteness. Thus the incidence locus is a closed finite-type scheme, with no unproved descent of an image being invoked.

Step 2 uses the homogeneous quotient's torsor and rational lift statements together with the algebraic homogeneous quotient's flat, surjective, finitely presented map and test-scheme coset equality. The displayed inverse g^{-1}ag lies in H by exactly that equality. The fppf covering calculus explicitly preserves coverings under base change and agrees with scheme fppf coverings; it supplies all three properties of r. This is an isomorphism on test schemes, not a claim inferred from equality of topological point sets.

Step 3 uses the identity-component theorem's geometric irreducibility and integral reduced component, with connectedness to replace components by G and H. The product theorem explicitly assumes geometric irreducibility, which is available. Surjective continuous images preserve irreducibility by the written two-closed-subsets argument. The dimension/transcendence-degree theorem explicitly gives finite dimension for finite-type domains; the affine reductions satisfy these hypotheses.

Step 4 checks flatness of r, local finite type of both arrows, and the actual fibre over z=(H,1). Its test-scheme equations give H with maps g↦(g,1) and first projection. The flat composite dimension node says precisely dim_u(U_s)=dim_u(U_x)+dim_x(X_s). The locally algebraic dimension node applies because H, I and G×H are irreducible and locally finite type, and gives topological local-to-global equality. Product dimension is used only for the nonempty finite-type schemes G,H. Cancellation is legitimate since dim H is finite, as established in step 3.

Step 5 applies the Jacobson-space theorem and closed-point residue-field theorem to the finite-type scheme I_a over k. Their statements supply dense closed points and residue field k, respectively; hence nonemptiness yields a rational fixed coset. The quotient statement lifts that coset to G(k), and the test-scheme criterion puts g^{-1}ag in H(k). Both directions of the rational image equality are written. No rational lift from an arbitrary nonclosed point is assumed.

Step 6 is elementary from universal closedness as defined in its cited definition: base change to G makes the projection closed. The first clause then follows from the already established rational image equality. This is the only use of properness.

Step 7 again uses exactly the Jacobson and residue-field statements. Finitely many rational points imply finitely many closed points; their finite union is closed as well as dense, so all points are closed and there is no positive-length specialization chain. This proves local fibre dimension zero even with nilpotents. Nonemptiness follows from the identity coset.

Step 8 uses the irreducible fibre-dimension node, whose statement gives both the dimension equality with a natural-number error term and the lower bound at every source point. It therefore applies at the chosen finite fibre, without any generic-fibre assumption or properness. Step 3's integral affine reduction checks the affine dimension-drop node's domain/reduced hypotheses. Equal dimension rules out a proper closed image closure.

Step 9 uses the affine spectra fibre-product theorem for G×H, finite-type permanence, and both clauses of affine constructible-open. These nodes really supply affineness, constructibility, and a nonempty open in a dense constructible set. It uses the conjugation morphism, with affine source, rather than applying an affine theorem to I. The open immersion definition supplies the open-subscheme structure. Rational containment is exactly step 5.

Against delivery-errors B–E: no new statement-only sublemma or duplicate was introduced; no clause was renamed as a dependency; the nine steps carry the incidence argument. Every non-elementary input is a cited existing statement, and each citation is copied verbatim into citations.json. No non-elementary step exceeds 2000 characters. Checked H=G (X is a point and both conclusions hold), H={1} with positive-dimensional G (the finite-fixed-coset hypothesis fails), the trivial group (dimension zero and the entire group is open), and a maximal torus in GL_2 with a regular semisimple element (finite fixed cosets without proper quotient). Nothing assumes characteristic zero or reduced fixed-point fibres. There was no prior return entry and no statement dispute.

## Unfinished work

None in the mathematical split. The server dry run and direct delivery are the remaining validation steps.
