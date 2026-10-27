# Q52 stage-1 report: lem-trf-nodal-pushout-coordinate-normal-form

## Files written

- dag/nodes/sec-trace-formula/lem-trf-nodal-pushout-coordinate-normal-form.json: statement item, now split into seven direct elementary steps; not a Mathlib leaf.
- citations.json: one verbatim group-completion quotation for each of steps 5, 6 and 7.
- report.md: this report.
- searches.jsonl: actual searches recorded by the prescribed msearch.py command.

No new nodes and no Mathlib leaves were created. The original statement, statement dependency, source, creation metadata and blueprint provenance are unchanged. Earlier recorded searches are retained, and the five searches run in this session are appended with their actual results.

## Attachments

None. Searching lean/WeilConjectures/ for the exact blueprint id and for nodal, group completion, GrothendieckAddGroup and monoid pushout found no declaration stating this item. The few nodal-curve occurrences concern derived functors or geometric examples, not this monoid presentation.

## WANTED

None. The ILO document is present and was read in place using pdftotext. No additional source is needed for this elementary calculation.

## Findings

ILO, Expose VI, Proposition 1.9, printed p. 71, gives the cocartesian square with diagonal map from N to N^2 and 1 sent to (1,a) in Z times P. It calls Q fs in its fs-geometric setting and subsequently asserts injectivity of g and that its group cokernel is Z. It does not write the coordinate normal form. The existing item is an agent-formulated algebraic calculation for arbitrary integral P; its source correctly warns that these calculations are omitted. The proof is accordingly marked agent-origin, rather than claiming ILO proves the greater generality explicitly. We use none of the source's geometric assertions or references to SGA.

The latest blueprint locality statement/proof and unit were read. They now follow Varshavsky's contracting-correspondence theorem and do not mention this historical ILO calculation. The item already records its historical provenance through lem-trf-nodal-divisorial-chart; the delivery completes that assigned algebraic item without editing or replacing any current unit or chapter statement. No blueprint_update on the item required a statement change.

The original item was statement-only. No mathematical error or statement dispute was found. The main pitfall is to regard equality in P group completion as equality in P without its injectivity hypothesis; that hypothesis is explicitly used in step 3. We also keep n in Z throughout, so negative values of t minus m_- impose no extra image condition. Group torsion is allowed throughout.

## Searches and duplicates

Before writing, searched the whole DAG for group completion, groupification, GrothendieckAddGroup, AddCon, monoid congruence, nodal normal form and min(x,y); also ran blueprint_refs.py ancestor and searches for monoid, nodal, group completion, reduced coordinates and cocart. The existing def-trf-fs-log-blowup defines the group completion by generators and relations and is reused. There is no new node that could duplicate an existing one. Blueprint same_as remains the searched empty list.

For the item, ran LeanFinder twice with different descriptions of the diagonal pushout, Loogle with Algebra.GrothendieckAddGroup and AddCon, LeanSearch with the normal-form assertion, and grep in GroupTheory/MonoidLocalization. Read the returned types: general monoid structures and the Grothendieck-group map do not assert the normal form; normal words for Monoid.PushoutI assume group factors and pertain to noncommutative pushouts. Pell, determinant-matrix and modular-form results are unrelated. Read Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean as well, confirming it provides the general completion construction, not this coordinate model. Hence no exact or one-line-specialization match. All new search records agree with searches.jsonl; unavailable searches were not invented.

## Not duplicates

No new-node/existing-node pairs: no new nodes.

## Review by Q52

I read ILO VI Proposition 1.9, printed p. 71, including the square and the assertions following it, the current latest locality proof and unit, and the statement of def-trf-fs-log-blowup. I checked the item with its full generality: P injects into P group completion, a is any element, the Z factor is already a group, and the defining relation is a monoid congruence, not an equality imposed only in the group completion. The definition node's sentence about the abelian group on symbols with the product/addition relation supplies exactly the presentation used in steps 5--7. Its fs and geometric hypotheses are not used as conclusions or imposed on P.

Step 1 uses no other theorem: F is additive by its formula, and equality of F-images is a congruence containing the generating pair, so the quotient map is well-defined. Step 2 writes each permitted reduction by adding a tuple to that pair and gives the base and step for induction on the minimum. This uses only nonnegative x,y and addition of a in P; no subtraction in P occurs. Step 3 uses the sign of x-y to recover both nonnegative coordinates of a reduced tuple. Equality of the second and third group coordinates then recovers n and p, using exactly the item’s injectivity hypothesis for the last equality. This simultaneously proves uniqueness and injectivity, without assuming that Q was already cancellative.

Step 4 explicitly substitutes the candidate inverse and checks all four coordinates and their domains. For m=0 it gives x=y=0. For m<0 the subtraction is in P group completion, and membership in P is the precise existence condition. The preimage is unique by the assumed embedding. Negative n and torsion in P group completion cause no issue.

Step 5 cites def-trf-fs-log-blowup only for its group presentation, quoted verbatim in citations.json. It derives extension and uniqueness directly by checking the defining relations on symbols, and writes both maps for the product identification R group completion = Z plus P group completion. Thus it does not use a separate theorem about group completion commuting with products without a citation. Step 6 uses that same presentation to extend h and g and computes h^gp composed with the candidate inverse coordinate by coordinate. Step 7 computes the other composition on u, e and g(0,p), and on v uses exactly u+v=e+g(0,a). It explicitly shows these generate Q and then its group completion. There is no missing generation or inverse-map compatibility assertion.

I checked B1--B10: no new statements or sketches are hidden in new nodes, the item is self-contained, the only named notion is defined by its cited dependency, TeX and the original provenance fields are retained, and there is no attachment or Mathlib-leaf claim. C1--C8 were checked against each step: every argument is a short calculation from the quotient or group presentation, and the sole cited statement says exactly what is used. No off-unit tools or cyclic dependencies were added. D1--D5: this is an explicit calculation, not a restatement in children or an appeal to omitted details. Each of the seven steps is under 650 characters, and none hides a non-elementary lemma. E1--E7: the only cancellation is in the ambient abelian group, equality of p is justified by injectivity, and the defining relation is applied in the permitted direction before any group inverses are used.

For small cases, P={0}, a=0 gives H=Z^2, all of H as the image, and u+v=e; the formulas give v=(-1,1). For P=N, a=0 the image is Z^2 times N. For P=N, a=1 and m=-2 the condition is b>=2; the representative is (0,2,t-2,b-2). For P a group, including Z/2 and a its nonzero element, membership in P is automatic and the image is all H; adding torsion to b leaves the uniqueness argument valid. For a general integral nonsaturated P the proof never divides an element of P or assumes any lattice embedding. No new hypotheses were needed, so I made no statement correction. The actual repairs were supplying the missing proof, recording the presentation citation precisely, and making the arbitrary-integer coordinate and the generator check explicit.

## Unfinished work

None in this one-level split. Remote dry run and delivery are performed by the prescribed deliver.py commands.
