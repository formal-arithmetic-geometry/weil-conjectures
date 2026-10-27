# Stage-1 report: lem-per-boundary-regular-flag-parameters

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-boundary-regular-flag-parameters.json: item, statement, split; no exact Mathlib match.
- citations.json: verbatim statement quotations for every use in the five proof steps.
- searches.jsonl: actual msearch records for this item.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The split is an argument using already existing nodes, rather than a restatement delegated to new clauses.

## Attachments

None. The search by exact blueprint tag and by regular-system/flag/boundary parameter terminology in lean/WeilConjectures found no declaration of this item. RegularLocalQuotientKernelParameters.lean gives parameters for one ideal without the prescribed-boundary or simultaneous-flag conclusion; it does not attach this item. Its complete proof is useful background but is not substituted for the present statement.

## WANTED

None.

## Corrections and source comparison

No statement correction or hypothesis change. The source is ILO, Travaux de Gabber, VIII Lemma 4.2.9, printed p.121 (PDF page 127), opening sentence of its proof. It asks for the simultaneous local parameters without proving their existence. I also read VIII Lemma 4.2.6 on printed p.120 (PDF page 126), which explicitly identifies I/mI with the kernel on cotangent spaces, and Stacks algebra.tex Tag 00NR, label lemma-regular-quotient-regular (lines 25750--25780), which explains the independent-cotangent-generator method. Stacks Tag 00KU, label definition-regular-local, and its preceding paragraph identify regular dimension with cotangent dimension. The argument filling the simultaneous-boundary gap is signed as agent-written, rather than misattributed as a complete proof printed in ILO.

The existing source field also points to Stacks 00NR; that lemma alone does not preserve arbitrary fixed boundary elements or prove the simultaneous claim. I have not cited its existing DAG node for something stronger than its statement. In particular, injectivity of L/mL into the ambient cotangent space is proved directly from the separately adapted parameter systems in Step 2, not inferred from the definition of regularity.

The newest blueprint is literature/blueprint/latest -> main-20261024. I read its lem-per-artin-gabber-affine-curve proof, the chapter record and the unit record. The created item's ancestor chain reaches Step 3 through the existing purity/modification route. The latest ancestor does not literally discuss regular flags; the precise supporting place is the opening parameter choice in ILO VIII 4.2.9. No chapter or unit route is altered, and the item is not a unit key statement, so no unit record is written.

## Searches and reuse

I searched the whole DAG by regular quotient, simultaneous/flag parameters, adapted basis and linear independence/basis extension, and ran blueprint_refs.py ancestor plus searches for regular parameters, basis flag, regular quotient, parameters, and simultaneous. The simultaneous search returned unrelated trace/Tate/factorization statements; none restates this item. Existing nodes already supply every non-elementary tool:

- lem-weil-pbc-regular-local-cotangent-dimension (Mathlib leaf).
- lem-weil-pbc-vector-space-basis-through-vector (Mathlib leaf, general independent-subset extension).
- lem-weil-pbc-nakayama-local-generators (Mathlib leaf, both directions and the submodule form).
- def-weil-pbc-regular-system-of-parameters (definition).

For the item, actual msearch calls tried two semantic phrasings, LeanSearch, Loogle IsRegularLocalRing, and grep in RingTheory. I read the returned signatures: they concern regular sequences, the regular local ring class, smooth algebra presentations and bases of algebra-extension cotangent modules; none states the simultaneous ideal/boundary conclusion. Every new search record was copied from searches.jsonl with its exact query. The pre-existing item's search records are retained as requested. There are no newly created nodes needing independent search records or same-tag comparisons.

## Not duplicates

No new nodes. No duplicate pairs arise.

## Review by Q14

I checked B through E of delivery-errors.md against the actual five steps and their cited node statements, not just against the intended argument.

Step 1 uses the statement of lem-weil-pbc-regular-local-cotangent-dimension to obtain dim_k(m/m²)=dim R=d: R is Noetherian local and regular by the item's hypotheses, so all hypotheses match. The parameter definition supplies length d and generation of m for each separately adapted system. Reduction of these generators spans the cotangent space; a spanning family of d vectors in dimension d is a basis. Scaling by units preserves generated ideals and lets the representatives of the boundary be exactly b_i. The boundary members therefore have distinct independent cotangent classes.

Step 2 uses only the systems already chosen. If x=sum a_j z_j belongs to L intersect m², independence forces each coefficient into m. This proves the kernel is mL and hence the needed injectivity, including L=0. In the same coordinate basis, both the test b_i in L and the intersection span(E) intersect U_L are computed explicitly. This step is elementary and does not silently use flatness, an exact cotangent sequence on the left, or a regular-immersion theorem. P contained in Q gives the nested subspaces and boundary subsets without any further theorem.

Step 3 cites the general basis-through-vector statement, which explicitly extends any independent subset, not just one vector. It is applied in U_P, U_Q and V. Before the second and third applications, I wrote the relation argument proving the proposed unions independent, using precisely the intersection equalities established in Step 2. No stronger simultaneous-basis theorem is assumed. Finite-dimensionality came from Step 1, so these bases are finite.

Step 4 cites the generator form of Nakayama, whose statement explicitly applies to finite modules and to their residue quotients. P, Q and m are finite, already witnessed by the chosen finite parameter generators. L/mL is identified with U_L by Step 2, so its basis lifts generate the actual ideal, not merely its image modulo m². Each boundary class is lifted by its original b_i, and Step 2 checks that this lift is in the required ideal. The remaining lifts exist by the definitions of U_L and V. Thus none of the proof confuses equality of tangent subspaces with equality of ideals without Nakayama.

Step 5 applies exactly the parameter definition: d chosen elements generating m. Ordering the lifts with A first and C next gives both initial segments. This is a reordering of finite disjoint sets, with m=|A| and l=|C|. It needs no new regular-sequence or dimension theorem. All cited statements are quoted verbatim in citations.json. The cited theorem nodes are Mathlib leaves, so no off-unit non-leaf theorem tool is used.

I tested d=0 (R is a field, Q=P=0 and all lists empty), r=0, P=0, P=Q, Q=m, and the extreme r=d. For a non-coordinate nested example, in k[[x,y,z]] with boundary z, P=(x+y²) and Q=(x,y), the constructed parameters x+y²,y,z work; they show why generators themselves need not be fixed. I also checked the tempting false generalization: in k[[x,y]], boundary x and P=(x+y²), the separate compatibility hypothesis for P fails because x and x+y² have equal tangent class; regular quotients alone would not suffice. This guards the exact hypothesis used in Step 2. There are no long steps above 2000 characters and no hidden comparison lemma left inside one. No hollow definitions, new unsplit proof sketches, forbidden SGA sources, Lean changes or compiler invocations are present.

## Unfinished work

None in this one-level split. The required dry run and direct push are the remaining delivery operations.
