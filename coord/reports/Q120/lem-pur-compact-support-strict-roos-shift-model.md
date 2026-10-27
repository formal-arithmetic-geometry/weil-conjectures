# Stage-1 report: lem-pur-compact-support-strict-roos-shift-model

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-compact-support-strict-roos-shift-model.json: preserved statement, split into four proof steps using existing DAG interfaces; not a Mathlib leaf.
- citations.json: ten step/node entries, each quotation tested as a verbatim substring of the current cited statement.
- searches.jsonl: six searches actually run with msearch.py; inherited node search records also retained.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project source by blueprint id and Roos/compact-support/shift concepts. Read WeilConjectures/SixFunctors/Etale/Derived/AdicSystem.lean lines 292–360 and CoefficientChangeExchange.lean lines 470–492. AdicSystem.compactSupportTower and compactSupportTower_realization describe compactly supported global sections to a point and perfect normalized towers, not the specified general-target strict semilinear tower, structural maps and Roos shift equality. They therefore cannot attach this item.

## WANTED

None. The source is an explicitly agent-formulated precision obligation; its cited blueprint document and the existing DAG interfaces are present. This proof is marked agent-written, not falsely attributed to a theorem in the blueprint or in Stacks.

## Source and route

Read GOAL.md, SETUP.md's three blueprint levels, the stage-1 brief, stage document, worker role and delivery-errors B–E. Read the sec-smooth-purity chapter, sk-thm-sf-compatibility unit, and literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md in full. The latter's maps-used and coefficient-comparison sentences motivate the normalization obligation but do not assert this shift result. The item inherits its nearest blueprint ancestor thm-pur-rational-and-qbar-purity through the two recorded adic-coherence nodes; its existing precise from.place and via fields are retained. Read the current proof of lem-pur-integral-realization-shift-coherence to see exactly how its last assembly step uses this item.

No statement dispute or unit-route departure was found. The split does not use SGA, and creates no new literature-tag nodes. No unit or chapter record was changed.

## Searches and Not duplicates

No new nodes were needed. Searched the entire DAG for Roos, shifted-cone, compact-support transitions, and scalar restriction. Ran blueprint_refs.py ancestor on the item and search on Roos and compact support. Read the possible transition, scalar-shift, realization and compact-support normalization matches before selecting the existing nodes. In particular reused lem-pur-system-pushforward-restriction-transition and lem-pur-injective-tower-roos-shifts rather than duplicating their general statements as special compact-support clauses.

Read every returned Mathlib search hit. Two LeanFinder phrasings returned derived-category bounded-representative/fraction facts; these do not identify the specified functors or maps. Loogle returned the generic CommShift API. LeanSearch returned mappingCone.shiftIso, shiftTriangleIso, map_δ and additive functor shift results. Inspected Mathlib/Algebra/Homology/HomotopyCategory/Shift.lean (cochain-shift and additive-map shift formulas), CategoryTheory/Shift/CommShift.lean (generic coherent shift structures), and HomotopyCategory/Pretriangulated.lean (cone map and shift interfaces). These provide general ingredients but no exact declaration, nor one-line specialization, for the complete item. The two grep searches are logged; the second passed a single file as its search location, so that script's displayed parsed file fields contain line-number fragments; its actual query and hits are retained faithfully and this is not claimed as a Mathlib attachment.

## Review by Q120

I read the source document for the item and the full statement of every node cited in its four steps. There are no new nodes requiring source review. The source's brief coherence paragraph alone would not justify this conclusion: the split names the more precise existing comparison interfaces and writes the assembly argument.

Step 1 uses the evaluation calculus for one flat-term K-flat reduction representative with actual quotient maps. I checked that lem-pur-system-pushforward-restriction-transition states the restriction-form equality, including the normalization of delta as the inverse ring-change comparison, for all m >= n. Applied it to N = J_j R K and the coefficient tower on W, with the pulled-back tower on the compactification. The statement allows arbitrary systems and explicitly does not require evaluation or restriction to preserve K-injectivity. The scalar-restriction lemma identifies the proper comparison combined with the exact open identification; it also supplies composition in coefficient homomorphisms. I read the integral compact-support definition's actual transition formula, which is exactly the resulting composite after restriction along the completed coefficient sheaf. Thus this step does not infer equality of derived arrows merely from their evaluated values, or silently assume flatness of quotient maps.

Step 2 uses the simultaneous realization theorem, whose statement explicitly replaces S_p J_j by exactly the given integral compact-support functor and intertwines canonical structural maps, including maps in expression contexts and compactification composition. I checked that p is proper, j is quasi-compact open and all input/intermediate normalization, etale-origin, cohomological and Tor bounds are hypotheses of the item itself. No extra separatedness of the base scheme is required by this theorem. This is an identification of actual functors and maps, not just existence of isomorphic objects.

Step 3 uses the injective-tower Roos-shift lemma on the sheaf-module category over the completed coefficient sheaf of the chosen small site. That statement applies to arbitrary original strict tower complexes and constructs the derived product on K-injective tower resolutions; it does not assume exact products of arbitrary sheaves. I checked its differential d(y,x)=(-dy-hx,dx), its limit-tuple inclusion with zero shifted coordinate, and the sign chi(y,x)=((-1)^r y,x). The operation-shift data explicitly extends this normalization to every actual strict system complex and every termwise shifted representative, naming S_p J_j R K itself. This is why no replacement by a family of unrelated derived arrows, and no unspecified derived-category cone, enters the proof.

Step 4 uses the realization recursion's actual c_V identity, including c_K=u_K^{-1}, and the insertion-shift lemma's natural squares for this inverse unit and a_A. Wrote the two unary substitutions for J_j and S_p and explained cancellation of the intermediate shift comparisons; this checks the specified c_{S_p J_j}, rather than selecting a new shift structure by transport. The definition of operation-shift data fixes compact support as the proper/open composite, so the target comparison is the required one. The cited insertion lemma includes all integer shifts and coherent addition, and the Roos lemma includes the same laws. The displayed parity identities also check negative shifts and inverses.

Checked small cases: K=0 gives zero maps and zero cones; j=id and p=id recover the respective single-operation formulas; m=n gives the identity coefficient transition; r=0 gives identity cone coordinates; r=1 and r=-1 both negate exactly the shifted-product coordinate; two odd shifts cancel that sign. No tensor slot is changed in this unary statement, so no unrecorded Koszul sign is introduced. The ambient signed tensor convention is preserved for use in the parent expression argument.

Checked C1/C4 by opening each cited statement and generating quotations from those exact files. Checked the chosen dependencies' transitive closures for a path back to this item; none exists. All four steps are below 2000 characters, and none hides a separate comparison theorem: each comparison invoked is the explicit statement of a cited node. Elementary assembly, restriction-composition and sign computations remain in steps rather than becoming new nodes. No imported fields were deleted, and no source statement was weakened.

## Unfinished work

None in the stage-1 split. The cited open nodes remain independent downstream work items, as prescribed by one-level splitting. No Lean was written or compiled. Server dry run and direct delivery are the remaining operational checks.
