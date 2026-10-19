# Stage-1 report: lem-weil-pbc-clopen-etale-neighbourhood-cofinality

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-clopen-etale-neighbourhood-cofinality.json — statement node, split into eight steps. Mathlib has useful ingredients, but the searches did not identify the whole assertion.
- citations.json — 24 step/node entries with the verbatim statements used; full statements retain all hypotheses of multi-clause citations.
- report.md — this report. No new nodes and no new Mathlib leaves. The sandbox also retains searches.jsonl and the local preparation script.

## Attachments

None for the item. Searching both the blueprint tag and the notions in the read-only project Lean source found no declaration of this assertion. The existing dependency AlgebraicGeometry.Scheme.Hom.exists_SpecMap_comp_eq_of_isSepClosed belongs to lem-exc-etale-lift-separably-closed-factorization, already attached and audited closed in the repository; I reused that node rather than proposing another attachment.

## WANTED

None. All literature needed for the argument is present.

## Issues found and changes

The imported item was a statement-only node. Its mathematical statement is correct and is unchanged. I replaced no source, unit, ancestry, or other maintainer-owned metadata. The main-20261015 blueprint ancestor thm-weil-pbc-direct-image-finiteness-proper contains its finiteness statement but no displayed proof; the inherited from.place describes the intermediate refinement for the Tag 0EZV route, not a quotation from the ancestor. The proof is consequently marked agent-written and follows that inherited finite-presentation/clopen route explicitly. Tags 0EZV and 09AY supply the surrounding motivation, not the exact assertion of this node.

I retained the item's existing Mathlib search records and added exactly the five searches run through msearch.py for NQ (LeanFinder twice, LeanSearch, Loogle and grep). Their actual hit names are recorded. LeanFinder returned etale-locus and formally-unramified results; LeanSearch returned local-affine, section-localization and clopen-idempotent ingredients. None supplies both the clopen section and equalization conclusions with the hypotheses of the item. Loogle and the specified AlgebraicGeometry grep returned no hits. The search log is retained.

## Not duplicates

No new nodes were created. Before deciding this, I searched the whole DAG by titles and statements for clopen refinements, pointed neighbourhoods, localization, affine shrinking, finite presentation, idempotents and field lifts, and searched the entire imported blueprint with blueprint_refs.py for both "clopen" and "pointed etale" (also the full item phrase). Existing generic statements were reused. In particular, the closed field-lift node is stronger than the field-lift subclaim needed here; the affine-shrink node already includes preservation of etaleness and of the marked point. No existing blueprint node found states this whole item in another form, so same_as remains [].

## Review by NQ

I read coord/delivery-errors.md B–E in full and checked the actual node statements against each step, rather than relying on node names. I read the chapter, unit, the current ancestor blueprint text and the parent's use of this item. The argument is below the existing proper-base-change route and changes no chapter or unit. For the source I read Stacks etale-cohomology.tex Tag 0EZV (lemma-check-stalks-better) and Tag 09AY (lemma-affine-only-closed-points), algebra.tex Tag 00CR (lemma-localization-colimit), Tag 00QO (lemma-characterize-finite-presentation), Tag 00EE (lemma-disjoint-decomposition), schemes.tex Tags 01HV and 01I3 (lemma-spec-sheaves, lemma-standard-open-affine), and morphisms.tex Tag 02GJ (lemma-etale-characterize). I read the proved project field-lift declaration at GeometricLifts.lean:54–88, including its residue-field factorization proof. No SGA source is used. There are no new nodes whose source requires a separate review.

Step 1 uses exactly the existing clopen-idempotent theorem (existence of e), the affine basic-open theorem (the open subscheme and its ring C_e), and open-immersion-etale (so the proposed subsystem actually consists of etale objects). These statements give the asserted clauses; no affineness of an arbitrary open was assumed. Empty clopens are covered by e=0.

Step 2 uses the universal property of localization: the complement of the kernel z maps to nonzero elements of the field Omega, hence to units. The hypothesis K -> C_z is an isomorphism is used with its actual structural map, so the resulting Spec K -> E is compatible with the original geometric point. The affine-spectrum correspondence supplies the contravariance. This step is elementary from the quoted statements; it does not identify C/z with C_z without justification.

Step 3 uses the closed node lem-exc-etale-lift-separably-closed-factorization with L=K, the actual embedding beta:K->Omega, p etale and the exact compatibility from step 2. Its statement explicitly allows arbitrary Omega, and gives both equations, not merely equality of underlying points. The affine-shrink node supplies an affine etale refinement through the marked point. Restricting y to it is an elementary open-subscheme restriction: the domain has one point and the structure-sheaf maps restrict. The affine etale-ring-map theorem says B is finitely presented as a C-algebra, which is precisely the finiteness needed in step 4, not merely local finite presentation.

Step 4 uses the localization-colimit node with multiplicative subset C minus z and the finite-presentation factorization node with R=C, domain B and target C_z. The index set is a set, so the latter's smallness hypothesis is met; the colimit is in commutative rings and all maps preserve the C-structure, exactly as that node asks. The conclusion is a C-algebra map B->C_s with s outside z. The affine correspondence and basic-open theorem give its scheme map. I checked the marked-point equation on the actual composite B->C_z->Omega; equality of underlying points alone would not suffice.

Step 5 uses only the assumed clopen basis and elementary restriction to an open subscheme. It restricts the previously constructed pointed morphism, so no extra lifting theorem is hidden here.

Step 6 uses the affine-shrink node at the common marked image v. The two inverse images of its affine open are open in W_i and hence in E; their intersection is not assumed affine. Instead the assumed basis gives a clopen W_0, whose affineness was proved in step 1. The affine-spectrum and affine-etale statements yield C-algebra maps B->C_e and finitely many algebra generators of B. V need not be separated or quasi-compact; only its chosen affine open is used.

Step 7 uses the quoted fraction equality in the localization-at-prime definition, which explicitly states that equality is witnessed by a multiplier outside z. Since C_z -> Omega is injective, each generator difference represented by a_j/e^r has a_j zero in C_z. I wrote the annihilators t_j and their product t out explicitly. The affine basic-open theorem supplies both section-localization rings and restriction homomorphisms, so on W_3 subset D(e) intersection D(t), both e and t are units by restricting their inverses. Thus all generator differences vanish, and equality on the C-algebra generators is equality on B. This is a finite polynomial/fraction calculation from the cited statements, marked elementary; it is not a new lemma or a restatement of the item's equalization clause.

Step 8 uses the exact definition of the pointed-neighbourhood category and the open-immersion-etale theorem. Initiality is checked by writing a common-refinement zigzag in each comma category, rather than invoking an unstated cofinality theorem. Nonemptiness is step 5 and connectedness is step 7. No assertion about existence of arbitrary colimits is used.

For the small cases, Spec 0 has no point z, so the pointed assertions are vacuous while the clopen assertion holds. For C=K, the argument gives the familiar rational lift of an arbitrary geometric point of an etale K-scheme. For a finite product of copies of K, shrinking may choose the marked component. For infinite profinite-style examples the proof uses only finite presentation of the selected etale chart and finitely many differences; it never assumes a point component is open. When B has no algebra generators, the annihilator product is 1 and the maps agree because both are C-algebra maps. Positive characteristic and separably closed but imperfect K cause no problem: the closed field-lift node assumes separably closed, not algebraically closed. The source V is allowed to be nonseparated, and the use of one common affine open avoids a separatedness assumption.

I checked B1–B10 (no new-node form or search claims to fabricate), C1–C8 (each non-elementary input is the statement of a cited node, not its proof; no cycles introduced by reusing a parent), D1–D5 (the proof itself constructs and equalizes the maps, no clause outsourced to a new node), and E1–E7 (all finite-presentation, field and smallness hypotheses checked above). Every step is below 2000 characters; there is no long step concealing a lemma. No statement dispute was needed.

## Unfinished work

None in the one-level split. Existing dependency nodes keep their current states and will be handled separately by the project.
