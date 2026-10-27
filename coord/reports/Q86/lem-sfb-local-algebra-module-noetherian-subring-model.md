# Stage-1 report: lem-sfb-local-algebra-module-noetherian-subring-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-algebra-module-noetherian-subring-model.json — statement, now split into seven steps; the whole statement has no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep. Its existing searches are retained and actual searches from this run are appended.
- citations.json — ten step/node entries, each quoting the cited statement verbatim.
- report.md — this report. No new DAG nodes, no new Mathlib leaves, no Lean files. prepare.py is sandbox-only preparation scratch; searches.jsonl is the search command's audit log.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, Noetherian subrings and algebra/module descent. Algebra.exists_fg_subalgebra_isPushout in WeilConjectures/Mathlib/RingTheory/FinitePresentation.lean gives an algebra-only model, without the local ring or module clauses, and therefore is not an attachment. Other module-model hits concern finite projective modules or derived tensor comparisons, not this item.

## Wanted sources

None. The necessary Stacks sources and Mathlib sources are available read-only.

## Corrections and route

The statement is unchanged and true. Stacks flat.tex, Tag 0AT8 (lemma-find-pure-spreadout), proof at lines 7287–7290, chooses the simultaneous local subring, algebra and module without spelling out their construction. The present split supplies that argument; it is marked proof_origin.by = agent because these details are written here, rather than claiming that the source prints them. The source's finite-type algebra and finite module are finitely presented over the Noetherian model rings; our direct finite presentations establish the stronger clauses already requested by the item.

No previous sandbox split/report was present. The inherited blueprint.from.node is null and tools/blueprint_refs.py ancestor returns None. I retained that provenance and its non-unspecified place/via chain, rather than inventing an imported ancestor. The split realizes exactly the local-model input of 0AT8 in the inherited 0AT9/BLR density route. It changes neither chapter nor unit and is not the unit's key statement, so no unit realization file is written. I read the chapter record and sk-thm-sf-ctf-stability unit record. The reused coefficient-model and localization/right-exactness results are existing Mathlib leaves, hence generic tools rather than an alternative unit route.

## Not duplicates

No new nodes are created. In particular, lem-trf-presentation-noetherian-coefficient-model already gives the finite coefficient core and its arbitrary base-change presentation, and is cited directly. Its affine geometric wrapper lem-trf-affine-presentation-noetherian-coefficient-model is unnecessary. Existing Noetherian finite-type/localization lemmas and tensor right exactness were found and reused rather than restated. Whole-DAG searches covered Noetherian subrings, presentation coefficients and module descent; blueprint_refs searches covered noetherian subring, local subring, module model and finite presentation. I also searched the newest literature/blueprint/latest/blueprint (main-20261024); its algebra-only/etale coefficient models do not state the simultaneous local algebra/module result.

## Review by Q86

I read Stacks flat.tex Tag 0AT8, lemma-find-pure-spreadout, including the preceding localization and subsequent quotient discussion, and algebra.tex Tag 00F3 (definition-finite-type), Tag 00DF (lemma-tensor-product-exact), Tag 00FN (lemma-Noetherian-permanence), and Tag 00QM (definition-essentially-finite-p-t). I opened every statement cited in the split and checked its hypotheses against its use. For the coefficient-model leaf I also read Mathlib/RingTheory/Extension/Presentation/Core.lean, particularly ModelOfHasCoeffs, its finite-presentation instance and tensorModelOfHasCoeffsEquiv. There are no new statements to audit against further sources.

Step 1 uses exactly the algebra and module finite-presentation definitions: a polynomial quotient and an exact finite free presentation. A matrix entry has a polynomial representative because the quotient map is surjective. The extra variables Y_l with equations Y_l-u_l preserve the algebra by the explicit inverse evaluation maps. This elementary adjustment is essential: the coefficient-core leaf speaks about the smallest subring of the relation coefficients, not an arbitrary enlarged subring. It makes every module-matrix coefficient genuinely occur in a relation, avoiding an unsupported strengthening of that cited statement.

Step 2 takes the Noetherian finite-type coefficient core, its quotient algebra E and its tensor isomorphism from lem-trf-presentation-noetherian-coefficient-model. I checked that its final clause really covers EVERY D-algebra T, including T=R_0 and T=R, without injectivity or flatness assumptions. The node expressly states all these facts; I do not use only an internal construction in its proof. The extra coefficients 1 and -1 do not enlarge an integer subring.

Step 3 constructs the local subring directly. Since D is an actual subring of R and all denominators lie outside the unique maximal ideal, the denominators are units in R. The fraction map is injective even if R has zero divisors: a fraction with value zero has zero numerator in D. Its image is therefore a localization, not merely a quotient of one. The contraction n consists of numerator fractions from p; every element outside n has its displayed inverse. This proves locality and the required equality n=R_0 intersect m explicitly, rather than presuming that an arbitrary subring is local.

Step 4 invokes lem-weil-pbc-localization-noetherian only after D is known Noetherian and R_0 is known to satisfy localization. Its statement includes the fraction and kernel criteria, both proved in step 3. The essentially-finite-type definition applies to the finite-type integer algebra D and W; the Noetherian definition gives finite generation of n. No assertion that subrings of arbitrary Noetherian rings are Noetherian is made.

Step 5 uses the arbitrary-base-change clause of the same coefficient-model statement. It supplies the unchanged finite polynomial relations over R_0. I wrote both maps of the associativity identification and checked their balanced relations and composites on pure tensors. Thus alpha uses exactly the coefficient evaluation map, and C_0 to C is the map alpha(1 tensor -) required in the statement.

Step 6 uses the module finite-presentation definition and lem-weil-pbc-tensor-right-exact. The latter states right exactness for any module, on either tensor side; its application over C_0 therefore needs no flatness. Free-module tensor identifications are explicit, and the matrix becomes H entry by entry because its coefficients were included in D. Both cokernels are quotients of the SAME C^b by im H, which specifies the C-linear beta. This proves the module clause through its presentation rather than moving that clause into a new node.

Step 7 uses only the defining tensor balancing relations. I checked the two displayed inverse maps and the C_0 balancing, then composed alpha and beta. This recovers the exact canonical map r tensor x maps to r beta(1 tensor x), not an unspecified R-linear isomorphism; the intermediate algebra action shows compatibility with C via alpha.

For the edge-case check, zero ranks, no algebra variables/relations, and an empty matrix require no coefficients and cause no divisions; empty coefficient lists give the prime integer subring. M=0 and C=0 are allowed by the quotient/cokernel constructions. If R is a field, p may be zero but every chosen denominator is still a unit; the construction remains valid. In positive characteristic the image of Z replaces Z itself, exactly as the coefficient-core statement requires. Zero divisors in R introduce no localization kernel because the chosen denominators are units of R. No flatness, finite generation of M over R, finite residue-field degree or finite generation of the maximal ideal of R is assumed. A ring with 1=0 cannot satisfy the stated local-ring hypothesis of a proper maximal ideal, so no extra exclusion is needed.

Against delivery-errors B–E: B1/B2/B3 apply with no new nodes and unchanged self-contained statement/definition dependencies; B4 TeX is singly escaped in JSON; B5 source tags and labels were checked; B6/B8 use existing Mathlib leaves without changing their matches; B7 actual queries/results are preserved; B9 provenance and same_as were checked; B10 no full attachment was found. For C1–C4 each non-elementary input is one of the opened cited statements and every occurrence has a verbatim quotation in citations.json. C5 reuses the existing nodes above; C6 all new proof dependencies are existing Mathlib leaves/definitions, so there is no return path to this item; C7/C8 introduce no off-route unsplit theorem. For D1–D5 the proof gives the finite-data, localization, matrix and balancing arguments itself, creates no restatement nodes, and supplies the source's omitted details. For E1–E7 I checked all hypotheses, actual maps and edge cases as described above; no statement dispute or source error arose. Every proof step is below 2000 characters; none hides a separate substantial comparison lemma.

The preliminary server review_split passed. The required full dry run and delivery are performed after this report is written.

## Unfinished work

None in the stage-1 split. The maintainer's independent mathematical review remains the normal next stage of delivery.
