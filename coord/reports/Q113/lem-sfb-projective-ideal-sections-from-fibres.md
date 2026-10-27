# Stage-1 report: lem-sfb-projective-ideal-sections-from-fibres

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-ideal-sections-from-fibres.json: statement, split into seven proof steps; Mathlib verdict no match.
- citations.json: verbatim statements for every cited node in each numbered step.
- report.md: this report. searches.jsonl is the search command's authentic log.

No new DAG nodes and no new Mathlib leaves. The section sequence is assembled from existing interfaces rather than restated in auxiliary nodes. No Lean was written or compiled. All writes were inside the assigned sandbox.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for projective ideal sections, geometric-fibre vanishing, projective twists and base-change/cohomology declarations. The project contains twist sections and abstract coherent-cohomology material, but no finished declaration supplies every clause of this item. Mathlib's ShortComplex.ShortExact.splittingOfProjective is an abstract splitting after short exactness and projectivity are given; it supplies neither the scheme fibre argument nor the canonical restriction/base-change identifications. Module.Flat.projective_of_finitePresentation is also only an algebraic input, not an attachment or a match for the item.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Problems corrected and scope

The seeded item had no proof. Its statement is mathematically sound; there is no STATEMENT-DISPUTED change. I added definition references for properness, quasi-compactness, quasi-separatedness, quasi-coherence and finite local freeness, and specified how the affine-base projective twists glue to relative twists. This does not change any hypothesis or conclusion. The coordinate-preserving comparison lem-trf-free-projective-bundle-base-change-space is needed because the item's projective space was defined by base change, while the standard-chart interface is relative Proj; the definition of the former alone does not supply standard charts.

The inherited blueprint.from.node is null. tools/blueprint_refs.py ancestor confirms that null ancestor, so I retained it and the complete inherited from.place/via provenance. Searches for projective ideal, cohomology base change, projective space twist cohomology, 0B9S and 01XT found no equivalent imported blueprint node. I read the current latest blueprint unit and the current relevant Picard nodes; the live DAG lem-pc-rf-perfect-base-change is the general scheme version of Stacks 0B91, whereas the refreshed blueprint text presents an affine Cech formulation. The proof here uses the actual live node statement, which agrees with 0B91, not extra conclusions inferred from a blueprint proof.

The off-unit coherent-cohomology and projective-chart facts are generic tools in split_report.tool_uses. They implement this Hilbert-section-bound prerequisite, not a replacement of the six-functor unit's route. No chapter or unit record is changed.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own statuses; no unsplit auxiliary statement was created.

## Not duplicates

No new nodes. In particular the previously created lem-sfb-flat-closed-family-ideal-base-change, lem-sfb-flat-projective-twist-base-change-data, lem-pc-flat-rf-open, lem-pc-rf-perfect-base-change and lem-pc-projective-space-twist-cohomology are reused.

## Review by Q113

I read coord/delivery-errors.md B--E in full (including the repeated copy), the stage-1 brief and stage contract, GOAL.md, the three levels in SETUP.md, the worker role and the item's chapter/unit records. I read the current latest blueprint unit, the current Picard open-locus, perfect-direct-image and monomial-cohomology texts, and the actual source statements in perfect.tex Tags 0B9S and 0B91 and coherent.tex Tag 01XT. I also read constructions.tex Tags 01NE/01NH and modules.tex's local-freeness and local matrix arguments. The argument is marked agent assembly because the exact ideal-section sequence is assembled here from those source interfaces.

Step 1 cites the coordinate-preserving projective-space comparison and the relative-space definition for the polynomial charts, the definition of local finite presentation for their finite presentations, and projective-space properness for quasi-compactness/separatedness. I opened each cited node. Properness here implies finite type and hence quasi-compactness; the closed diagonal is affine by the cited closed-immersion definition, and affine permanence explicitly gives quasi-compactness. The flat-projective-twist statement applies with exactly the item's flat finitely presented closed family, without a Noetherian or reduced-base hypothesis, and explicitly gives properness of q, finite presentation and relative flatness of F, and all pullback-twist identifications.

Step 2 cites the existing flat-closed-family ideal statement. Both of its finite-presentation hypotheses are available (p from step 1, q from the item), and its flatness hypothesis is exactly q-flatness. It explicitly provides finite-type quasi-coherent I, the exact pulled-back ideal sequence and the canonical kernel map. Tensoring by the twist is proved in a rank-one trivialization, not assumed from a definition of flatness. The identification with i_*O_Z(d) is verified in the same bases and their transition units. Preservation of the kernel by sections is simply its sectionwise definition. This step uses no coherent-Noetherian assumption.

Step 3 uses the open-locus statement exactly as stated: the equivalence for ALL maps into T. The derived-cohomology model supplies the fibre cohomology interpretation and absence of negative cohomology; the general Mathlib single-cohomology lemma supplies concentration rather than incorrectly citing full faithfulness of an unrelated construction. Each geometric fibre is a one-point field scheme, so its degree-zero module of dimension r is free of rank r. Every point has a geometric point over it, and an open subscheme containing every point is T even when T is nonreduced. The degree-zero-properties statement explicitly gives the actual cohomology module of a single locally free derived object. Thus the conclusion concerns E_d=q_*F and not an arbitrary chosen vector bundle. No reducedness hypothesis from semicontinuity is used.

Step 4 invokes the canonical derived base-change isomorphism of the existing 0B91 node for proper finitely presented q and finitely presented relatively flat F. These hypotheses were all verified in step 1. The flat-complex pullback statement applies to E_d in degree zero: on a trivializing open it is finite free, so is flat. I read the derived-module-comparison definition and ordinary pullback adjunction: they use the ordinary tensor unit, making the degree-zero map b tensor s -> b times the pulled-back section. This addresses the canonical-map clause; an abstract isomorphism alone would not establish it. The argument is local on arbitrary T and T', so no affine or finite-type restriction on g is introduced.

Step 5 cites the ring version of the monomial-cohomology node, not the field-only projective-space theorem. Its n=0 clause is read separately: the degree-d piece in one variable is canonically A via x_0^d. For n>=1 the degree-zero monomial formula applies since d>=0. The bases and transition functions in the twist definition explicitly show that coefficient maps carry each monomial section to the same monomial, which proves the claimed restriction and arbitrary-base-change compatibility rather than merely a dimension calculation. The coordinate comparison is the one already fixed in step 1.

Step 6 is the elementary matrix argument written out. I checked that the base-change isomorphism of step 4 and the monomial identification of step 5 carry alpha to the GIVEN geometric-fibre restriction map, since both act by pullback of sections. A surjective r-by-N matrix over the algebraically closed residue extension has an invertible r-minor already at the point's residue field. The inverse-minor calculation gives the explicit local section and explicit basis of the kernel, so finite local freeness of K is proved before it is used. I did not cite the local-splitting node, which assumes finite local freeness of all three terms and would be circular here.

Step 7 uses only the pullback definition and the earlier steps. Pullback preserves the specified splitting identities. The comparison square commutes on pure tensors by the same pullback-of-sections formula. The bottom kernel is the actual ideal kernel by step 2. The two established canonical isomorphisms therefore induce the canonical kernel isomorphism, proving base change for K without assuming vanishing of R^1p_*I(d) or assuming K already commutes with base change. The pulled-back exact sequence is consequently the actual restriction sequence.

I tested T empty, the zero ring on an affine base, n=0, d=0, Z empty (r=0), and Z=X (K=0). If T is nonempty and r>N the fibre-surjectivity hypothesis is impossible, as the minor argument records. The argument allows disconnected and nonreduced bases and arbitrary nonflat base changes. On the empty base the claims are vacuous, including ranks. The rank-zero case is separated before choosing a minor. No step exceeds 2000 characters and no standard or hidden comparison lemma remains inline. Every non-elementary input is cited; citations.json contains literal text from every corresponding node statement. Searches were run only with msearch.py, their hits read, and a second natural-language phrasing was tried before recording no match. The earlier searches on the seeded item were retained alongside the new authentic log entries.
