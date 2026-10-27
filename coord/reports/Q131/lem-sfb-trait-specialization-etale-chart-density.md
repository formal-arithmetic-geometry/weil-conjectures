# Worker report

Group Q131; item lem-sfb-trait-specialization-etale-chart-density; stage 1; 2026-10-23.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-trait-specialization-etale-chart-density.json: statement, split into six proof steps; no Mathlib match for the whole criterion.
- citations.json: literal statement extracts for every citation of every proof step.
- report.md and searches.jsonl: review and actual Mathlib search log. prepare.py is sandbox-only preparation code.

No new nodes; no new Mathlib leaves. The statement, statement dependencies, inherited source and blueprint provenance are unchanged. The sandbox initially contained no node, proof, report, citations or searches to resume.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and specialization/chart/density vocabulary and for henselian/etale lifting. GenericOpenGeometricFibreDensity.lean proves a shrinking statement for geometric fibres, not this stack criterion. Existing scheme-level henselian sections and ring lifts cover ingredients only. No project declaration found states the complete item.

## WANTED

None. All sources used were available in literature/stacks-project. No SGA source is used.

## Audit findings and changes

The live item was unsplit and already had a correct statement. It is an agent generalization of the trait specialization in moduli-curves.tex 0E86, not a verbatim theorem of that tag: 0E87 is its stable-moduli application. In particular neither tag by itself asserts lifting a prescribed special point through an arbitrary etale chart. The proof now supplies that argument using an algebraic-space atlas and the existing henselian ring lifting statement. No statement dispute or weakening is needed.

The inherited blueprint ancestor command returns None. I preserve the inherited null from.node and the exact from.place/via chain rather than inventing an imported ancestor. I read the current latest unit and its direct-image proof clause (3), as well as the recorded chapter/unit. Its current direct-image paragraph is an assembly via compactification. This auxiliary stable-moduli branch is inherited from the earlier alteration expansion; this item does not change that route or the fixed chapter/unit.

Whole-DAG searches checked strict henselian sections, algebraic-space atlas lifting, power-series completeness/locality/domain, 08HQ, 0ALJ, etale composition/base change, and scheme atlas fibre products. Whole-blueprint searches (blueprint_refs.py) for henselian section, trait specialization, henselian, etale atlas and smooth dense found no imported equivalent of the item. Broader direct searches in latest found no replacement. The exact relevant existing nodes were reused rather than creating a general section lemma which would mostly relocate the lifting clause.

The new Mathlib searches ran only through msearch.py. I read the results: semantic searches return scheme smooth/etale charts, henselian-ring criteria, rational-map density, and one unrelated manifold LiftPropOn; Loogle returns scheme etale permanence. The grep of stack/trait/henselian vocabulary found no stack density statement. A second semantic phrasing also found no match. These do not give a one-line specialization proving the framed stack lift. Existing search records of the live item were retained. An exploratory etale-permanence search was useful for checking vocabulary, but the existing lem-trf-space-chartwise-etale-permanence makes a new Mathlib leaf unnecessary.

## Tool uses

The split_report.tool_uses records generic tools from other units. The power-series local/quotient/complete/domain lemmas and complete-pair-henselian are commutative algebra, not a different direct-image route. The algebraic-space fibre-product and etale calculus statements are generic atlas tools, not trace-formula input. det-pe-morphisms-etale-comparison is used only for etale implies weakly etale; lem-fix-weakly-etale-algclosed-section only supplies a rational point in the atlas fibre. lem-sc-etale-henselian-ring-lift is the exact prescribed-residue lifting theorem. None is replaced by a theorem of the item's own unit. Definition nodes and the affine-shrinking Mathlib leaf are notions/tools under the contract.

## Not duplicates

No new nodes. In particular, the existing scheme section node lem-sbc-strict-henselian-etale-neighbourhood-section does not specify which closed lift a section has, so I do not cite it for that stronger conclusion. The existing lem-sc-etale-henselian-ring-lift does specify the reduction map and is what step 3 actually uses. The existing algebraic-space and etale-permanence nodes avoid creating duplicates of general atlas machinery.

## Review by Q131

I read moduli-curves.tex 0E86 (lemma-smooth-dense) in full: its final argument maps the generic and closed points of a power-series trait to the open locus and the given point. I also read 0E87 (lemma-smooth-dense-in-stable), whose proof restricts that density to an open. I kept that specialization argument and supplied the additional etale-chart lifting with a prescribed framing. For the lifting source I read algebra.tex 08HQ (lemma-map-into-henselian), including its tensor-product argument, and more-algebra.tex 0ALJ (lemma-complete-henselian), whose hypothesis is completeness at the very ideal being used. I read algebra.tex Remark 032C for the power-series source and the statements of its existing local-ring, quotient, variables-complete and domain nodes. There are no new node sources to certify.

Step 1 uses exactly the local-ring, quotient-of-variables, variables-completeness and complete-pair-henselian statements. The first two identify the maximal ideal and the particular quotient as constant coefficient; the next two give the henselian hypothesis for (R,(t)). I verified this is the maximal ideal, not an unrelated adic ideal. We need only henselian local here; no extra strictness theorem is hidden.

Step 2 uses the full conventions of def-sfb-stable-pointed-moduli-groupoids to make the prescribed 2-isomorphism a point of the 2-pullback and to represent the pullback by an algebraic space. The etale-base-change clause of lem-sfb-dm-etale-atlas-calculus supplies its etale map to T. I read stacks-morphisms.tex 0CIN and 0CIM and the compatibility paragraph immediately preceding 0CIM. def-trf-algebraic-space supplies a scheme atlas. lem-trf-space-fibre-products-etale-covers says the pullback of that atlas is a surjective etale scheme map, precisely the fibre P over the specified e, not merely the fibre over its underlying point. lem-trf-space-chartwise-etale-permanence supplies the composite W to T. I read spaces.tex 025Y and spaces-properties.tex 03FR and its composition/base-change discussion. Finally, det-pe-morphisms-etale-comparison explicitly gives etale implies weakly etale, and lem-fix-weakly-etale-algclosed-section explicitly gives a section of the nonempty fibre P. I read proetale.tex 0F6C and its residue-field argument. Thus the lift remains over the original field Omega. No field enlargement, finite-type assumption on V, quasi-compactness or separatedness is smuggled into this step.

Step 3 uses the full affine-shrinking statement, which includes both the lifted geometric point and etaleness of the affine composite. I checked the existing leaf's statement and its 04HX/01HR/02GP/02GN/01JR source references. Then I applied the exact statement of lem-sc-etale-henselian-ring-lift: its R,B,S,K become R,B,R,Omega, its beta is identity, and epsilon is the constant-coefficient surjection with maximal kernel from step 1. It yields both equations f alpha = identity and epsilon f = theta. def-weil-affine-spectrum gives the contravariant scheme maps and equality translation. This corrects the tempting but unjustified shortcut of applying an unpointed section-existence statement and claiming it preserves the chosen point.

Step 4 is an explicit elementary unwinding of the 2-fibre product and its equivalence to a discrete groupoid. I reread the whole moduli-groupoid definition, including the equations for arrows in a 2-fibre product and the discrete representing algebraic-space convention, and def-trf-scheme-algebraic-space's actual representable h_T. The isomorphism of restricted triples has identity scheme components, so its compatibility equation really recovers the prescribed special-fibre isomorphism. This checks the framing rather than only the underlying topological point.

Step 5 uses the domain node for the zero prime and the local-ring node for the unit criterion. The remaining calculation is written out: choose the first nonzero coefficient of a series, factor t^n, and invert the remaining unit; this identifies the puncture with the generic point. Every basic open about (t) contains (0), so continuity of the scheme map sends this specialization to V. I did not use topological density pullback along an open map without having already proved density, nor did I assume V irreducible or reduced. Membership in the open is invariant under the constructed isomorphism because it is a full substack.

Step 6 uses the existence clause of def-weil-algebraic-closure and the residue-field description of def-weil-geometric-point. They let us address every point y, not just closed points or k-rational points. The trait assumption is applied to the object a(v) over this algebraic closure of kappa(y); the structural inclusion makes it an algebraically closed extension of k. The elementary closure argument now proves density at y. This verifies the no-finite-type claim, which would fail as an argument if one only tested closed k-rational points.

I checked delivery-errors B--E point by point. Each cited statement was read and a literal extract placed in citations.json (C4); every non-elementary input is one of those named statements (C1). No new definition or statement hides a missing hypothesis, no proof clause is moved to a new node, and there are no new Mathlib leaves. Edge cases: V empty; an etale chart whose image omits other components of the stack; an infinite disjoint union of charts; nonclosed y with transcendental residue field; the identity chart; and nontrivial stabilizers with a different prescribed special-fibre isomorphism. The fibre product retains that isomorphism, so the last case is handled by lifting its actual point. An etale map meeting only the puncture has no prescribed closed lift and is never used as such. Every step is below 2000 characters; no long step hides an additional lemma. The proof dependencies will be checked for cycles by the required server dry run.

## Unfinished work

None in the stage-1 split. Existing unsplit dependencies remain their owners' items. No Lean was written and no compiler, Lake, build, repository write or git command was run by the worker.
