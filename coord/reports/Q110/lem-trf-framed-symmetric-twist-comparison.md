## Files written

- dag/nodes/sec-trace-formula/lem-trf-framed-symmetric-twist-comparison.json: statement item, now split into seven explicit proof steps; Mathlib verdict: no exact match for the combined framed sheaf statement.
- citations.json: one verbatim cited-statement quotation for every node used in every numbered step.
- searches.jsonl: actual msearch.py results, including two distinct semantic phrasings, Loogle, LeanSearch, and two source searches.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, the item id, symmetric algebra, symmetric twist, and frame/tensor terminology. The existing SymmetricAlgebraSheaf.lean builds a symmetric-algebra presheaf and affine relative spectrum; it does not state this item's framed isomorphism with every transition, degree and restriction clause. In particular it is not an attachment of this item. No Lean was written and no compiler, Lake or build tool was run.

## Wanted literature

None. All sources needed for this split are present in literature/stacks-project/.

## Findings and changes

The statement is unchanged. The source Tag 02NC ends its local-trivialization argument with details omitted. The delivered proof supplies the module maps, inverse identities, affine symmetric extensions, degree calculation and arbitrary-open compatibility needed for the symmetric-algebra specialization; it does not claim that 02NC itself states this whole subsidiary lemma. Accordingly proof_origin.by is agent, with the source route and supporting sections named.

An initial draft described the graded pieces through a sheafification assertion not explicitly stated by its cited construction node. I replaced that sentence with the existing def-trf-canonical-symmetric-graded-algebra, whose statement explicitly specifies the affine degree submodules, degree-preserving restrictions and canonical affine-section identifications. This avoids taking an extra theorem from a construction node. Restriction of the symmetric algebra and tensor product is explicitly justified using the existing module sheafification comparison, not assumed from a vague appeal to functoriality.

The six original statement dependencies remain unchanged. The proof uses existing nodes only. The whole DAG was searched for symmetric algebras, the frame/tensor construction and Tags 01CG/01CI; blueprint_refs.py searches for symmetric algebra and frame found no blueprint statement equal to this item. Its existing blueprint ancestor and precise from.place are retained; same_as is empty. This is a subsidiary algebra input on the existing 087S/02NC projectivity-conversion branch, not the statement node of sk-i-curve-zero, so its unit's realized fields were not changed.

## Mathlib search reading

All newly recorded searches are copied from the actual searches.jsonl records. The two interrupted LeanFinder sessions had already completed and written their results; the log was read before proceeding, and those calls were not repeated. The results name free-module/sheaf generator formulas, the ring universal property, a ring tensor unitor, and ordinary symmetric-algebra equivalences. I read Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean, in particular lift at line 99, algHom_ext at line 120 and IsSymmetricAlgebra.of_equiv/comp_equiv. Those are tools for ordinary ring algebras; none includes the sheaf restriction comparison and homogeneous frame transition required here. The existing DAG already carries the ring universal property as a Mathlib leaf, so no duplicate was created. The AlgebraicGeometry grep found no framed symmetric twist theorem. The second source grep located the ring universal property and extensionality, confirming the distinction.

## Review by Q110

I read the item, its parent lem-trf-relative-proj-invertible-twist, the chapter/unit records, the three levels in SETUP.md, GOAL.md, the stage-1 contract and delivery-errors B through E. I read Constructions Tag 02NC (lemma-twisting-and-proj), including its actual trivialize-and-glue proof; Modules Section 01CF and Tag 01CG (lemma-local-tensor-algebra); Modules on Sites Section 03EK (section-tensor-product) and Tag 03CY (lemma-sheafification-presheaf-modules); Sites Tag 04B8 (lemma-almost-cocontinuous-sheafification), and the ringed-site relocalization statement 04IY. There are no new node statements to source-check.

For step 1 I opened lem-weil-pbc-module-sheafification-restriction and used its statement: the comparison preserves original unit sections and tests equality of maps on those sections. Its hypotheses hold for the inclusion of opens contained in U: the objects form a set, every cover of such an object is the same cover in the larger open site, and the coefficient sheaf is restricted from O_S. I opened def-pur-sheaf-tensor-product and lem-weil-pbc-symmetric-algebra-sheaf-construction: they explicitly give the two presheaves being restricted and sheafified. Multiplication compatibility is checked on original sections in each linear variable. No existence of a colimit over a large category is used.

For step 2 I opened def-sc-invertible-module, which supplies a local rank-one frame, and def-weil-presheaf-modules-sheafification, which explicitly says that a module-presheaf map into a module sheaf factors uniquely through sheafification. Together with the tensor definition this licenses the balanced coefficient map. The inverse identities are written on pure tensors before applying the uniqueness statement; the induction starts with the unit in degree zero. This is an elementary tensor calculation using the cited definitions and their universal properties. It does not assume that tensoring global sections computes a sheaf tensor product on a nonaffine open.

For step 3 I opened pqf-def-coherent and lem-weil-pbc-affine-opens-basis. Quasi-coherence and finite type are local properties in the stated definitions, and frames cover S; local isomorphisms therefore transfer the associated-module presentations and finite generating surjections. The affine neighbourhood can be chosen inside the framed open; no intersections of affines are asserted affine. I also opened lem-weil-pbc-module-restriction-open-immersion-colimits: clause (2) explicitly gives quasi-coherence of an open restriction, as needed to apply the next step on U. There is no noetherian, separatedness or local freeness assumption on E.

For step 4 I opened lem-weil-pbc-quasi-coherent-symmetric-algebra: its clause (a) supplies and uniquely characterizes the two algebra sheaf maps, and clause (b) is exactly the affine-section comparison. The two composite identities follow by evaluating on generators and using clause (a)'s uniqueness. I opened lem-weil-pbc-symmetric-algebra-universal-property: its concluding extensionality clause justifies identifying the affine components with the ring symmetric maps of tau_e(V) and tau_e(V) inverse. Neither a definition of symmetric algebra alone nor a theorem about full faithfulness is substituted for that uniqueness statement.

For step 5 I opened lem-weil-pbc-symmetric-algebra-graded, which explicitly says the degree-k submodule is spanned by products of k generators. I use it with the same affine comparison of step 4, and def-trf-canonical-symmetric-graded-algebra, whose statement specifies precisely the canonical affine grades and restrictions. Mapping each monomial preserves k, and applying the inverse proves graded invertibility. The extension from affine opens to the degree subsheaf uses only its sheaf condition and the affine basis; it is written out, without an uncited symmetric-power comparison theorem.

For step 6 the two cited statements are again the sheaf universal property and the sheafification/restriction comparison. The latter supplies the generator-preserving restriction identification. Each restriction of beta_e has exactly the generator formula for the restricted frame, so the former supplies equality with beta_(e restricted to V), even for nonaffine V. The maps commute with ordinary restrictions because they were constructed as sheaf morphisms. The affine statement is compatible with those same maps, not a different choice of section comparison.

For step 7 I checked the balancing identity for (ue) tensor n inductively, then computed each of the k factors of a monomial. Multiplying the k scalar factors gives (u^n)^k=u^(nk), and linearity gives the formula on the entire affine degree piece. The cited grading statement supplies exactly the spanning claim, and the cited affine basis and symmetric affine comparison let the equality be checked for an arbitrary local homogeneous section. The assumption that u is a unit is used to ensure ue is a frame; its inverse is u inverse times the coefficient map, so no missing invertibility assumption is smuggled into the construction.

I tested n=0 (unit tensor identification, no dependence on e), k=0 (scalars fixed), E=0 (the symmetric algebra is just the scalar algebra), empty opens (unique sections and maps), n=1 and k=1 (the prescribed generator normalization), and a nonfree finite module over a ring (the proof uses spanning by monomials and never a basis of E). The tensor argument works for arbitrary coefficient rings, including rings with zero divisors. The proof avoids assuming every section on a nonaffine open is a finite sum of tensor generators: the maps first descend by sheafification and homogeneous comparisons are checked on an affine cover.

The non-elementary tool uses from other units are declared in split_report.tool_uses, with their specific roles. They are generic module/sheaf or symmetric-algebra facts and do not replace any unit-level geometric argument. Definitions and Mathlib leaves are used as notions. There are no new nodes that might be elementary duplicates or clauses relabelled as a split. No proof step exceeds 2000 characters. The dependency union agrees with proof_deps, and citations.json quotes the statements actually opened; no cited proof is treated as a stronger statement.

## Not duplicates

No new nodes were created.

## Unfinished work

None in the stage-1 split. No attachment claim or statement dispute remains. Server preflight and delivery follow this report.
