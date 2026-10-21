# Stage-1 delivery: lem-sp-etale-sum-coefficient-computation

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-etale-sum-coefficient-computation.json: statement, split; not a Mathlib leaf. The statement and its statement dependencies are unchanged. Five proof steps and their dependencies, proof origin, search records, and split report were added.
- citations.json: fourteen verbatim statement quotations, one for each step/node citation.
- No new DAG nodes; no new Mathlib leaves. searches.jsonl records the searches performed by the required command. prepare.py is sandbox preparation only, not a project delivery file.

## Attachments

None. Searched the project source by the exact blueprint identifier and the notions of sheetwise compactified etale pushforward, sum extension, coefficient change, and counits. The existing etaleLowerShriek and its exactness/adjunction declarations in WeilConjectures/SixFunctors/Etale/LowerShriek/EtaleMap.lean cover only underived sum extension, not every clause of this item. A general Mathlib tensor/sum declaration is likewise not an attachment.

## WANTED

None. This is explicitly an agent calculation from the existing named geometric/derived interfaces, with the Stacks pure-tensor construction as its source; neither Stacks nor the blueprint is claimed to state the full normalized derived-map assertion verbatim.

## Audit of the imported item and route

The item was unsplit with no proof. I found no false statement to repair. The substantive hazard is replacing a specified derived adjoint transpose by an arbitrary isomorphism with the same endpoints. Step 3 uses lem-sp-acyclic-flat-proper-coefficient-model, whose statement explicitly represents that very map on acyclic-flat models; step 4 then evaluates that representative. The argument does not cite the parent lem-sp-et-proet-coefficient-compatibility or the downstream etale-sum-counit-scalar node.

The existing normalization theorem already implies the requested acyclicity: apply its isomorphism to any sheaf M in degree zero, then take positive cohomology. This avoids creating a node for a clause of the item. The same degree-zero normalization gives r_*j_!M = e_Σ!M and fixes its sheet components. Flatness of r_*j_!P follows from that identity and the existing sum-extension flatness theorem. K-flatness is then the existing bounded-above-flat theorem.

The blueprint ancestor is det-sp-reduction-exceptional. I read its main-20261015 Charts proof paragraph in sk-lem-sp-reduction-exceptional.proof.md: summation over geometric etale fibres commutes with coefficients. This calculation realizes that paragraph, as requested by the parent split. I read the current chapter and unit records, including the coefficient-compatibility clause of sk-thm-sf-compatibility. No chapter or unit record was changed. The generic K-flatness, Noetherian permanence, open tensor, and compact-support normalization tools are declared in split_report.tool_uses; they implement the stated route.

## Mathlib and duplicate searches

I searched the whole imported blueprint with blueprint_refs.py for etale/coefficient, etale sum, and acyclic flat proper, and searched the DAG by the relevant notions. The ancestor command gives det-sp-reduction-exceptional. The useful statements already existed, so no new node was created. Broad blueprint searches also located compatibility statements with different coefficient domains; none supplies the entire bounded acyclic-flat computation as a one-line specialization.

Using msearch.py under Q120, I ran LeanFinder with two distinct formulations, Loogle with CategoryTheory.Sheaf, TensorProduct, the AlgebraicGeometry grep for etale sums/shriek/acyclic flat, and LeanSearch for the scalar comparison on etale sheets. All services returned successfully. I read the returned hits. TensorProduct.directSumLeft and its generator formula were checked in Mathlib/LinearAlgebra/DirectSum/TensorProduct.lean:67 and following: these give the module tensor/direct-sum calculation only. Other hits concern generic exact derived functors, pushforward adjunctions, or unrelated condensed objects. None states the geometric acyclicity or identifies the specified proper derived transpose. The original item's earlier search records were retained and the actual Q120 queries appended.

## Not duplicates

No new nodes. In particular, lem-sp-acyclic-flat-proper-coefficient-model supplies a general conditional proper-map computation; this item verifies those conditions geometrically for j_!P and evaluates the resulting map in the normalized etale sheet model. Neither is a replacement node for the other.

## Unfinished work

None at this one-level stage-1 split. Existing cited nodes retain their own independent proof obligations. No Lean was written and no compiler, Lake, or build was invoked.

## Review by Q120

I checked the split against delivery-errors B-E with the node statements and sources open. For the item I read Stacks more-etale.tex Tag 0GL6 (remark-Rf-lower-shriek-change-of-rings), which states the change-of-rings compatibility, and Tag 0GKF (lemma-f-shriek-projection), especially its actual rule (Z,s) tensor t maps to (Z,s tensor f^-1 t). I also read etale-cohomology.tex Tags 03S5 (proposition-describe-jshriek), including the germ of a sheet generator, and 0F4L (lemma-shriek-into-star-separated-etale), including extension on a clopen graph and zero elsewhere. These explain why taking a sheet component keeps the same index after tensoring. There is no SGA input.

Step 1 cites the definition of proper (which includes finite type), finite-type-over-Noetherian (whose statement allows any Noetherian base, not just a field), and the full etale compact-support normalization theorem. The last really asserts an isomorphism on ordinary unbounded module derived categories, for finite commutative coefficients and separated finite-type etale maps of Noetherian schemes. On M[0], its other endpoint is a sheaf in degree zero. Thus positive cohomology vanishes without assuming an acyclicity theorem that the node did not state. Its degree-zero clause supplies exactly the component normalization used later. W is Noetherian because r is proper over the Noetherian V. Both A and B are finite, so both normalization applications satisfy the torsion-ring condition, even when B is not A-flat.

Step 2 cites open tensor for preservation of flatness by j_!, the sum-extension flat/K-flat theorem for the flatness of e_Σ!P^n, and bounded-above-flat-K-flat on a ringed site. I read sites-cohomology.tex Lemma 06YS (lemma-bounded-flat-K-flat), including its bounded-above hypothesis. Both image complexes retain the same bounded degree interval as P, so this condition holds. Flatness is over A throughout this step; it is not inferred from sectionwise flatness or confused with B being A-flat.

Step 3 cites the complete statement of the general acyclic-flat proper coefficient model and open tensor. I checked every hypothesis of that statement: proper r, Noetherian W,V, finite A,B, finite degree support, flat C^n and r_*C^n, and higher-image vanishing both before and after tensoring. Step 1 handles the B-side vanishing for an arbitrary B-sheaf P^n tensor_A B. Open tensor identifies this with C tensor_A B. The model theorem states equality with the named counit transpose, not only existence of an isomorphism. This is why no extra derived-adjunction lemma is silently assumed in the sheet computation.

Step 4 cites the direct-image evaluation definition, open tensor (identity on U), normalization (component extraction), and the sheafified direct-sum definition. It is elementary after step 3: evaluate the ordinary adjunction's counit on a pure tensor, then take its component. I checked balancing and additivity explicitly, and used locally generated sheaf sections instead of assuming a globally split finite etale cover. In particular I deliberately did not use the graph-extension/injectivity nodes whose actual statements assume finite etale: e here need not be finite. The support and sheet identification comes from the more general compact-support normalization statement. This avoids a C4 hypothesis mismatch.

Step 5 cites the model theorem's naturality in chain maps and the normalized isomorphism, and checks the differential on the displayed generators. The differential acts on x_s and leaves b in degree zero, so there is no omitted Koszul sign. The finite-support calculation applies to empty index sets; zero complexes and zero coefficients give zero maps. The identity coefficient map gives the identity generator formula. A nonflat map such as Z/4 to Z/2 is permitted: no step applies exact tensor with B over A. There are no new statements requiring small-case tests, and all five proof steps are below 2000 characters. All fourteen citations.json quotes were checked as literal substrings of the cited statements. The item's statement, blueprint provenance, and existing search records were retained.
