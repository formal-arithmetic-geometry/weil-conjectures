# Q08: lem-wf-tensor-weil

## Files written

- dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-tensor-weil.json: statement; five-step split; no Mathlib match.
- dag/nodes/sec-algebraic-groups-lie-algebras/lem-ag-uniform-complete-tensor.json: statement-only underlying closure lemma; unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: actual msearch.py results, retained without alteration.

## Attachments

None. I searched the live WeilConjectures source by the blueprint id and tensor/Weil terminology. AlgebraicGeometry.Etale.WeilComplex.tensor, WeilConjectures/SixFunctors/Etale/Derived/WeilComplexTensorHom.lean:360, has a genuine proof of the finite-coefficient bifunctor. Its implementation notes at lines 56-64 explicitly say that the rational E-adic categories in this item are not the implemented model: the declaration uses finite Lambda and Dctf, not the present raw rationalized compatible-uniform category. It also only places triangulated exactness on the underlying tensor. Thus it is not an exact attachment. The Sheaf/Paper/WeilTensorProduct.lean module constructs the ambient tensor and its Frobenius for def-wf-tensor-product; it does not prove the constructible restriction of this item.

## WANTED

None. The current and master blueprint, the Bhatt-Scholze paper, and the needed Stacks source are present.

## Source error

STATEMENT-DISPUTED: the imported phrase “exact bifunctor” is ill-typed if read as an exact functor between triangulated WeilD categories with the current definitions. The current reviewed def-wf-weil-category explicitly supplies no triangulated structure on its category of fixed pairs. Its objects and commuting derived morphisms cannot simply be identified with an equivariant derived category. A type check of the imported assertion fails at the prerequisite “triangulated structure on WeilD,” before any tensor claim can be expressed. I have retained the same WeilD objects, arrows, coefficient model and tensor formulas, and made exactness the underlying assertion: fixing either underlying object gives a shift-compatible triangle-preserving functor on C_E. This is the interpretation expressly used by the upstream tensor docstring at lines 354-359. I do not claim to construct a triangulation on the pair category.

The imported proof proves neither constructible closure nor exactness. It also mentions a “Weil-cocycle condition,” whereas the current definition requires precisely one invertible Frobenius arrow, whose iterates are determined. The proof now uses that definition rather than introducing another condition. No target is changed, and neither the cyclotomic unit theorem nor its proof is edited.

## Not duplicates

lem-ag-uniform-complete-tensor vs lem-pur-integral-operations-preserve-constructible: the latter uses def-weil-derived-complete-integral-detailed (complete objects with uniformly bounded finite reductions), not the category with common adic-lisse complex models and compatible etale-origin witnesses of def-weil-pbc-bounded-constructible-complete. Neither an equivalence nor this stronger closure is stated there; the new lemma asserts the missing closure for the precise category, and has no pullback clause.

lem-ag-uniform-complete-tensor vs lem-fix-constructible-tensor-completion: the existing lemma proves that ordinary tensor is complete and the canonical completion comparison is invertible, in the detailed integral category. It does not assert membership in the compatible-uniform category or produce its common tower models and etale witnesses.

lem-ag-uniform-complete-tensor vs det-thm-sf-pf-field-tensor: the latter concerns derived categories of condensed coefficient rings and their localizing closures; the new lemma concerns integral completed ring-sheaf coefficients and a raw rationalization input. No comparison of these coefficient models is assumed.

lem-ag-uniform-complete-tensor vs lem-sf-tensor-ctf: the latter is a finite coefficient result, requiring finite Tor amplitude; the new lemma concerns the entire completed integral tower and its common models and compatible witnesses.

lem-ag-uniform-complete-tensor vs lem-zl-rational-realization-tensor-comparison: that node is a specified realization comparison for rational tensor; it does not prove the integral compatible-uniform closure here.

lem-ag-uniform-complete-tensor vs lem-pur-derived-pullback-tensor-iso: that node is monoidality of pullback and the coefficient comparisons, not closure of this integral full subcategory.

I searched the entire DAG by completed tensor, uniform/constructible tensor and Bhatt-Scholze 6.5.5; searched all blueprint nodes with blueprint_refs.py by tensor, completed tensor, tensor closure, tensor constructible and uniformly bounded constructible; and checked the live Lean source. The blueprint's only tensor closure hit at the field stage uses the distinct condensed model. No new node restates the Weil bifunctor, its Frobenius map, or its exactness clause.

## Review by Q08

I read the current main-20261015 lemma and its proof in full and compared the master text (the item statement and proof are unchanged between these snapshots). I read the chapter record and both the stored and current sk-p-cyclotomic unit. This tensor lemma is unrelated recorded-in-advance material nested under that unit, not its key cyclotomic proposition. The split keeps the source's underlying tensor/Frobenius route. The off-unit statements are generic tools declared in split_report.tool_uses; none substitutes for a cyclotomic proof.

For the new node I read Bhatt-Scholze Lemmas 6.5.3-6.5.5 and their proofs, especially the tensor-completeness argument on pages 49-50. The paper's D_cons is not automatically our compatible uniform category. That is why the new node is stated as an additional refinement, unsplit, and its source field expressly says so. Its intended argument must check common local models and compatible witnesses, not merely cite the paper's tensor closure. Over a DVR finite modules have finite free resolutions, so bounded adic-lisse finite-type local complex models can, after local refinement, be replaced by bounded finite-free models. Their total tensor is again bounded with finite-type adic-lisse terms. Finite reductions are given by balancing the two scalar factors, and tensoring the etale-origin witnesses gives compatible witnesses by the same quotient identities. Completion must be compared with these normalized reductions. These are the substantive underlying facts delegated to this one node, rather than hidden as an elementary step of the Weil proof. No proof has been placed in the statement-only node.

Step 1 uses the new node's exact membership conclusion, the raw rational-category definition (same integral objects), the current Weil category (the same compatible-uniform integral source), and the tensor definition (Koszul completion, then rationalization). I checked all these statements, rather than identifying the different D_cons, finite, or condensed models. The separated finite-type geometric fibre has exactly the noetherian finite-dimensional, invertible-ell setting already used by that Weil category. There is no Frobenius-stable integral lattice requirement: the Weil isomorphism is allowed to be a rational morphism.

Step 2 uses the tensor definition's explicit comparison, the ringed-topos theorem's simultaneous naturality, the completion reflector's naturality, and the derived-tensor descent theorem's uniqueness for transformations. I read each statement. The proof explains extension from representative maps to derived maps and then rational fractions. The naturality equation is in the correct direction PT(K,L) to T(PK,PL).

Step 3 is the short inverse calculation from the definitions. The inverse order is mu inverse after tensor of the inverse Weil arrows; no monoidal coherence theorem or extra group-action axiom is being silently invoked. The category needs one isomorphism, not a further cocycle datum.

Step 4 writes every equality proving that the tensor of two commuting morphisms commutes with tensor Frobenius. I checked source/target types and the placement of P(u), P(v) and mu. The identity and composition equations follow directly from the ambient bifunctor and equality of underlying arrows. These two elementary steps use no non-elementary unstated lemma.

Step 5 uses the existing fixed-K-flat tensor theorem, which explicitly includes coherent shifts, cones and connecting maps, and the existing exact Koszul completion theorem with its precise strict-tower formula. The resolution theorem supplies the required flat-term K-flat model. The uniform-category theorem supplies exactly the inherited integral triangulation, and the scalar-localization theorem supplies exactly the raw rational triangles and induced shifts. All five statements were read. The fraction formula in the tensor definition gives the localized functor, so there is no unproved identification of a different rational tensor. This proves underlying exactness; it does not infer a triangulation on fixed pairs.

I tested the statements on the empty scheme, the zero complex, the coefficient unit, shifted coefficient units and torsion integral models A/varpi. The tensor of two torsion models can have negative-degree Tor (A/varpi tensor^L A/varpi has degrees -1 and 0); the new node does not incorrectly assert degree-zero tensor or a field-flatness argument at finite quotients. Torsion representatives vanish after rationalization as they should. A Weil scalar varpi^-1 is permitted even when it preserves no integral lattice. Products of the two Frobenius inverses work for arbitrary non-scalar isomorphisms as well. Tensor exactness here is separate exactness in each variable, not exactness as a joint functor of a product triangulated category.

I checked delivery-errors B-E: the new node is self-contained and statement-only, each mathematical notion is introduced or inherited through a defining node, searches are genuine msearch calls with a second semantic phrasing, no Mathlib match was confused with a generic ingredient, and no unsearched helper or clause-only restatement was created. Search hits for ordinary module adic completion and light condensed monoidal structures were read and rejected because they lack this category's tower and witness conditions. All citations have verbatim statement quotations in citations.json. Every proof step is below 2000 characters (775, 866, 510, 807, 1248), so none hides a long lemma. No SGA source, compiler, Lake, repository write, manual git operation, or subagent is used.

## Could not finish

Nothing in the one-level split remains unfinished. The new underlying closure node deliberately remains unsplit, as required for newly introduced dependencies. Final acceptance remains the maintainer's independent mathematical review.
