## Files written

- dag/nodes/sec-trace-formula/lem-trf-curve-closed-point-twist-witness.json: statement, split into six proof steps; existing Mathlib searches retained, five genuine new searches appended; no exact Mathlib match.
- citations.json: sixteen step/citation pairs with verbatim excerpts of the cited statements.
- No new nodes; zero new Mathlib leaves. The statement and its statement dependencies are unchanged.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag, closed-point/coherent/residue-field/skyscraper notions and Euler/tensor assertions found no project declaration giving every clause of this item. General project results and Mathlib skyscraper constructions do not constitute an attachment.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Findings and corrections

The item had a statement and Mathlib research, but no proof. Its statement is correct. No hypothesis has been changed. In particular neither smoothness nor algebraic closure of k is needed, and z need not be k-rational. The basis dimension is over kappa(z), not over k.

The full DAG and blueprint searches already locate the required results: 01T6 (pqf-lem-locnoeth-lft), 01XZ (pqf-lem-coherent-ft-locnoeth), 035C (lem-weil-pbc-closed-immersion-finite), 01Y6 (lem-weil-pbc-finite-pushforward-coherent), 00AE with module linearity (lem-weil-pbc-closed-pushforward-stalks), and 0AYT (lem-pc-chi-zero-dim-support). Creating another witness lemma, a point-stalk lemma, or a zero-support twist lemma would duplicate a result or restate a clause. Instead the split writes out annihilation, the basis, singleton dimension and tensor swap.

The current literature/blueprint/latest chapter, unit and locality ancestor were read. The supporting coherent-curve calculation is inherited through the item's recorded ancestor chain and is explicitly located in its blueprint.from.place. This delivery changes no chapter, unit or ancestor route. Searches through blueprint_refs.py for closed points, coherent pushforward, invertible tensor, closed point invertible, zero dim support, chi, skyscraper and residue field stalk found no blueprint node stating this combined witness; same_as remains empty.

## Not duplicates

No new nodes. The generic 0AYT result is cited directly, rather than recreated in sec-trace-formula. The parent's Euler-tensor formula is not used: doing so would be circular.

## Review by Q146

I read Stacks varieties.tex, lemma-degree-on-proper-curve (0AYV), especially the closed-point witness in condition (2), and lemma-chi-tensor-finite (0AYT), including its rank-n tensor conclusion and proof. I also read the actual statements of every cited DAG node, and coherent.tex 01XZ and 01Y6, morphisms.tex 01T6 and 035C, sheaves.tex 00AE, and modules.tex 08KS. There are no new nodes requiring a separate source review.

Step 1 uses the proper-morphism definition only for finite type, the locally-Noetherian definition for spectra of fields, the 01T6 statement to make C locally Noetherian, and the 01XZ equivalence to make O_Z coherent. The field ideal calculation and its one-generator structure module are written explicitly. Thus there is no unmentioned regularity or Noetherian hypothesis.

Step 2 uses the precise closed-immersion-is-finite statement, then finite-pushforward coherence. I checked that the latter requires a locally Noetherian target and a coherent source module: both are supplied by step 1. It is not an etale constructible-sheaf result.

Step 3 uses the spectrum definition for the one-point spectrum of a field and its global sections, the stalk definition for its only neighbourhood, and both clauses of the closed-pushforward-stalks statement. The latter explicitly supplies O_{C,z}-linearity for the stalk-map action and zero away from the image. The canonical immersion in the hypotheses has the residue-quotient action, as the residue-field definition says. The statement is not being inferred from a set-valued geometric stalk comparison.

Step 4 uses the vector-dimension and topological-Krull-dimension definitions. I checked its elementary calculation: maximal-ideal elements have zero residue; 1 is a basis of the residue field over itself; z is distinct from xi; and the support singleton has a chain of length zero and none of greater length. No separate node is needed for these calculations. This also establishes actual support equality, not just containment.

Step 5 cites exactly the third assertion of lem-pc-chi-zero-dim-support. It gives both coherence of G tensor L and its Euler equality under precisely properness, coherent G, zero-dimensional support and invertible L. Each hypothesis has already been checked. This is the generic 0AYT black box explicitly used by the item's 0AYV source, recorded as an off-unit tool in split_report.tool_uses; it changes no proof route.

Step 6 expands tensor symmetry using balanced generators and sheafification from def-pur-sheaf-tensor-product rather than hiding a monoidal lemma. I checked balancing in both directions and commutation with restrictions; their composites are identity before and after sheafification. The coherent definition transfers finite generation and the kernels of all maps from finite free modules along an isomorphism. Cohomology functoriality sends the inverse sheaf maps to inverse k-linear maps, so the finite dimensions in the Euler definition agree. This supplies the requested left tensor, not just the right tensor.

I checked B--E in delivery-errors.md against these files: no new undeclared notions or unsourced nodes, all uses appear in proof_deps with a verbatim statement quote, no proof-of-a-cited-node is used, no parent formula is invoked, no clause is moved to a new node, and every non-elementary fact is an existing citation. All six steps are under 2000 characters. The elementary flags on steps 4 and 6 cover written calculations, not hidden geometric inputs.

Small cases checked: a non-rational closed point of degree d on P1 over k has residue stalk dimension one over kappa(z), while its Euler characteristic is d; a nontrivial line bundle O(1) still has a one-dimensional fibre there, so the equality holds. A singular closed point on an integral proper curve also has residue action annihilated by its maximal ideal; no DVR assumption occurs. Replacing z by a nonclosed generic point would invalidate the zero-off-support calculation, but is explicitly excluded. The zero-module exception does not arise since kappa(z) is a nonzero field.

## Unfinished work

None in this one-level split. Existing dependencies remain their owners' work. No Lean was written and no compiler, Lake or local project check was run.
