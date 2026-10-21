## Worker report

Written: `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-ordinary-evaluation-localization.json` (statement, split; no Mathlib match), `citations.json`, and this report. The temporary `write_split.py` records the sandbox generation only. No new nodes, no Mathlib leaves, no Lean writing or compilation, and no repository or launcher edits.

Attachments: none. The upstream tag search has no declaration for this item. The scheme-only `AlgebraicGeometry.schemeOrdinaryEvaluation_localization` and the ordinary module/sheaf evaluation declarations do not state the theorem for an arbitrary ringed site. The upstream `ihomUnitTensorToIhom` also uses the opposite tensor-adjunction convention and supplies no ordinary-complex augmentation normalization. Neither is an attachment.

WANTED: none.

The imported item contained no proof. I retained its mathematical statement and hypotheses and supplied nine steps: actual sheafified component construction, differential calculation, auxiliary K-flat replacement of E, fixed comparison coordinates, normalized coefficient evaluation, normalized F-valued evaluation, the ordinary associator calculation, the derived coherence calculation, and cancellation of a bijection and an isomorphism. Nothing is unfinished within this one-level split. All non-elementary ingredients already have nodes.

The source annotation of the imported tensor comparison deserves care: `lem-weil-pbc-site-derived-tensor-descent` explicitly gives its displayed comparison on K-flat complexes with flat terms. The present item assumes only K-flatness of F and D. I do not apply that restricted assertion to F,D. The item also explicitly assumes `def-coef-ringed-tensor-hom-model`, whose statement supplies a natural comparison for arbitrary K-flat pairs, and that is the comparison used in steps 3, 5, 6 and 8. Its normalization agrees with the tensor-descent comparison on the flat-term subcategory. No termwise flatness is added to the theorem.

## Sources and searches

I read `sites-cohomology.tex`, section-hom-complexes (the Hom differential), lemma-compose (0A90), the construction in section-internal-hom and lemma-internal-hom (08J9), lemma-internal-hom-composition (0A98), lemma-dual/equation-eval (08JD/08JE), lemma-K-flat-resolution (06YS), and lemma-symmetric-monoidal-derived (0FPT). The coefficient evaluation in 08JD comes from composition and the identification with Hom out of the coefficient unit. The displayed fixed-augmentation equation is an explicit representative proof supplied here, not a verbatim theorem claimed to occur in Stacks; `proof_origin.by` is agent. I also read `sites-modules.tex`, section-internal-hom (04TT/03EM), section-tensor-product (03EK), and lemma-sheafification-presheaf-modules (03CY), to check that equality on the actual sheafification-unit images is sufficient.

The current blueprint ancestor file is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.md`. It contains the two displayed internal-Hom identifications but no proof paragraphs. I therefore replaced the inherited reference to a nonexistent second proof paragraph by its actual second displayed isomorphism. This is the same coefficient-dual evaluation route, without any SGA citation or unit-level route change.

I searched the whole DAG for 08JD, 08JE, 0A98, ordinary evaluation, uncurrying and K-flat replacement, and read the existing tensor-Hom model, representative evaluation, K-flat resolution, derived Hom, Hom-complex and total-tensor statements. `tools/blueprint_refs.py ancestor` identifies `det-thm-sf-ctf-stability-internal-hom`; searches for ordinary evaluation, dual tensor Hom, tensor Hom, and 0A90 find no exact blueprint duplicate. The existing scheme-localization theorem was read as a possible duplicate and rejected for its scheme-only domain, not repackaged as a ringed-site leaf.

All six fresh Mathlib searches are the actual commands logged in `searches.jsonl` and copied into the item's searches. They include LeanFinder with two phrasings, Loogle, LeanSearch, and two grep queries. I read their returned names/types. The relevant ordinary-module candidates `dualTensorHom` in `Mathlib/LinearAlgebra/Contraction.lean` and `ModuleCat.ihom_ev_app` in `Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean` were also opened. They have neither the ringed-site cochain domain nor the fixed-augmentation derived comparison, so no Mathlib leaf was declared. The older searches already present on the imported item were retained unchanged; they are not represented as fresh Q116 searches.

## New nodes

None. The construction and the sign identities are elementary steps, and the existing model supplies the needed uncurrying theorem. In particular neither the ordinary-map clause nor the final derived identity was moved into a renamed child.

## Not duplicates

No new-node/existing-node pairs: there are no new nodes.

## Tool uses

`lem-pc-kflat-resolution` is used as the generic ringed-site resolution theorem. `lem-sf-ringed-derived-closed-symmetric-monoidal` supplies the generic structure already assumed in the item. Both are recorded in `split_report.tool_uses` for the maintainer to judge; no top-level maintainer-owned `tool_uses` field was written. The coefficient-Hom model and its representative evaluation are definitions of structures fixed in the item's hypotheses.

## Review by Q116

I checked the node and all statements in the steps' `uses` lists against the sources above. There are no new statements needing a separate source audit. The statement is valid for arbitrary unbounded E and F: the Hom uses a product while the tensor total uses a coproduct, so the construction introduces no convergence, finiteness, or product-versus-sum assumption. Smallness is exactly the item's chosen module universe; no new index category or extra universe assumption is introduced.

Step 1 uses `def-pur-sheaf-hom` for maps on every localized site, `def-pur-hom-complex` for product projections, `def-pur-sheaf-tensor-product` for the actual associated presheaf tensor, `def-weil-presheaf-modules-sheafification` for unique factorization, and `def-pc-tensor-complex-sheaves` for coproducts. Each statement says precisely this. The bilinear map is defined on all objects over U, with y restricted there; it is not just a sectionwise linear map mistakenly treated as a sheaf Hom section. Universal properties are the elementary argument for existence and uniqueness.

Step 2 uses the two differential definitions, and I checked both contributions separately. The differential of the dual is minus (-1)^q times precomposition; multiplying this by the total-tensor (-1)^p gives minus (-1)^(p+q). In particular the adjacent degree a+q+1=0 is retained: replacing every unsupported value by zero too early would lose this contribution. This is the explicit argument for the no-sign assertion.

Step 3 uses the full conclusion of `lem-pc-kflat-resolution`, valid for an arbitrary ringed site and arbitrary E. The model definition explicitly says total tensor preserves K-flatness; the symmetric-monoidal statement explicitly identifies the constraints as induced on K-flat total tensors. These give exactly T,W and the named comparisons. The assertion that O is K-flat is the two-line unit calculation written in the step. No property of F,D beyond their assumed K-flatness is used.

Step 4 uses the functoriality and fixed augmentation stipulated in `def-pur-derived-internal-hom`, ordinary componentwise precomposition in `def-pur-hom-complex`, and inversion of quasi-isomorphisms in `def-weil-abstract-derived-category`. These statements give the displayed maps g_O,g_F and the invertibility of H(Qs,1). The domain of g_F is Q Hom(E,F), not QD; the step distinguishes them explicitly. Only h_O,h_F are assumed quasi-isomorphisms; I did not replace this by a global Hom-exactness assumption.

Step 5's chain calculation uses s being a chain map and the precise dual differential. The model's statement applies to K-flat D,L and a chain map into Hom(L,I(O)), and the representative-evaluation definition requires the actual projections and inverse localized augmentation. Thus its output is exactly Q(eta_O v_s) followed by the inverse fixed augmentation, not an arbitrary map representing coefficient evaluation. The section formula and uniqueness give eta_O v_s on every component.

Step 6 applies that same model with K-flat T,L and target I(F). Its hypotheses were verified in step 3; F itself need not be injective. The representative-evaluation definition states the fixed projections and the inverse augmentation used here. The b component is eta_F(y phi(sz)), with s in the correct first Hom variable. The model provides b as a chain map, so no unproved assertion of chain-level uncurrying is hidden in this step.

Step 7 compares b with eta_F c on every actual iterated pure-tensor generator and all total inclusions; the same universal-property detection from step 1 proves equality. The constraints in the cited monoidal statement are induced by the ordinary module tensor associator/unit, so they only change parentheses and multiply coefficients. I checked that no braiding is used, hence no Koszul sign appears here. Localization, as stated in the cited derived-category definition, cancels Q eta_F; it does not supply a chain inverse.

Step 8 uses the closed statement for adjunction naturality and its counit formula, and uses the model's natural tensor comparison together with the induced associator/unit constraints. I wrote the three actual comparison equations: the associator equation, naturality on v_s, and the right-unit equation. Substitution cancels precisely the D,L comparison from step 5 and yields the same Qc mu_(T,L)^(-1) as step 7. Thus both augmentation compatibilities are demonstrated rather than hidden in the word transport. All factors in these model applications are K-flat, including W and O checked in step 3.

Step 9 uses the stated bijectivity of the closed adjunction and functorial derived Hom. These allow cancellation of transposition and then H(Qs,1); no conservativity or faithfulness of localization is assumed.

For the mathematical edge cases I checked zero E or F, the zero coefficient sheaf, and a site with only zero module sheaves: all component maps and the identity reduce to the unique zero morphisms. Over the one-object site with coefficient ring Z, take zero-differential rank-one complexes with E supported in degree -q and F supported in degree p; for odd p and q the image is still y phi(x), not its negative. For nonzero differentials the calculation in step 2 verifies the neighboring a+q+1=0 case, which is the sensitive sign test. E may be unbounded; no step requires a bounded or termwise finite Hom product. The case E not K-flat is handled only by the auxiliary resolution, never excluded.

Against delivery-errors B-E: there are no new duplicate, elementary, or clause-only nodes; no new statement lacks definitions or sources; every dependency in every proof step is quoted verbatim in `citations.json`; no node's proof is cited in place of its statement. The model's non-elementary uncurrying assertion is an explicit assumption of this item, not a property inferred from a bare universal-property definition. I checked the unit route and avoided the parent duality-maps node, which already depends on this item and would be circular. All nine steps are below 2000 characters. The concrete corrections were to fill the missing proof, to replace the stale blueprint proof-paragraph locator by the actual displayed formula, and to distinguish arbitrary K-flat inputs from the flat-term subcategory when choosing the tensor comparison.
