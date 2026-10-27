# Q39: lem-zl-open-shriek-weight-preservation

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-open-shriek-weight-preservation.json`: item, statement, split; no Mathlib match. The statement and its statement dependencies are retained verbatim. Five proof steps use existing nodes only.
- `citations.json`: one entry for each of the 21 step/node citations, with verbatim statement text.
- `report.md`: this report. The search command maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is not its unit's key statement.

## Attachments

None. I searched the project `lean/WeilConjectures/` for the exact blueprint tag, mixed-weight predicates, extensionByZero, and derivedLowerShriek. `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek_of_isOpenImmersion` in `DeligneLaumon/Reduction/FormalSteps.lean:253` has a proof, but uses `nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion`, whose proof in `WeilSheaf/LowerShriekFunctoriality.lean:154-161` is `sorry`. Moreover its native `WeilComplex` interface is not the common-stage fixed-pair category locked by this item. The purity and exactness declarations in `WeilSheaf/StalkExtensionByZero.lean` do not supply both clauses of this item. The docstring mentions a mixed-weight theorem but the file actually provides punctual purity and exactness, so its docstring is not evidence of an attachment.

## WANTED

None. The item's source and the auxiliary BBD source are present locally.

## Audit and corrections

The imported item had no proof. Its statement is correct, including zero objects and repeated filtration terms; there is no statement dispute or statement change. I retained all parent searches and added the actual Q39 search queries from the command log. LeanFinder and LeanSearch returned scheme restriction and generic triangulated/homological-functor material, not a theorem about these Weil weights. Loogle and grep returned no relevant matches. Auxiliary searches for a bounded heart-test criterion were also negative; I did not manufacture such a lemma. The complex argument uses the already existing finite ordered Postnikov tower instead.

I searched the whole DAG's titles and statements for extension by zero, open exactness, heart preservation, t-exactness, shifted cohomology, and finite cohomology devissage, and used `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `extension by zero`, `t-exact`, `open-shriek-weight`, and `mixed upper weights`. The item's closest blueprint ancestor is `lem-zl-morphism-open-closed-reduction`; its existing precise `from.place` is retained and `same_as` is empty. Punctual extension is an existing stronger infrastructure statement, not a duplicate mixed-filtration theorem; finite cohomology devissage is likewise already a node. No additional node is warranted. No same-tag new/existing pairs exist.

The two assertions are proved by arguments, rather than moved into new nodes. In particular no new node restates clause (1) or (2). The proof uses exactness of the actual common-stage compact-support functor, not a discrete non-torsion etale extension or an unidentified native adic model. All geometric hypotheses of the extension lemma hold verbatim: both schemes are separated and finite type over the same finite field, and the open immersion is defined over that field. At the geometric coefficient stage this is a separated finite-type morphism between finite-type schemes, so the field compact-support triangulatedness theorem applies. No hypothesis is strengthened to an assumption on the mixed filtration or on the input complex.

## Not duplicates

No new nodes were created. Existing nodes `lem-zl-extension-by-zero-punctual`, `lem-sp-exact-functor-preserves-homology`, `lem-sfb-bounded-postnikov-extension-generation`, `lem-zl-field-shriek-lower-bound`, and `lem-zl-complex-extension` supply the needed facts and are cited directly.

## Review by Q39

I read the current main-20261015 source proof `sec-deligne-laumon-general/sk-l-dl-general-excision/lem-zl-morphism-open-closed-reduction.proof.md`, especially Part 2's assertion that extension by zero extends filtrations and preserves the complex bound. I also read the open-extension paragraphs (1) and (2) of `sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md`. For the finite cohomology argument I read BBD, *Faisceaux pervers*, PDF pages 30-33 and 35-36: the truncation adjunctions and cohomology functors in 1.3.3-1.3.6, and the successive-extension/cohomology-factor statement of 1.3.13. No new node needs a further source audit. This expanded proof is labelled agent-written because the blueprint omits details and the application of the generic finite tower is written here.

For Step 1 I opened the full statements of `def-weil-punctual-weights`, `lem-zl-extension-by-zero-punctual`, and `lem-sp-exact-functor-preserves-homology`. The first defines a finite filtration by constructible Weil subsheaves with pure quotients. The second explicitly asserts exactness on exactly the rational/common-stage Weil hearts and preservation of heart objects by the recorded derived functor. Part (a) of the third explicitly carries nested subobjects and quotient objects to their images under an exact functor. Thus every transported term embeds in the image of F, and its quotient is the image of the original pure quotient. I did not infer exactness from a definition of extension by zero or from an ordinary etale-stalk assertion.

For Step 2 the same extension lemma explicitly gives both the inside/outside coefficient fibres and local Frobenius compatibility, and explicitly concludes preservation of punctual purity. These are precisely the facts required to prove purity of each quotient, with the same residue-field cardinality. The invariance under the displayed quotient isomorphism is written as the eigenvector calculation. The mixed-weight definition then gives clause (1). Zero fibres have no nonzero eigenvectors. The empty filtration proves mixedness of zero, and a repeated term causes no need for strictness or nonzero pure quotients.

For Step 3 I checked that `prop-constructible-truncations` supplies a bounded t-structure for these common-stage coefficients and commutation with every scheme automorphism, in particular the geometric Frobenius of U. `lem-sfb-bounded-postnikov-extension-generation` gives the cohomology factors of this actual L, in their increasing order, rather than arbitrary heart factors. `lem-weil-heart-short-exact-triangles` gives functorial truncations with their adjunction characterization, which forces the canonical maps between consecutive truncations to commute with their Frobenius structures. `def-weil-complex-weights` gives the induced cohomology structure; `def-weil-weil-sheaf-complex` explicitly defines fixed pairs and warns that they need not form a triangulated category. I followed that warning: only the underlying triangles are distinguished. The first two arrows suffice for the cited weight-extension theorem, and they are equivariant.

For Step 4 I checked the complex-weight definition's exact sign: H^r(L) has bound w+r. Clause (1), already proved for all real bounds, therefore gives j!H^r(L) bound w+r. The punctual extension node says the derived compact-support functor sends heart inputs to heart outputs, not merely that its H^0 is exact. This is why its value is B[0]. `lem-zl-field-shriek-lower-bound` explicitly supplies the shift isomorphism for the recorded common-stage functor, while `prop-functor-package` states coherence and equivariance of its comparisons on these domains. The abstract identity H^s(K)=H^0(K[s]) in the heart/truncation lemma shows that B[-r] is concentrated in degree r, so its one required bound is w+r, exactly as needed. No comparison with the derived category of the heart is assumed.

For Step 5 I opened `lem-zl-complex-extension`: it requires only first two arrows of fixed pairs whose underlying arrows extend to a distinguished triangle, and gives the middle bound from the outer bounds. This exactly matches each image truncation step. I checked triangulated exactness and the shift comparison in `lem-zl-field-shriek-lower-bound`, together with the Weil compatibility in `prop-functor-package`. The induction claim, zero base, factor bound, and endpoint are all explicit. No invariant-triangle assertion about the category of fixed pairs is smuggled into the argument.

I checked B-E of `coord/delivery-errors.md` against the actual files. There are no statement-only new nodes to contain a hidden proof, no new notions to leave undefined, and no new Mathlib leaves to attach imprecisely. Every non-elementary fact used has a cited statement, not just a tag or a source paragraph. Each step/node citation has a verbatim quotation in `citations.json`; I read these statements before citing them. The generic tools from other units are declared in `split_report.tool_uses`, with why they are needed; the open-closed route of the unit is preserved. Dependency traversal found no path from the reused infrastructure back to this item. Every proof step is shorter than 2000 characters. The only inductions are the explicit finite truncation induction and the already supplied mixed filtration, and no geometric argument is hidden in either.

Small cases checked: F=0; a filtration of length zero; a repeated filtration term; j the identity; U empty; a pure sheaf placed in degree r (its complex bound is reduced by r); and a bounded complex with more than one cohomology degree. These give the same endpoint, zero cases and weight signs as the two clauses. No compiler, Lake, Lean edit, repository write, or local maintainer-check invocation was used.

## Unfinished work

None within the stage-1 split. Existing cited nodes retain their own proof obligations. Server dry-run and direct delivery are performed after writing this report.
