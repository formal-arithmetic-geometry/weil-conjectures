# Stage-1 delivery: lem-route-sp-qbar-twist-action-exists-unique

## Files written

- dag/nodes/sec-smooth-purity/lem-route-sp-qbar-twist-action-exists-unique.json: item, split; no exact Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-rational-twist-transition-semilinear.json: one new statement-only node, unsplit; no exact Mathlib match.
- citations.json: verbatim statement extracts for every proof-step citation.

## Attachments

No finished project declaration states the item. Searches of lean/WeilConjectures for the blueprint tag and spQbarTwist/spRationalTwist found none. The exact project declaration AlgebraicGeometry.ProEtale.spQbarTwistAction_existsUnique in lean/Sheaf/Paper/ProEtaleTateTwists.lean:416 has sorry. AlgebraicGeometry.ProEtale.spRationalTwistMap_semilinear belongs to the new lem-sp-rational-twist-transition-semilinear node: same file, lines 376–390, theorem line 383; it too has sorry, so this is an identification of an open obligation, not a finished attachment. No Lean was written or compiled.

## WANTED

None. The current blueprint, cited node statements, and exact Lean definitions/docstrings are present locally. The proof is marked agent-written because the blueprint and its expanded categorical assembly are agent-written.

## Issues corrected

The provisional item put a proof sketch and Lean signature inside its statement, with no statement dependencies or proof. I replaced these with a self-contained natural-language statement, retaining exactly the Lean hypotheses: prime ell and arbitrary scheme X. The surrounding Tate-twist blueprint assumes ell invertible to establish local freeness, but the action construction itself does not. I did not cite that stronger-hypothesis theorem as though it supplied the arbitrary-scheme construction. Instead the actual positive-index B tensor_Z roots limits and rational balanced tensors are introduced explicitly. The index n>=1 corresponds to Lean's n+1. Neither a comparison with constant coefficients nor an invertibility/local-freeness theorem is used. The source, Lean record, import fields, chapter and unit of the existing item are retained.

The upstream docstring's phrase “the coefficient colimit is p_X^* Qbar” is justified by an underlying-abelian-sheaf colimit at the point and the left-adjoint preservation theorem, with exactly the published cocone. It is not the full continuous-function condensed algebraic closure, nor a discrete constant field. Existence and uniqueness of the action use tensor-colimit preservation in two variables and the full family of mixed tensor legs. This avoids assuming that arbitrary sheaf-colimit sections have global stage representatives, and avoids citing the diagonal hom-ext lemma for two different diagrams (its statement only handles X tensor X).

## Not duplicates

lem-sp-rational-twist-transition-semilinear vs sk-def-sp-tate-twist: the latter constructs all twists on schemes where ell is invertible; this theorem is the specific action-intertwining equality for the actual normalized transitions on an arbitrary scheme, before taking any closure colimit. The existing definition's prose about semilinearity is not an arbitrary-scheme theorem with the specified Lean maps.
lem-sp-rational-twist-transition-semilinear vs lem-route-sp-rational-twist-map-exists-unique: the existing node pins the transition by a balanced-tensor normalization; the new statement proves that this abelian-sheaf map intertwines the two module actions. The existing statement does not assert that equality.
lem-sp-rational-twist-transition-semilinear vs lem-weil-qbar-twist-common-stage: that node concerns twist functors in a common-stage derived category with scalar comparison isomorphisms; the new node concerns one abelian-sheaf morphism between actual pulled-back condensed-coefficient twists.
lem-sp-rational-twist-transition-semilinear vs lem-route-sp-qbar-twist-action-exists-unique: the new node concerns finite-field transitions only; it neither constructs an algebraic-closure action nor asserts any existence/uniqueness clause of the item.

DAG searches used the declaration name, semilinear/colimit/twist keywords, common-stage terms, and all matching coefficient nodes. Blueprint searches were “Tate twist”, “filtered colimit”, “scalar action”, “semilinear”, “rational twist”, and “semilinear transition”; the last two found no imported node. All matching statements were inspected before writing the new node. No new Stacks source/tag is assigned: the specialized new fact is sourced to the blueprint construction and the exact Lean docstring, not an unrelated Stacks theorem.

## Review by NP

I read the chapter and unit records, the current latest blueprint sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md and its coefficient-twist detail, and the current Cartesian-coefficient proof, especially “Rational and algebraic closure”. I also read the current coefficient-colimit proof and point-colimit proof and the sheaf tensor-structure source. The current snapshot is main-20261025 (b767183f5ce5f281d407f582da76ab91d6176fe0); latest paths are used throughout. For the new node I read the integral finite levels, the limit, the balanced rational extension, and the normalization, identity, composition and semilinearity declarations in ProEtaleTateTwists.lean. Semilinearity is a genuine comparison of the finite-root inverse-limit action with the rational tensor quotient, not the existence/uniqueness claim being split. It remains statement-only as required.

For Step 1 I opened the finite-compositum theorem and checked its nonempty directed conclusion, both actual transition-law statements, the new action-intertwining statement, and the general-site abelian-colimit theorem. These give precisely directedness, functoriality, semilinearity and existence of Q; exactness, which the last theorem also asserts, is not used. The chosen universe contains the algebraic closure and a small site skeleton, so the colimit is small. No hypothesis that ell is invertible is used here or anywhere else.

For Step 2 I opened the point-abelian-colimit theorem: it names exactly continuous functions with values in one finite subextension and the actual cocone legs. The inverse-image node explicitly says p_X^* is left adjoint; the preservation theorem applies to this small point diagram. The cocone definition identifies every pulled-back leg. I checked that the two point inclusion definitions assert strict composition and compatibility with the closure inclusions, and that the pulled-back-coefficient definition gives functorial ring-object structures. This justifies multiplication and unit compatibility, not just a bare additive comparison.

For Step 3 I checked the exact equality asserted by the new semilinearity node against both factors in b_{E,F}^H. Its application is at H subset K, with input i_{E,H} tensor j_{F,H}; rational and coefficient composition give the displayed equality. Cocone compatibility cancels no monomorphism. A finite compositum compares any two upper fields. The same formula with a common upper bound checks naturality in both E and F. No black-box assertion of independence is left unexplained.

For Step 4 the tensor node's second clause says that both tensor variables preserve colimits, for abelian sheaves on an essentially small site. Its domain matches this site and these coefficients. I use it first for E_X tensor -, then for - tensor Q, and invoke exactly the universal property in the colimit-definition statement. This constructs an abelian-sheaf morphism and proves mixed-leg equality detection. The two functors and endpoints are written out, so the diagonal tensor hom-ext node (a tempting but inapplicable citation) is unnecessary.

For Step 5 the module-object definition gives exactly the unitor and associator equations required. Tensor-colimit preservation yields the three-variable equality test by successive descents; the common-field action reduces to the existing M_H module axiom. The actual coefficient maps preserve products and units as verified in Step 2. The unit check uses F=F and the recorded identity transition. The displayed calculations are checks of these two axioms, not new theorem-sized claims.

For Step 6 I tested both actions after every mixed tensor leg, using the full quantified formula with a common upper field. Step 4 gives equality of action maps, and the module-object definition says that the remaining fields are proofs of the two laws, so equality of structures follows. In particular uniqueness is not inferred from existence of a ring-colimit structure or from uniqueness of a bare abelian colimit.

I checked edge cases: X empty, X in characteristic ell (root sheaves can be trivial and no claim of rank one is made), ell=2, bottom field Q_ell, E=F=H, proper and ramified finite inclusions, and replacing either common upper field by a larger one. There is no injectivity assumption on the twist transitions or coprojections. Both abelian/sheaf tensor products and all module-object associators have the same typing as the Lean signature. Every step is below 2000 characters; no long step hides a separate comparison or a “standard” lemma. All non-elementary claims cited in the proof have literal statement extracts in citations.json. All Mathlib searches recorded were actually run by msearch.py and their hits were read. Fixed-ring colimit modules and bimodule tensor constructions do not match; ModuleCat/Stalk.lean also constructs varying-ring module structures for ordinary groups, but it does not give the sheafified Tate diagram or prescribed coefficient identification in one specialization. No existing Mathlib result found states the new semilinearity comparison.

The possible proof of the new node for its future worker is already in the read Lean docstring: test the integral action equality on each finite projection, where the map is coefficient inclusion tensor identity; then use the rational normalization on the prequotient and the epimorphic balanced-tensor projection. This is retained here as guidance, not placed in the new node's statement or proof.

## Unfinished work

None for this one-level stage-1 split. The new semilinearity statement is deliberately left unsplit for a later worker. Stage 2/3 work is outside this delivery.

## Validation

The required remote dry run exited successfully: OK (not pushed), commit f5b9613fcc2, server preflight passed. The final report corrects the theorem line to 416. The next dry run found stale quotes for two concurrently updated live transition nodes (identity and composition). I read both new statements in full: their hypotheses are still arbitrary X and their specified maps use exactly the same positive-index limits and balanced-tensor normalizations, so the proof applications remain valid. I refreshed the verbatim conclusion extracts in citations.json and repeated the dry run for the final package before pushing. No local DAG/preflight check or compiler has been run.
