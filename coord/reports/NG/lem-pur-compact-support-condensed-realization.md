# Worker report: lem-pur-compact-support-condensed-realization

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-compact-support-condensed-realization.json: same statement; repaired split into seventeen ordinary-derived proof steps, not a Mathlib leaf.
- dag/nodes/sec-smooth-purity/lem-pur-ringed-coefficient-projection-cocycle.json: new statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-ringed-refinement-coefficient-square.json: new statement-only lemma, unsplit; no Mathlib match.
- citations.json: regenerated from the actual cited statements, one verbatim quotation for every step/node pair.
- report.md: this current review. report-history.md preserves the entire previous report, including its searches and superseded BLOCKED history; item-before-repair.json preserves the returned split. Searches newly run in this attempt are in searches.jsonl. repair.py and write_report.py are sandbox-only preparation files.

## Attachments

None. Searched the whole read-only slopmaster2 WeilConjectures tree for the item tag and the compact-support/condensed-realization concepts, and for both new names and coefficient-projection/refinement concepts. Read the ordinary constant-coefficient etale/pro-etale comparison in SixFunctors/ProEtale/Derived/LowerShriekComparison.lean. It has a different source and target and does not assert this completed integral/condensed comparison. The exact master composite in SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean (definition at line 268, read through line 280) is the intended open-then-proper composite. Its open preservation theorem at line 203 is sorry; it is not finished proof evidence or an attachment.

## WANTED

None. Bhatt–Scholze and the Stacks source used for this repair are present. The maintenance review path named in the prompt is absent in this shared snapshot; the complete return and explicit 2026-10-18T02:26:33Z reconciliation in the dispatch are used as the repair instruction. This is not a remaining withdrawal blocker: the dispatch explicitly supersedes it.

## Findings and corrections

The statement, coefficient categories, target ancestry and maintainer fields are unchanged. Compared the shared node against the retained sandbox: only proof and status initially differed. The initial required dry run exited 1 because citations.json was missing. The retained proof was not repaired by that run. The new split replaces its old enhanced-section-language arguments by the current ordinary unbounded derived-system statement, canonical K-flat scalar extension, separately derived proper image and the global compactification already fixed in the item. No new exceptional adjoint or infinity/dg/model-category machinery is used.

The four returned long steps were substantively repaired:

1. Original Step 2: removed the inline proof of K-flat preservation. The existing lem-sf-open-tensor-normalization states the needed derived open/coefficient comparison for arbitrary ring sheaves and ringed diagram sites. There is no need to reprove its resolution argument. Normalization and the quotient cocycle are expressly stated in def-weil-pbc-adic-coefficient-datum; new Step 2 cites that statement and transports it along b. This replaces, rather than renames, both hidden arguments.
2. Original Step 7: new Steps 6–7 cite lem-sp-finite-free-direct-image-coherence, whose statement supplies the B-linear, counit-normalized isomorphism on the whole unbounded category and its shifts. The basis/direct-sum/conservativity proof is gone from the item. Its open factor is again the existing general open theorem. Uniform-category preservation is a short use of the existing stratified-perfect characterization.
3. Original Step 8: new Step 8 is only arithmetic substitution in three existing statements: the DVR expansion, the completed quotient identification, and finite freeness of the completed scalar sheaf. Reducing an isomorphism B^d ≅ S-hat modulo t^n gives A_n^d ≅ D_n, so no separate arithmetic lemma is hidden. The false same-index finite-freeness assertion is never used. New Step 9 cites the existing finite-free cocycle; the new arbitrary-coefficient projection-cocycle node supplies the missing nonflat reduction-square version. New Steps 10–11 cite the existing arithmetic-restriction theorem, including its projection and augmentation normalization, instead of reproving a ceil-index left adjoint. The exact-product-functor/strict-limit theorem supplies finite-free tensor through the limit with exact countable products explicitly checked. New Step 12 gives the mixed integral/field square using the commuting ring square and specified adjunction counits.
4. Original Step 11: the genuinely missing refinement/coefficient square for arbitrary ring sheaves and whole systems is a new statement-only node. Finite constant-ring etale refinements already exist but do not cover completed/condensed sheaves or all system arrows. New Step 15 applies that statement before total limit, using the existing semilinear proper/open pasting and constant-tower restriction. New Step 16 handles rationalization and the coefficient colimit as functors preserving these already established equations. New Step 17 records the ordinary derived shift inputs. No long combined refinement proof remains.

Original Steps 1, 3–6 and 9–10 were also read against every cited statement and replaced/re-certified as new Steps 1, 3–7 and 13–14. All seventeen steps are below 2000 characters. The new nodes have no proof, no proof_deps, and no proof sketch embedded in their statements. They isolate generic lower-level lemmas: neither states the completed compact-support realization, the alpha isomorphism, a, the Omega comparison or the whole requested conclusion.

The mathlib_searches fields preserve the previous item searches and append the current actual searches. Both new nodes record leanfinder, loogle, grep and leansearch, plus a second semantic phrasing. The log is the msearch.py output, not reconstructed service calls. Read the returned signatures and the relevant local source in Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean and PullbackContinuous.lean: pushforwardComp, pullbackComp, pullback_assoc and conjugateEquiv_pullbackComp_inv concern underived module functors. They do not state the ordinary unbounded derived coefficient mate or the clopen-refinement square. The other hits are presentations/free sheaf naturality, general site sheafification, ring topology or discrete/solid condensed modules; none specializes in one line to either new statement. No Mathlib leaf is claimed.

## Not duplicates

Searched the whole DAG and whole imported blueprint for K-flat/open tensor, normalized reductions, subsequence, finite free coefficient, coefficient projection/cocycle, refinement coefficient, clopen and compact-support realization. Reused the existing open, arithmetic, finite-free and semilinear-refinement statements. blueprint_refs.py ancestor returns None on this seeded target chain; both new nodes retain that ancestor with the full via chain and an explicit place in sk-thm-purity-transport Steps 2–3. The item is not a unit key node; no unit record is edited.

lem-pur-ringed-coefficient-projection-cocycle vs lem-sp-finite-free-direct-image-coherence: the existing node gives the isomorphism and cocycle for finite free coefficient sheaves on scheme pro-etale sites. The new node gives only an identity of possibly noninvertible maps for arbitrary coefficient homomorphisms and on ringed diagram topoi; it is needed for the nonflat quotient square. The existing finite-free theorem is cited for invertibility, not recreated.

lem-pur-ringed-coefficient-projection-cocycle vs lem-weil-pbc-mate-pasting: generic mate pasting is reused as the categorical input; the new statement fixes the derived ring-sheaf coefficient functors, balanced scalar associators, and commutative coefficient-square identity. Constructing these simultaneous ringed-diagram comparisons is not supplied by an abstract notation-only specialization.

lem-pur-ringed-refinement-coefficient-square vs lem-sp-refinement-coefficient-mate: the existing scalar square is on bounded-below etale inputs for finite constant rings, with a site-transport clause for finite coefficients. The new square uses arbitrary ring sheaves on pro-etale and ringed diagram topoi and has no boundedness condition.

lem-pur-ringed-refinement-coefficient-square vs lem-sf-proper-open-coefficient-refinement: the existing theorem is finite constant-coefficient, bounded-below and etale. It cannot be applied to B-hat -> E^c or to an equality of whole system maps.

lem-pur-ringed-refinement-coefficient-square vs lem-sf-semilinear-proper-open-mate-pasting: that node gives the clopen-normalized geometric comparison, restriction to constant towers and the pasting equations for a fixed ring system. It gives no coefficient-change square. We cite its pasting theorem and isolate only the additional square.

lem-pur-ringed-refinement-coefficient-square vs lem-sf-proper-open-tensor-compatibility: that theorem is fixed finite-field/finite-ring or its particular quotient-system setting, and treats the tensor projection formula with an object in that fixed coefficient category. The new coefficient-change square is B-linear in arbitrary sheaf coefficients and whole ringed diagram categories.

lem-pur-ringed-coefficient-projection-cocycle vs lem-sfb-proper-open-tower-derived-unit: the existing statement, “Derived-unit resolution calculation in a proper/open tower”, concerns the resolutions and units for composing geometric proper/open functors; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-sfb-ringed-comparison-tensor-adjunction: the existing statement, “Tensor and adjunction compatibility of canonical ringed-topos path comparisons”, concerns monoidality and counits of an invertible comparison between two factorizations of one ringed-topos morphism; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-sfb-ringed-kunneth-factorizations: the existing statement, “Two factorizations of the ringed-topos external product comparison”, concerns two Kunneth projection/exchange composites; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-sfb-derived-composition-adjunction-normalization: the existing statement, “Derived composition preserves the specified adjunction normalization”, concerns normalization of right-derived composition for exact left adjoints; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-sfb-ringed-derived-monoidal-comparisons: the existing statement, “Monoidal and adjunction normalization of derived ringed-topos comparisons”, concerns monoidal derived pullback composition and its right-adjoint conjugate; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: the existing statement, “Canonical composition comparison for unbounded ringed-topos direct images”, concerns composition isomorphisms of two derived direct images; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing statement, “Derived adjunctions under compatible changes of ring sheaves”, concerns coefficient restriction, its conservativity and compatibility with a single adjunct; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs def-weil-pbc-derived-direct-image-composition: the existing statement, “Composition isomorphisms of derived direct images (conjugates of those of inverse images)”, concerns the definition of the bounded-below etale direct-image compositor; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs def-weil-pbc-adjunction-conjugate: the existing statement, “Conjugate transformations of adjoint functors”, concerns the definition and general identities for conjugate adjunction transformations; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-weil-pbc-frobenius-exchange-restriction: the existing statement, “Finite-level exchange is the restricted ambient exchange”, concerns coefficient restriction of geometric Frobenius exchange maps; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-sp-restriction-transition-transpose: the existing statement, “Scalar-adjunction transpose of a compact-support mixed-coefficient map”, concerns the transpose of compact-support transitions for finite constant coefficients and finite-Tor constructs; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-kun-module-abelian-kinjective-direct-image-acyclic: the existing statement, “Abelian direct-image acyclicity of a module K-injective complex”, concerns acyclicity of a forgotten-coefficient K-injective resolution under etale direct image; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-sf-compact-support-restriction-of-scalars: the existing statement, “Finite-level compact-support direct image commutes with restriction of scalars”, concerns restriction of finite constant coefficients for a compactification composite; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-pur-ringed-coefficient-restriction-counit: the existing statement, “Derived ringed-topos counit under coefficient restriction”, concerns the scalar-unit equation for restriction of a ringed adjunction counit to a constant coefficient ring; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-cbc-etale-derived-direct-image-coherence: the existing statement, “Ordinary etale derived direct-image composition and its coherence”, concerns associativity of bounded-below etale geometric direct-image composition; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-kun-etale-module-abelian-ringed-presentation: the existing statement, “Simultaneous ringed presentations of coefficient forgetting and abelian etale direct image”, concerns underived presentation of module and abelian sheaf categories as ringed topoi; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-asd-proper-finite-coefficient-extension: the existing statement, “Canonical unbounded proper direct-image comparison for finite coefficient extension”, concerns invertibility of a single proper scalar comparison for finite constant rings on etale sites; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-weil-proetale-direct-image-restriction-of-scalars: the existing statement, “Derived pro-etale direct image commutes with restriction of scalars”, concerns restriction, not extension, of finite constant coefficient rings through direct image; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

lem-pur-ringed-coefficient-projection-cocycle vs lem-pur-completed-coefficient-pushforward-comparison: the existing statement, “Completed-coefficient pushforward restriction and strict reduction towers”, concerns restriction to constant coefficients and completed direct-image reconstruction; the new statement is the transitivity/commutative-square equation for possibly noninvertible derived coefficient-extension mates, including arbitrary ringed diagram coefficients.

## Unfinished work

The two new lemmas are intentionally statement-only obligations for the next DAG level. This is not a claim that their Lean proofs, or those of the existing inputs, are completed. All requested one-level repairs have been written; server validation is recorded below when completed.

## Review by NG

I read the retained node and all its direct dependency statements, then read each additional cited statement in the revised split. The source for the item is Bhatt–Scholze 6.7.2 (proper image preserves completed constructibility), 6.7.6–6.7.8 (the compactification composite is separately derived and its independence is not a derived-underived-composite assertion), 6.7.14 and 6.7.16–6.7.17 (coefficient projection), and 6.8.14–6.8.15 (integral/rational/field transport). I read these passages in the PDF text in the sandbox. They motivate this assembly; the paper does not literally prove the archived condensed category comparison, which is a named existing DAG input. I checked the current master definition against the item rather than identifying different coefficient categories by notation.

For the projection-cocycle child, I read Stacks sites-cohomology.tex Tag 0D6E, lemma-derived-pushforward-composition and its following remark-base-change, and the statements of mate pasting, successive derived quotient normalization and the current ordinary semilinear theorem. The new child is explicitly an agent supplement: its identity follows by taking the two ordinary adjunction transposes of scalar extension of the same counit, using the K-flat balancing associator, and then applying the pasting identity. No noninvertible mate is turned into an isomorphism. For the refinement-square child, I read Bhatt–Scholze 6.7.6–6.7.7 and the actual clopen-section formulas in the existing strict-tower and semilinear proper/open statements, together with the finite-coefficient refinement nodes. The new child isolates the coefficient square: open base change is normalized by the unit, scalar extension preserves identity/zero on the clopen decomposition, and transposing this equality gives the displayed B-linear refinement equation. These are generic ordinary derived facts below the item; neither is claimed verbatim in the cited human source. I also read Stacks Tags 0941 (lemma-derived-limit-is-ok) and 0A07 (lemma-Rf-commutes-with-Rlim) to check that the limit comparisons in this repair are those of actual diagram-derived functors.

I checked the hypotheses where they are used. Step 1 verifies noetherianity, finite dimension, invertibility of ell and quasi-compactness of the open, including for its identity-proper compactification. It now explicitly cites finiteness and perfectness of the DVR quotients; these were previously left implicit. Steps 2–3 use completeness only after uniform restriction has supplied it. The current ordinary-system theorem is used solely for derived tensor, exact open extension, proper image, units/counits and mate words; its cartesian-first-input internal-Hom clause is unused. Step 7 uses the stratified-perfect characterization with precisely the completed ring sheaf and compatible witnesses in the item. Steps 8–11 keep v-adic levels en distinct from same-index n, use the canonical completed quotients, and check exact products for the limit/scalar comparison. Step 13 checks one common lower bound for the filtered diagram and proper => qcqs for g; no unbounded-continuity assertion or full continuous Omega-function sheaf is substituted. Step 15 checks bounded-below etale-origin witnesses before using invertibility of the constant-tower refinement mate.

For clarity, the following is my step-by-step reading, with the complete list of statement citations below each entry. The verbatim statements in citations.json certify which assertions were read; they do not replace the mathematical scope checks here.

1. The finiteness statements give the geometric hypotheses, the standard-quotient statement gives finite perfect P_n, and uniform restriction applies to both c and the open with identity proper part. Coefficient inverse image includes its quotient compatibility.

Cited statements: `lem-weil-pbc-finite-type-over-noetherian`, `lem-kun-dimension-finite-type`, `lem-weil-pbc-profinite-coefficient-inverse-image`, `lem-weil-pbc-standard-quotients-perfect`, `lem-cbc-integral-compact-support-uniform-restriction`.

2. Direct-image-limits states both invertibility and the actual derived-diagram projection map; open normalization explicitly covers arbitrary ring changes on diagram topoi. The adic datum explicitly states normalization and its quotient cocycle. The only elementary inference is transporting transition isomorphisms across b.

Cited statements: `lem-coef-semilinear-derived-sections`, `prop-weil-pbc-direct-image-limits`, `lem-sf-open-tensor-normalization`, `lem-weil-pbc-ring-sheaf-change-adjunction`, `def-weil-pbc-adic-coefficient-datum`.

3. The strict tower node defines the same sequence of functors, and the completed-coefficient comparison explicitly includes strict-diagram coefficient restriction. The evaluation-calculus counit is the actual projection adjunct. Completeness makes its unit invertible, and the triangle identity proves alpha R(q)=b. Exactness and R-linearity use the specified functors, not chosen cones.

Cited statements: `lem-weil-compact-support-reduction-tower-functor`, `lem-coef-semilinear-derived-sections`, `lem-pur-completed-coefficient-pushforward-comparison`, `lem-coef-derived-system-evaluation-calculus`, `lem-weil-pbc-constant-completion-equivalence`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.

4. The open theorem is specialized to identity scheme map with B -> E^c. Its normalized adjunct is exactly the required scalar/open map. Rational transport extends supplied data; the realization statement says J is that scalar functor and essentially surjective, giving preservation.

Cited statements: `lem-sf-open-tensor-normalization`, `prop-weil-pbc-rational-transport`, `lem-weil-pbc-condensed-e-realization`, `def-weil-pbc-condensed-e-module-category`.

5. The direct-image clause of the realization node includes counits for g; substituting Step 4 and q inverse gives the displayed a. Uniform output plus essential surjectivity gives preservation of the actual ambient composite.

Cited statements: `lem-weil-pbc-condensed-e-realization`, `prop-weil-pbc-rational-transport`.

6. Condensed flat calculus supplies finite freeness, the coefficient category supplies inverse-image identifications, and finite-free direct-image coherence states the precise B-linear isomorphism with its counit normalization. The open theorem supplies its other factor.

Cited statements: `lem-weil-pbc-condensed-flat-coefficient-calculus`, `def-weil-pbc-condensed-e-module-category`, `lem-sp-finite-free-direct-image-coherence`, `lem-sf-open-tensor-normalization`.

7. Completed-scalar comparison gives chi and completeness, not merely some scalar isomorphism. The perfect-model characterization gives uniform-category preservation. Finite-free direct-image coherence and open normalization now supply d; conjugation with q and chi defines the claimed scalar comparison.

Cited statements: `lem-weil-finite-free-completed-scalar-comparison`, `lem-weil-pbc-integral-stratified-perfect-characterization`, `lem-weil-pbc-profinite-coefficient-inverse-image`, `lem-sp-finite-free-direct-image-coherence`, `lem-sf-open-tensor-normalization`, `lem-sfb-successive-derived-quotient-normalization`.

8. This step only substitutes the DVR expansion in the existing quotient theorem and reduces a finite-free module isomorphism. I checked that t is a nonunit in S by the coefficient-definition statement. Associativity is the stated balancing isomorphism. The step is elementary relative to these citations and creates no duplicate arithmetic node.

Cited statements: `def-weil-integral-scalar-extension`, `def-weil-l-adic-coefficient-extension`, `lem-weil-pbc-constant-completion-equivalence`, `lem-weil-finite-free-completed-scalar-comparison`, `lem-sfb-successive-derived-quotient-normalization`.

9. The finite-free direct-image theorem explicitly gives its tower equation. The new arbitrary-map cocycle is needed where the reduction map is not flat. The open factor is the unit-normalized adjunct; its cocycle follows from balanced associativity and the cited mate-pasting equation.

Cited statements: `lem-sp-finite-free-direct-image-coherence`, `lem-pur-ringed-coefficient-projection-cocycle`, `lem-sf-open-tensor-normalization`, `lem-sfb-successive-derived-quotient-normalization`, `lem-weil-pbc-mate-pasting`.

10. The new cocycle gives the commuting coefficient-square identity on the ordinary ringed diagram topos itself. Open normalization is on that same diagram topos. Consequently the b/d square includes every transition and is not deduced by evaluating.

Cited statements: `lem-pur-ringed-coefficient-projection-cocycle`, `lem-sf-open-tensor-normalization`, `lem-sfb-successive-derived-quotient-normalization`, `lem-weil-pbc-mate-pasting`, `lem-coef-semilinear-derived-sections`, `lem-weil-pbc-diagram-site-realization`.

11. Arithmetic restriction explicitly preserves projections and strict augmentations. Exact products hold in both pro-etale module categories, and finite free tensor preserves their products; thus the exact-product/strict-limit theorem applies. The chi statement defines its unit by these quotient augmentations. Applying these functors to the previous square and using the unit/counit identity gives the alpha square.

Cited statements: `lem-sp-strict-tower-arithmetic-restriction`, `lem-weil-proetale-countable-products-exact`, `lem-cbc-exact-product-functor-strict-limit`, `lem-weil-finite-free-completed-scalar-comparison`, `lem-coef-derived-system-evaluation-calculus`, `lem-pur-ringed-coefficient-projection-cocycle`.

12. Continuous coefficient realization explicitly says the integral-to-field square commutes. J preserves proper adjunction counits, so the new cocycle and open normalization compare exactly the constituents of a. Rational transport preserves the assembled equation.

Cited statements: `lem-weil-pbc-continuous-coefficient-realizations`, `lem-pur-ringed-coefficient-projection-cocycle`, `lem-weil-pbc-condensed-e-realization`, `lem-sf-open-tensor-normalization`, `prop-weil-pbc-rational-transport`.

13. The presentation node provides actual bounded-below complexes and identifies cocone maps under scalar transposes. Flat coefficient extension and exact open extension keep a common lower bound. The qcqs continuity statement and conservative proper-image coefficient restriction therefore apply exactly as stated.

Cited statements: `lem-weil-pbc-condensed-coefficient-complex-presentation`, `lem-weil-pbc-condensed-flat-coefficient-calculus`, `lem-pur-site-restriction-module-adjunction-exact`, `lem-weil-pbc-condensed-qcqs-pushforward-continuity`, `lem-weil-pbc-ring-sheaf-change-adjunction`.

14. The two-colimit node states object descent, morphism descent and eventual equality, as well as scalar preservation. These give preservation at Omega and independence of the chosen finite presentation. The arbitrary-ring cocycle already permits the terminal coefficient ring Omega^c.

Cited statements: `prop-weil-pbc-qbar-condensed-two-colimit`, `lem-pur-ringed-coefficient-projection-cocycle`, `lem-weil-pbc-condensed-flat-coefficient-calculus`.

15. The semilinear proper/open theorem states the clopen-refinement map and its pasting identities before evaluation, and identifies constant tower restriction. The constant-tower theorem gives its invertibility on the witnessed finite inputs. Apply Rg_2 to the new arbitrary-ring refinement square; the ringed-derived monoidal comparison explicitly identifies the direct-image composition with the composite adjunction. Its counit equation, the coefficient cocycle and mate pasting identify this square with the b square. These statements apply equally on the ordinary ringed diagram topos. Unit/counit naturality then gives q and alpha.

Cited statements: `lem-sf-semilinear-proper-open-mate-pasting`, `lem-cbc-strict-tower-proper-open-calculus`, `def-weil-pbc-bounded-constructible-complete`, `lem-coef-semilinear-derived-sections`, `lem-pur-ringed-refinement-coefficient-square`, `lem-pur-ringed-coefficient-projection-cocycle`, `lem-sfb-ringed-derived-monoidal-comparisons`, `lem-weil-pbc-mate-pasting`, `lem-weil-pbc-constant-completion-equivalence`, `lem-coef-derived-system-evaluation-calculus`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`.

16. The new refinement child applies to completed and condensed coefficient sheaves, unlike its finite-constant predecessors. It gives the primitive square; the J counit comparison, rationalization and finite-stage colimit transport that established equality. The remaining pasting equation is already the statement of the semilinear proper/open theorem.

Cited statements: `lem-pur-ringed-refinement-coefficient-square`, `lem-weil-pbc-condensed-e-realization`, `prop-weil-pbc-rational-transport`, `lem-sf-semilinear-proper-open-mate-pasting`, `lem-pur-ringed-coefficient-projection-cocycle`.

17. The ordinary derived-adjunction shift theorem includes all integer-shift unit/counit equations, and the projection theorems include their shift structure. Exact open extension is degreewise; its identity/zero component maps are unchanged by shift. Exact total limit, rational transport and bounded-below continuity preserve the stated structures.

Cited statements: `lem-weil-pbc-derived-adjunction-shift`, `lem-weil-pbc-ringed-projection-mate-exact`, `lem-sp-finite-free-direct-image-coherence`, `lem-sf-exact-functor-derived-triangulated`, `lem-pur-ringed-coefficient-projection-cocycle`, `lem-pur-ringed-refinement-coefficient-square`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, `prop-weil-pbc-rational-transport`, `lem-weil-pbc-condensed-qcqs-pushforward-continuity`.

I tested the small cases rather than adding hypotheses to force invertibility. With u the identity, the new coefficient cocycle reduces to the balancing map and identity counit. With identity coefficient maps it gives the identity comparison; with a nonflat quotient Z/ell^2 -> Z/ell its assertion remains an equality and makes no false flatness/isomorphism claim. For a refinement with u and the opens identities the new square is the identity; with the empty open all terms are zero. For an actual extra boundary component the clopen projection is zero on that component and identity on the section, on both routes. The definition is therefore the normalized section projection and not an unjustified claim that the refinement square is cartesian. Ramification e=1 is the unchanged index case; for e=2, n=1 the quotient is S/v^2, not S/v. Zero complexes, shifts and identity field extensions preserve all the displayed formulas. The one-point/constant-ring cases agree with the elementary balanced tensors and with the cited finite-free theorem.

Checked B–E against these files: both new statements introduce their own sites/schemes/rings and domains, cite definitions of their notions and the actual source place, carry only statements, and have real logged searches. They do not duplicate the cited narrower finite-ring lemmas or state a clause of the realization item. Each non-elementary fact taken by the proof is now a statement citation; all citations were re-read, with the nonflat, small-index, uniform-witness and coefficient-category hypotheses checked above. No statement change or dispute was needed. The old signature in report-history.md is not used as certification of this repair.

## Validation

The required initial retained-split dry run exited 1 with missing citations.json; nothing was pushed. The repaired packet passed the server split review, which recognized the new tool-use declarations. Its full server preflight identified one formatting failure: Step 10's TeX array row separator next to a command was read as a doubled command escape. I replaced the array with the two coefficient paths, keeping the same square. The route findings are advisories, and the generic tool declarations include their mathematical purpose. After the final refinement-composition clarification, citations.json contains 92 verbatim entries, covering every proof citation. The required deliver.py dry run and push run the final server checks; their results are not presumed in this report.
