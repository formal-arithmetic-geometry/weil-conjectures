# Stage-1 repair: det-thm-sf-pf-adic-projection

## Files written

- dag/nodes/sec-six-functors-basics/det-thm-sf-pf-adic-projection.json: statement, repaired split; nine steps, preserving the statement and steps 1–6,8–9.
- dag/nodes/sec-six-functors-basics/lem-sfb-section-module-derived-operations.json: new statement-only lemma; no Mathlib match after the retained two LeanFinder phrasings, LeanSearch, Loogle and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-projection-first-shift.json: new statement-only lemma; no Mathlib match after the retained two LeanFinder phrasings, LeanSearch, Loogle and source grep.
- citations.json: every step/node citation is backed by the verbatim complete statement, including the new nodes.
- report.md: this repair and review. The retained searches.jsonl and earlier scratch scripts are kept; scratch scripts are not delivery files.

Two new nodes, zero Mathlib leaves. Only sandbox files are written. No Lean, compiler, Lake, direct git command, live project edit, launcher edit, or subagent is used.

## Attachments

None. Searching the exact blueprint tag and the integral projection and shift notions in /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no declaration stating the complete item. AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral, SixFunctors/Etale/Derived/ProjectionFormula/Integral.lean:172, has extra completeness/Tor hypotheses, discrete étale coefficients, and uses the explicitly sorried inputs at lines 94–153. The pro-étale version, SixFunctors/ProEtale/Derived/ProjectionFormula.lean:339, also requires étale-origin witnesses. Neither states tensor closure and extension to all localizing objects. CategoryTheory.Adjunction.commShift_rightAdjointProjectionMap_app, CategoryTheory/Adjunction/ProjectionMapShift.lean:44, concerns shifts of the second input under supplied comparison-shift hypotheses. It does not state the new first-input ringed derived assertion or the section-module comparison. No upstream master sorry is treated as a completed proof.

## WANTED

None. All blueprint and Stacks sources used are available locally.

## Return and corrections

The dedicated return asks for the hidden lemmas in step 7 (2193 characters) to be extracted, retaining the statement and the other steps. I continued the retained sandbox repair. The only changed proof step is 7, now citing (a) the derived monoidal/adjunction comparison between internal and section-ring modules, and (b) shift compatibility of the ringed projection mate in its first input. The existing ringed-projection-mate-exact already states the second-input assertion, so no duplicate is created for it. Neither new statement asserts invertibility of a projection formula or closure of a constructible/localizing category; neither restates an item clause. The tensor-closure and two generator-extension arguments remain in the item.

The shared node already includes the earlier accepted NW split and its review. Its statement, Lean/audit records, historical blueprint/import fields, and maintainer metadata are retained. The current main-20261015 unit source is in sec-six-functors-basics and concerns the integral localizing formula; dag/units/sk-thm-sf-pf-adic.json is still bound to the older master derived-complete tower statement. This existing metadata discrepancy is reported, not edited. This detail is not the unit's key node, so no unit realization is delivered.

## Source error retained from the original split

The blueprint calls Tag 099I derived Nakayama, but the tag table identifies algebraization.tex, lemma-restriction-derived-complete-equivalence: an equivalence after flat scalar change, not the vanishing criterion. The existing det-thm-sfb-proper-base-change-integral(2) states the criterion, and its clause (3) supplies the bounded formula used here. The item statement is unchanged; no new STATEMENT-DISPUTED correction is needed. Tag 0F0G is the torsion étale proper projection formula, not a condensed integral comparison. This repair does not apply it directly across coefficient conventions.

## Unfinished work

The two new nodes deliberately remain unsplit statement-only obligations. The one-level repair is complete subject to the required server dry run and push. The maintainer independently reviews the delivery. No new theorem is marked proved or Mathlib-closed.

## Review by Q99

I read the dispatched brief, coord/brief-stage1.md, delivery-errors B–E in full, stages/1-dag.md, SETUP's three levels, GOAL.md and coord/dag-sync.md, the chapter and unit records, and the current main-20261015 item, proof, and enclosing unit. I compared the sandbox against the current shared item: the mathematical statement is byte-for-byte unchanged; only step 7, its dependency union, status and split report differ. There was no report.md in the retained sandbox and no running delivery command, so there was no prior finished report/dry run to supersede. The previous search log was read and reused rather than repeated.

For step 1 I opened lem-weil-pbc-qcqs-over-affine, det-def-localizing-closure-ctf-equals-bc and det-def-localizing-closure-existence. Their statements give separated finite-type implies qcqs, the integral equality Dctf=Dbc, and ambient sums plus minimality. The field is affine and the finite extension coefficient is listed; fullness proves that ambient coproducts remain coproducts in the full subcategory.

Step 2 uses exactly clause (3) of det-thm-sfb-proper-base-change-integral: proper p, standing schemes, finite E and bounded constructible inputs. These are exactly our hypotheses and coefficient category. It proves only the existing bounded clause, leaving the localizing extension to the item's later steps.

For step 3 I read sk-def-sfb-derived-tensor-hom, def-pc-tensor-complex-sheaves, def-pc-kflat-complex and def-weil-abstract-derived-category. The cone and shift identities are direct signed-total-complex calculations and the displayed Hom identities are the adjunction and coproduct universal properties. They work for unbounded complexes because total tensor uses sums. The independent section-ring equivalence now has an explicit lemma in step 7, so the comparison needed to use the sheaf-complex formulas is not hidden. No global coproduct assertion about Rp_* is taken from tensor closedness.

For steps 4–5 I checked sk-lem-int-tensor's actual uncompleted integral tensor clause and det-def-localizing-closure-existence(2), which permits an arbitrary class of generators. Exactness and sum preservation from step 3 make the preimage subcategories localizing. First B is bounded and A arbitrary localizing, then A is fixed arbitrary and B arbitrary. This order is essential; no boundedness of arbitrary localizing objects is assumed. These are short arguments from minimality, so no new nodes are created for them.

For step 6 I read det-proper-base-change-unbounded-pullback and det-proper-image-localizing-proper. The latter expressly supplies both conditional hypotheses for O_E in our standing geometry, not only a conditional restriction statement. After step 1 identifies the generators, pullback and proper pushforward restrict to the specified closures and preserve their ambient sums. Tensor closure keeps their arguments in that domain. No preservation of all ambient sums by proper pushforward is asserted.

Step 7 now uses the full comparison statement of lem-sfb-section-module-derived-operations: exact symmetric monoidal equivalences, comparison of both derived functors, the unit/counit, and the pullback tensor comparison, over the same section-ring coefficient. It uses clause (iii) of lem-weil-pbc-adjunction-shift-compatibility-unique for the compatible shifts and lem-sf-triangulated-right-adjoint with exact U. The ringed projection-mate node expressly supplies exactness and shift compatibility in L. The new lem-sfb-ringed-projection-first-shift supplies exactly the missing K-variable equation. Exact equivalences carry both identities to module objects and full triangulated subcategories inherit them; this does not identify condensed coefficients with discrete constants. All sites have small representatives in the fixed coefficient universe.

For steps 8–9 I opened sk-lem-sf-determination and checked all its hypotheses: the coefficient is admissible, the domain/codomain are localizing Dctf categories via step 1, the functors preserve sums and triangles by steps 3,6, and step 7 is about the actual canonical transformation. Step 8 fixes bounded L, with invertibility on all bounded K supplied by step 2. Step 9 fixes arbitrary localizing K, with the bounded L case supplied by step 8; the source and target schemes in this second determination application are both Y.

For lem-sfb-section-module-derived-operations I read sites.tex Tag 00YV, proposition-functoriality-algebraic-structures-topoi, and sites-cohomology.tex Tags 07A4 (lemma-pullback-tensor-product), 07A6 (lemma-adjoint), 0B56 (equation-projection-formula-map), together with the statement of the internal/section-module equivalence and sk-prop-sfb-cartesian-coefficients. The combined derived comparison is agent assembled, not claimed to be the literal statement of 00YV. Its intended argument is: the section-action equivalence and its inverse preserve the underlying abelian sheaves, hence kernels, cokernels, acyclicity and quasi-isomorphisms; the balanced bilinear universal property identifies ordinary relative tensors. The equivalence and tensor identity preserve K-flatness, and exact equivalences preserve K-injectivity. The underived inverse-image action and direct-image action are the same sectionwise actions, so deriving gives the displayed functor comparisons. Deriving the same adjunction identifies its unit/counit; deriving the same tensor comparison identifies its monoidal structure. Thus the displayed adjunct is identified by that very adjunction, rather than by a claimed uniqueness of arbitrary projection isomorphisms. This is a real comparison lemma, retained as an unsplit node without a proof sketch inside its statement.

For lem-sfb-ringed-projection-first-shift I read the same Tags 0B56 and 07A4, derived.tex Tag 0A8D (lemma-adjoint-is-exact), and the existing adjunction-shift and ringed-mate statements. These sources supply the construction and exactness inputs, not a ready-made first-input compatibility theorem. Its intended proof substitutes epsilon_(K[1]) = epsilon_K[1] composed with e_U and U(e_R) in the adjunct (epsilon_K tensor 1) mu_(RK,P). Shift compatibility of mu and of tensor makes the resulting transpose the shifted transpose at K. The shift-compatible adjunction bijection then gives s_G pi_(K[1],P) = pi_(K,P)[1] s_F. Naturality gives the first two triangle squares and this equation the connecting square. In particular the new node is not obtained merely from naturality of a transformation, which alone would not suffice.

I checked B1–B10: both new nodes introduce all objects and ringed-site/size hypotheses, cite their notions, have only statements and empty proof fields, exact blueprint ancestry and places, and genuine retained Mathlib searches with two phrasings. The search responses concern ordinary underived module sheaf adjunctions, counit coherence, and generic derived transformations. Mathlib/Algebra/Category/ModuleCat/Presheaf.lean:24 explicitly lists the internal-module comparison as future work. No candidate is a one-line specialization of the asserted full derived comparison or first-input projection coherence, and no unavailable service is labeled no match. Existing Mathlib leaves are reused by citation.

For C1–C8 I opened all distinct cited statements and copied them into citations.json; the new comparisons replace actual hidden inferences rather than a definition citation being treated as a theorem. For D1–D5 the unchanged bounded formula is reused, while tensor closure and both determination arguments remain explicit. Neither new lemma is a clause of the item. For E1–E7 I checked the geometry, universes, coefficient rings and chosen shift structures, and distinguished ordinary ambient sums from completion. No SGA source is used. Every non-elementary item step is below 2000 characters; there is no long argument left to conceal a comparison.

Small cases checked: the identity morphism (both comparisons and the projection are identities after unit identifications), zero inputs, the empty site/scheme and empty coproduct, shift 0 and shift 1, a geometric point with the tensor unit, and O_E/pi_E, whose derived tensor retains the Tor term. Neither new assertion assumes flatness of an input complex or invertibility of a projection mate. On infinite sums with unbounded shifts, only the localizing restriction of Rp_* is used. The section-ring lemma does not replace continuous condensed sections by a discrete ring. The first-shift lemma remains meaningful for nonproper ringed morphisms because it asserts compatibility, not a projection isomorphism.

## Not duplicates

I searched the whole DAG by tags and concepts, and the whole imported blueprint using blueprint_refs.py (ancestor, projection, section-ring, internal module and shift compatible). Existing exact bounded formula and second-input mate statements are cited. The closest additional comparison, lem-c2-proetale-section-module-algebraic-inverse-image, is underived and identifies only algebraic inverse image; lem-weil-pbc-ring-sheaf-change-adjunction compares scalar restriction between different ring sheaves, not internal modules and section-ring modules. The remaining same-tag pairs are distinguished below. Common Stacks tags record shared inputs, not identical statements.

- lem-sfb-section-module-derived-operations vs def-asd-ordinary-supported-kummer-scalar: the existing statement is about Canonical derived scalar-change relation for supported Kummer classes; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-coef-ringed-sequence-site: the existing statement is about Canonical ringed sequence site for the coefficient quotient tower; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-coef-ringed-tensor-hom-model: the existing statement is about Canonical closed tensor-Hom representative model on a ringed site; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-kun-constant-projection-morphism: the existing statement is about Canonical constant-coefficient derived projection morphism; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-pe-comparison-torsor: the existing statement is about Torsors under the comparison inverse image of a group sheaf; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-algebraic-inverse-image: the existing statement is about Algebraic inverse image of ring and module sheaves; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-continuous-coefficient-module-encoding: the existing statement is about Explicit continuous coefficient module encodings; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-derived-direct-image-composition: the existing statement is about Composition isomorphisms of derived direct images (conjugates of those of inverse images); it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-derived-normalization-arrows: the existing statement is about Canonical derived coefficient normalization arrows; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-four-arrows: the existing statement is about Four finite-level arrows; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-four-corners: the existing statement is about Four finite-level corners; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-internal-abelian-sheaf-module-equivalence: it gives the abelian section-action equivalence and underlying sheaves, without its derived monoidal/adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-projection-formula-map: the existing statement is about Projection-formula map; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-ringed-tensor-square-presentation: the existing statement is about Representative presentation of a commutative ringed tensor square; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-sheaf-pullback-unit-presentation: the existing statement is about An inverse-image presentation with specified unit; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs def-weil-pbc-sites-and-cohomology: the existing statement is about Sites, morphisms of sites and cohomology on an object of a site; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-c2-proetale-section-module-algebraic-inverse-image: it gives an underived AlgebraicInverseImageOfUniverses presentation, with no derived tensor/pushforward/adjunction equivalence.

- lem-sfb-section-module-derived-operations vs lem-kun-inverse-image-monoidal: the existing statement is about Monoidality of the derived inverse image; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-pe-constant-left-module-inverse-image: the existing statement is about Exact geometric inverse image with arbitrary constant left-module coefficients; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-pur-derived-pullback-tensor-iso: the existing statement is about Derived pullback commutes with derived tensor product on the constructible categories; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-pur-sheaf-ring-derived-coefficient-adjunction: the existing statement is about Derived change of rings along a map of ring sheaves is left adjoint to restriction of scalars, with normalized unit and transposes; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-pur-support-site-comparison: the existing statement is about Etale-proetale comparison for supported sections and their exterior products; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sbc-derived-restriction-zero-transport: the existing statement is about Restriction triangle and coefficient transport in degree zero; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sbc-derived-section-pullback-zero: the existing statement is about Degree-zero derived section pullback before restriction coherence; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sbc-derived-section-single-unit: the existing statement is about Derived section pullback intertwines the two single-object units; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sbc-restricted-derived-evaluation-pullback: the existing statement is about The restricted derived section square for arbitrary source sheaves; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sbc-restricted-derived-section-shift-comparison: the existing statement is about Shifted single comparison for restricted derived section pullback; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sbc-restricted-derived-section-zero-comparison: the existing statement is about Zeroth comparison for restricted derived section pullback; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sbc-restricted-derived-sections-shift-transport: the existing statement is about Transport of restricted section pullback through the shift comparison; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sbc-restricted-derived-sections-single: the existing statement is about Single comparison for restricted derived sections before homology; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sc-etale-inverse-image-joint-representatives: the existing statement is about Simultaneous local unit representatives of etale inverse-image sections; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-sf-point-fibre-derived-tensor: the existing statement is about The point fibre functor preserves derived tensor at all coefficient stages; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-derived-scalar-extension-restriction-adjunction: the existing statement is about Derived reduction modulo varpi^n is left adjoint to restriction of scalars; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-abelian-pullback-global-sections-comparison: the existing statement is about Abelian inverse-image global sections and set section comparisons; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-adjunction-lifts-abelian-group-objects: the existing statement is about An adjunction between finite-product-preserving functors lifts to abelian group objects; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-adjunction-lifts-group-ring-objects: the existing statement is about An adjunction whose left adjoint preserves finite products lifts to abelian group and commutative ring objects; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing statement is about The cohomology pullback is induced by the unit of the derived adjunction; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-constant-ring-inverse-image-comparison: the existing statement is about Compatible constant-ring inverse-image comparison; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-derived-adjunction-shift: it states canonical derived adjunction shift compatibility, without the tensor/counit projection comparison.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-abelian-direct-image-internal: the existing statement is about The internal commutative-group identification commutes with abelian etale direct image; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-abelian-local-unit-representatives: the existing statement is about Local unit representatives for a supplied abelian etale inverse image; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-inverse-image-abelian-lift: the existing statement is about Étale inverse image: abelian lift and hom-set comparison; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-inverse-image-abelian-lift-hom: the existing statement is about lem-weil-pbc-etale-inverse-image-abelian-lift-hom; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-inverse-image-abelian-lift-ops: the existing statement is about lem-weil-pbc-etale-inverse-image-abelian-lift-ops; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-inverse-image-algebraic-structures: the existing statement is about Inverse image of etale sheaves of sets, abelian groups and rings; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-inverse-image-ring-adjunction: the existing statement is about Étale ring inverse-image adjunction and forgetful hom-set comparison; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-inverse-image-ring-lift: the existing statement is about Étale inverse image: ring lift and hom-set comparison; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-ring-direct-image-comparison: the existing statement is about The transported right ring-object functor is sectionwise etale direct image; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-ring-direct-image-operations: the existing statement is about Sectionwise ring-operation preservation of the etale direct-image comparison; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-ring-inverse-image-counit: the existing statement is about EtaleRingInverseImageCounit; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-etale-ring-inverse-image-unit: the existing statement is about EtaleRingInverseImageUnit; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-finite-level-rectangle: the existing statement is about Finite-level exchange rectangle; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-finite-product-ring-functor: the existing statement is about A finite-product-preserving functor transports commutative ring objects; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-geometric-ring-transport: the existing statement is about Ring operations transported through a geometric inverse image; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-inverse-image-comparison-addition: the existing statement is about Addition transport for supplied compatible comparisons; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-lifted-comm-group-branch: the existing statement is about Mathlib group lifting with explicit operation and adjunct formulas; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-lifted-comm-ring-branch: the existing statement is about Assembly of the transported ring-object adjunction; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-module-pullback-section-comparison: the existing statement is about Underlying sets of module pullback section comparisons; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ring-adjunct-preserves-operations: the existing statement is about The forward adjunct preserves internal ring operations; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ring-coadjunct-preserves-operations: the existing statement is about The inverse adjunct preserves internal ring operations; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ring-hom-equiv-core: the existing statement is about The natural hom-bijection restricts to transported ring objects; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ring-sheaf-change-adjunction: it compares restriction of scalars between two ring sheaves, without an internal-module equivalence or its symmetric monoidal comparison.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ringed-exchange-tensor-coherence: it compares exchange and tensor maps for a square of ringed topoi, not shifts in a projection input or internal/section-ring derived categories.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ringed-projection-mate-exact: it states shift compatibility after fixing E and varying P, whereas the new shift lemma varies K; it assumes module-sheaf categories and does not compare them to internal modules.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ringed-projection-restriction: the existing statement is about Localization comparisons for the ringed projection mate; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: it states ringed pullback/tensor compatibility, without internal-module transport or the first-input projection-mate equation.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-abelian-forward: the existing statement is about The full sectionwise abelian-object functor; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-abelian-objects-bijective: the existing statement is about Sectionwise abelian-object functors are bijective on objects; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-abelian-objects-bijective-injective: the existing statement is about Sectionwise reconstruction is injective on objects; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-abelian-objects-bijective-surjective: the existing statement is about Sectionwise reconstruction is surjective on objects; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-algebraic-structures-abelian-component: the existing statement is about SheavesAlgebraicStructuresAbelian intermediate component; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-algebraic-structures-objects: the existing statement is about Sheaves of abelian groups and of commutative rings are group and ring objects in sheaves of sets; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-algebraic-structures-ring-component: the existing statement is about SheavesAlgebraicStructuresRing intermediate component; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-algebraic-structures-ring-core: the existing statement is about Ring sectionwise construction and operation compatibility; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-algebraic-structures-ring-morphism: the existing statement is about Ring sheaf morphism criterion; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-pullback-forget-comparison: the existing statement is about Canonical forgetful comparison for sheaf inverse image, respecting units; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-pullback-unit-presentation: the existing statement is about Maps, products and equality testing for inverse-image unit presentations; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-ring-object-sectionwise-reconstruction: the existing statement is about Sectionwise reconstruction on the identical underlying sheaf; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-ring-objects-bijective: the existing statement is about Sectionwise ring-object functors are bijective on objects; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-ring-objects-injective: the existing statement is about Injective component of sectionwise ring-object reconstruction; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-sheaf-ring-objects-surjective: the existing statement is about Surjective component of sectionwise ring-object reconstruction; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-site-pullback-abelian-underlying: the existing statement is about Underlying sets commute with abelian sheaf inverse image; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs new-r2-etale-abelian-kan-comparison-locally-surjective: the existing statement is about Local surjectivity of the concrete underlying-set Kan comparison; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-section-module-derived-operations vs prop-weil-pbc-derived-inverse-image-adjunction: the existing statement is about Derived adjunction of inverse and direct image on D^+; it does not assert the derived symmetric monoidal equivalence between internal modules and modules over their section ring with both derived adjunction comparisons.

- lem-sfb-ringed-projection-first-shift vs def-coef-ringed-tensor-hom-model: the existing statement is about Canonical closed tensor-Hom representative model on a ringed site; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs def-kun-constant-projection-morphism: the existing statement is about Canonical constant-coefficient derived projection morphism; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs def-weil-pbc-four-arrows: the existing statement is about Four finite-level arrows; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs def-weil-pbc-four-corners: the existing statement is about Four finite-level corners; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs def-weil-pbc-projection-formula-map: the existing statement is about Projection-formula map; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs def-weil-pbc-ringed-tensor-square-presentation: the existing statement is about Representative presentation of a commutative ringed tensor square; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs lem-kun-inverse-image-monoidal: the existing statement is about Monoidality of the derived inverse image; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs lem-pur-derived-pullback-tensor-iso: the existing statement is about Derived pullback commutes with derived tensor product on the constructible categories; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs lem-pur-support-site-comparison: the existing statement is about Etale-proetale comparison for supported sections and their exterior products; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs lem-sf-point-fibre-derived-tensor: the existing statement is about The point fibre functor preserves derived tensor at all coefficient stages; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs lem-sf-triangulated-right-adjoint: it gives exactness of an adjoint, without the projection transformation or a section-module equivalence.

- lem-sfb-ringed-projection-first-shift vs lem-trf-finite-structural-maps-commshift: its four maps are the ordinary unit, proper coincidence, compact-support composition and exceptional counit at finite coefficients, not the projection mate in K.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-adjunction-shift-compatibility-unique: it supplies unique adjunction-compatible shifts, without a tensor projection mate.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-derived-adjunction-commshift: it gives shift compatibility of a derived adjunction unit and counit, not the projection comparison.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-derived-adjunction-shift: it states canonical derived adjunction shift compatibility, without the tensor/counit projection comparison.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-derived-exchange-triangulated: the existing statement is about The derived exchange transformation commutes with shifts and maps triangles to morphisms of triangles; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-finite-level-rectangle: the existing statement is about Finite-level exchange rectangle; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-ringed-exchange-tensor-coherence: it compares exchange and tensor maps for a square of ringed topoi, not shifts in a projection input or internal/section-ring derived categories.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-ringed-projection-mate-exact: it states shift compatibility after fixing E and varying P, whereas the new shift lemma varies K; it assumes module-sheaf categories and does not compare them to internal modules.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-ringed-projection-restriction: the existing statement is about Localization comparisons for the ringed projection mate; it does not assert the first-input shift equation for the ringed projection mate with arbitrary K and fixed P.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: it states ringed pullback/tensor compatibility, without internal-module transport or the first-input projection-mate equation.

- lem-sfb-ringed-projection-first-shift vs lem-weil-pbc-ringed-slice-evaluation-transpose: the existing node gives slice-restriction compatibility with tensor-Hom evaluation, transposition, and Koszul symmetry for arbitrary unbounded objects; the new node instead gives the shift equation in K for the projection mate R K tensor P to R(K tensor U P), with no slice restriction or internal-Hom comparison. Neither statement specializes to the other.

- lem-sfb-section-module-derived-operations vs lem-weil-pbc-ringed-slice-evaluation-transpose: the existing node compares evaluation and transposition under restriction to a slice of one ringed site; the new node compares internal-module and section-ring derived categories and their tensor and inverse/direct-image adjunctions, without asserting slice evaluation compatibility.

The resumed dry run identified the newly present same-tag slice-evaluation node above. I opened its full statement and verified both distinctions before adding these comparisons; no mathematical node or retained search record was changed.
