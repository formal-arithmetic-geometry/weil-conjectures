# Stage-1 delivery: lem-per-trait-sheaf-gluing

Group Q35; 2026-10-18. Direct delivery, with worker self-review and subsequent independent maintainer review.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-trait-sheaf-gluing.json: statement item, split into ten proof steps. The statement, original provenance and original Mathlib searches are preserved. New actual search records are appended.
- citations.json: a verbatim statement quotation for every cited node of every proof step.
- report.md: this report. searches.jsonl is the search command's actual log.

New nodes: 0. New Mathlib leaves: 0. No Lean source was written or compiled.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 source for the item id, trait/sheaf/gluing, and specialization terminology. No project declaration gives this category equivalence and all its clauses. Existing open/closed and restriction declarations supply only ingredients. Master is reference material, not an attachment certificate.

## WANTED

None. Every source needed is present locally.

## What needed correction or expansion

The item's statement is correct. Its notation M_s means a geometric stalk at the fixed closed geometric point, as in ILO XVII convention ii. The original proof was empty: ILO XVII 1.2.2 calls the set-sheaf arrow equivalence clear but does not prove it there. I supplied its explicit inverse and natural reconstruction maps, then treated coefficients, kernels, cokernels and sections.

The source statement has an arbitrary commutative ring. lem-exc-field-discrete-modules requires a finite ring, so it cannot supply this case. Steps 2-3 instead transport the scalar endomorphisms along lem-exc-abelian-sheaves-gmodules. A constant-ring-sheaf action is recovered by local constant scalar representatives and unique sheaf gluing. No finite generation, constructibility, torsion, excellence or invertibility hypothesis is used.

A further C4 check found that lem-exc-field-sections-stalk-invariants speaks of an algebraic closure whereas this item allows an arbitrary algebraically closed overfield Omega. I removed that citation and supplied the short argument Gamma(F)=Hom(Z_constant,F)=Hom_H(Z,V)=V^H, with the constant-stalk and abelian-sheaf equivalence nodes. Thus the invariant comparison is the actual germ map for this Omega, without an unstated algebraicity assumption.

The familiar lem-weil-pbc-closed-pushforward-stalks and lem-weil-pbc-closed-immersion-pushforward-fully-faithful are about Zariski O-modules. I did not use them. Step 7 uses lem-kun-04ca, whose statement is the etale abelian-sheaf closed-immersion theorem.

## Sources, blueprint, and Mathlib searches

Read ILO Travaux de Gabber, Expose XVII, section 1.2.2 opening paragraph, printed p. 260, together with the immediately preceding conventions. Read the local Stacks etale-cohomology.tex statements/proofs at Tags 04JQ (lemma-equivalence-abelian-sheaves-point), 03QT (theorem-equivalence-sheaves-point), 03QW (lemma-global-sections-point), 03QO (lemma-vanishing-etale-cohomology-strictly-henselian), 03Q1 (lemma-stalk-pullback), 04CA (proposition-closed-immersion-pushforward), 04FX (lemma-stalk-pushforward-closed-immersion), 03PT (lemma-stalk-exact), and 03PU (theorem-exactness-stalks). No SGA source is used. The proof is marked agent-written because it expands an assertion of clarity into an explicit reconstruction.

Read the chapter and sk-p-dl-a1-perverse unit records and the current main-20261015 ancestor lem-per-artin-gabber-affine-curve proof, especially Step 3. This auxiliary implements the sheaf input to the normalized trait residue model below the ancestor's potential-dualizing argument. It does not change the chapter or unit route. The item is not the unit's key statement, so no unit record was changed. Its existing from.node/place/via were retained; same_as remains empty after whole-blueprint searches for gluing, specialization arrow, and strictly henselian trait sheaf. DAG searches by these notions and by the relevant Stacks tags found ingredients, not a duplicate of the item. No new node is proposed.

Ran the prescribed msearch command with leanfinder twice (trait arrows; more general open/closed Artin gluing), loogle, grep and leansearch; read every returned hit. Services worked. Loogle's AffineEtale.sheafEquiv and abelian/Grothendieck instances concern the affine-etale/small-etale comparison, not gluing along the closed complement (read AffineEtale.lean around lines 140-155). The semantic hits concern structure-sheaf specialization or Zariski open-cover/scheme gluing. They do not state this item or a one-line generalization. The grep found no matches. Exact tool names and query text are preserved in searches.jsonl and appended to mathlib_searches.

## Not duplicates

No new nodes. Existing categorical and field lemmas are cited directly rather than restated as new nodes.

## Review by Q35

I checked delivery-errors B through E against the item, the source paragraphs and the full statements of every cited node. The item introduces R, T, the two points, K, Omega, Ksep, H and Lambda. The fixed geometric closed point is made explicit in Step 1; separably closed residue is supplied by def-weil-pbc-henselian-terminology. The nonfield local PID definition of a DVR gives the two-point spectrum and the open generic point. I verified the statement's dependency list is unchanged and contains all its named definitions.

Step 1 uses precisely the strictly henselian and DVR definitions and the geometric-stalk definition. A nonzero prime of a PID is maximal, so there are exactly two points; inverting a uniformizer gives the fraction field. This is an elementary argument, not a new lemma.

Step 2 uses the arbitrary-algebraically-closed-overfield abelian-sheaf equivalence of lem-exc-abelian-sheaves-gmodules. The sheaf-of-modules and constant-sheaf definitions support the scalar-endomorphism transport. The equations and scalar-linear morphisms are written out, so no finite-ring field-module theorem or unwritten module-object classification is taken as a black box.

Step 3 uses that same field equivalence with separably closed residue field, hence trivial absolute Galois group. prop-weil-pbc-inverse-image-modules-exact supplies the exact constant-coefficient inverse image, its coefficient identification, module direct image, and actual adjunction units/counits. These are the functors used in the fiber product, not derived or adic replacements.

Step 4 uses lem-weil-pbc-constant-sheaf-geometric-stalk for the normalized integer stalk. Changing a geometric lift does not change a constant germ, so the action is trivial. Full faithfulness of the abelian-sheaf equivalence and evaluation at 1 give the invariant-section comparison. The strict-local sections-stalk node states the germ isomorphism for any abelian sheaf over any strictly henselian local ring and any algebraically closed residue overfield; it applies to j_*F without constructibility or finite-stalk hypotheses. def-weil-pbc-direct-image identifies its T-sections with F(eta), and lemma-openclosed-stalk-upperstar identifies the closed inverse-image stalk. I removed the algebraic-closure-only invariant node after checking its precise hypothesis.

Step 5 uses the strict-local germ theorem and the stalk definition to identify specialization with the actual restriction of a global representative. The image is invariant by Step 4. This proves equivariance and naturality, not merely the existence of an abstract arrow.

Step 6 uses the module adjunction and the sheaf-of-modules definition. Its fiber product is constructed sectionwise by pairs with equal images and verified by the sheaf gluing condition. The map from the closed factor is the actual b:W->V^H. This is an elementary finite-limit construction, not an invocation of an unstated recollement theorem.

Step 7 cites the exact module inverse image for preservation of the fiber product, lem-kun-04ca for the closed counit and supported image, and lem-sc-open-immersion-pushforward-fully-faithful for the open counit. All three are etale assertions. The abelian counit is a module counit because it commutes with each scalar. The i-inverse image of the i-unit is identity under the counit by the triangle identity. Hence the two fiber products become B times_B C(W) and F times_0 0. The strict-local germ node then identifies the first projection's closed-stalk map with b; this checks the specialization arrow too.

Step 8 uses the actual module adjunction units, the inverse-image stalk comparison, and the geometric-stalk isomorphism detection theorem. I wrote the naturality square that makes the two maps to i_*B equal. The reconstruction map is identity on both restrictions by triangle identities. The two chosen geometric points cover T; the detector applies to underlying set sheaves, and a bijective module homomorphism has a linear inverse. This proves the natural inverse equivalence without assuming the desired classification.

Step 9 uses only the definition of discrete continuous modules. I wrote the kernel and quotient arrows and both universal properties. Quotient continuity is checked by the stabilizer of a representative, which is open and contained in the stabilizer of its class. Thus cokernels are genuinely in the continuous discrete category. No exactness of invariants is claimed; that functor is generally not right exact.

Step 10 uses the strict-local theorem and the already proved invariant comparison from Step 4; it identifies the actual section restriction and generic restriction functors.

Every use has a verbatim statement quote in citations.json. Off-unit generic tools are declared with reasons in split_report.tool_uses; none replaces a step of this unit's route. A read-only dependency walk found no path back to the item. No proof step exceeds 2000 characters. The natural inverse and its arrow compatibility are proved in the item, so no clause has merely been relabelled as a child node.

I tested constant modules (W=V with identity and trivial action), closed-supported sheaves (V=0), open extension by zero (W=0), arbitrary nontrivial continuous generic action, the zero ring/modules, and a morphism whose quotient gains invariants. The fiber product gives the expected restrictions in each case; the last case confirms that componentwise cokernels do not require exactness of invariants. Neither the reconstruction nor the source uses finite coefficients or excellence.

## What remains

No mathematical work remains on this split. Run the required server dry run, repair any diagnostics, and push the same sandbox through deliver.py.
