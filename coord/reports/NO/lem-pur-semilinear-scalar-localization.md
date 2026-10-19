# Worker report: lem-pur-semilinear-scalar-localization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-semilinear-scalar-localization.json`: statement, split; not a Mathlib leaf. The statement is unchanged. Nine proof steps reuse existing nodes; no new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every node cited in every proof step.
- `searches.jsonl`: actual msearch records; the item's previous search records are retained in the node.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for semilinearity, scalar localization and semilinear functors found no declaration stating the item. The semilinear Frobenius, scheme-module and abelian-variety declarations concern different constructions. No upstream master sorry declaration is treated as finished evidence.

## WANTED

None. The current blueprint and the underlying commutative-algebra and triangulated-localization sources are present locally.

## Findings and changes

The base node was statement-only, with `lean_audit.slopmaster2.state = none`; no previous sandbox item or report existed. I retained its entire statement, provenance, historical Mathlib searches, chapter, unit, and blueprint ancestor. I added explicit statement dependencies for the localization ring and the existing definition of a morphism of exact functors. The actual proof is agent-written: the blueprint's finite-extension sentence does not supply the general categorical calculation in this item.

The route is the finite-extension part of `prop-pur-rational-purity-transitivity-summands.proof.md` in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/`, realizing Step 3 of `sk-thm-purity-transport`. I read the chapter and the unit record. The generic localization tools make that step precise and do not replace its purity construction. No SGA source is used.

The potentially dangerous inference is to treat the two inverted elements as equal or to require phi(t) to be a power of u. Instead the proof uses the unit c = image(phi(t)) in S[1/u], and obtains the formula with c^{-n}. A semilinear map on each Hom group becomes an R-linear map by restricting the target action along R -> S -> S[1/u]. Existing module localization then constructs it. Whiskering is checked after showing that the induced coefficient maps compose. In particular the next induced coefficient map sends c, already a unit, to a unit; it need not have an integral inverse.

## Mathlib searches and existing interfaces

I ran msearch with LeanFinder (two phrasings), LeanSearch, Loogle, and two grep patterns. All services returned results. The hits were read: `CategoryTheory.Localization.liftNatTrans` in `Mathlib/CategoryTheory/Localization/Predicate.lean:326`, with its component and vertical-composition formulas at lines 332 and 339, presupposes a categorical localization and specified liftings. `CategoryTheory.Localization.linear` and `functor_linear_iff` in `Localization/Linear.lean:37,79` are same-ring linearity results for such localization functors. They do not identify our raw Hom-tensor category as that localization. `LinearMap.extendScalarsOfIsLocalization` in `RingTheory/Localization/Module.lean:215` starts with two already localized modules and makes their R-linear map linear over the localized ring. It is not the categorical semilinear statement. The item therefore is not a one-line specialization of these hits. The Hom-module ingredients already have DAG leaves, so I created none.

I searched the whole DAG and imported blueprint by semilinear, localization, linear functor and natural transformation, including `tools/blueprint_refs.py search` and its ancestor command. The ancestor remains `prop-pur-rational-purity-transitivity-summands`; `same_as` remains empty. `prop-weil-pbc-rational-transport` treats the same coefficient ring O_E on source and target and the specified constructible categories. It is a special case of the present item, not a result giving the present different-ring assertion. I reuse the more basic module localization nodes rather than creating a semilinear module lemma that follows immediately by restricting scalars.

## Not duplicates

No new nodes. In particular no new node restates a clause of this item. The ring-fraction calculation, semilinearity, functor equations, and componentwise coherence calculations are proof steps.

## Review by NO

I read the current blueprint proof of the ancestor and its parent split, and opened every cited node's statement. For the algebra I read `literature/stacks-project/algebra.tex`: Tag 00CO (`definition-localization`, with the preceding fraction relation), Tag 07JZ (`definition-localization-module`), Tag 07K0 (`lemma-universal-property-localization-module`), and Tag 00DK (`lemma-tensor-localization`). The tags were checked against `literature/stacks-project/tags/tags`. For exactness I read `derived.tex`, Tag 05R6 (`proposition-construct-localization`), particularly its definition of distinguished triangles as images up to isomorphism. I also read the defining shift equation in the current blueprint's `pur9-def-exact-transformation.md`. These sources justify the existing interfaces used here; the extra categorical calculations are written in the item, not attributed to a source that omits them.

Step 1 uses `def-weil-ring-localization-away` for the equality criterion and ring operations on fractions. Applying the coefficient map to the annihilator equation and multiplying by c^{-k-m-n} proves independence; the ring operations and uniqueness are direct computations. This does not assume injectivity of either ring map or regularity of t.

Step 2 uses `def-weil-linear-scalar-localization` for the actual Hom tensor modules and the linear functor Q_S. `def-weil-pbc-module-localization-away` explicitly states the universal property for R-linear maps into modules on which t acts bijectively; I checked that its target is the Hom module in D[1/u], with the restricted R-action, where t acts as the unit c. `lem-weil-pbc-localization-module-tensor` states exactly the tensor/fraction identification with its generator formula, so this is a citation of its statement, not of its proof. This is the non-elementary existence input.

Step 3 uses the scalar-action formula in the module-localization definition and fraction presentations from the ring-localization definition. The displayed computation proves semilinearity, and evaluating on t^{-n}(f/1) proves uniqueness. Step 4 uses the composition and identity formulas in `def-weil-linear-scalar-localization`; its displayed product of denominators proves the functor law for every pair of localized arrows. These are short calculations from previously established maps, not black-box claims of existence.

Step 5 uses `def-weil-linear-category` for bilinearity and the scalar-localization definition for Q_S's functor laws. Multiplying the integral naturality equation by c^{-n} gives naturality on all fractions; localizing both inverse equations gives natural isomorphisms. All source objects remain objects of the localized category, which is why there is no additional choice of transformation components.

Step 6 uses only Steps 1–4: bar(psi) sends units to units and bar(H)bar(F) has the correct semilinearity and integral values, so uniqueness applies. I checked the compatible coefficient maps and the inversion hypothesis for the composite before invoking uniqueness. Step 7 uses Q's composition law from the scalar-localization definition. It writes the actual components for both whiskerings, and uses Step 6 to identify their endpoints. Induction on composition expressions then proves equation preservation. This avoids the two-square mismatch noted in the ancestor's independent review: there is no appeal to a generic grid-interchange statement.

Step 8 uses `lem-weil-linear-scalar-localization-triangulated` for the precise triangulated structure and exactness of Q in both categories. The categories have the required linear shifts by hypothesis. The scalar-localization definition supplies induced shifts and their commutation with Q. For a triangle with last arrow w, the transported last arrow is explicitly Q_S(sigma_K F(w)); this checks the shift comparison rather than merely asserting the endpoints agree. Every distinguished localized triangle is isomorphic to one of these integral images, exactly as the cited statement requires. `def-weil-triangulated-category` supplies closure under triangle isomorphism and the definition of exactness. The generic triangulation result is declared in `split_report.tool_uses` because the purity unit supplies no substitute for it.

Step 9 uses `pur9-def-exact-transformation`, whose statement gives the displayed shift square verbatim, and the scalar-localization definition for commutation of Q with shift and composition. Localizing that square proves that the extended comparison is exact. Its isomorphism property was separately checked in Step 5.

I checked B–E against the finished files: every non-elementary input is an existing cited statement, all citation quotations are literal parts of those statements, and no new lemma is hidden in an unsplit node or replaced by a document reference. Every proof step is under 2000 characters; the two non-elementary ones are 853 and 1145 characters. No separate standard comparison or identification is left unproved. The elementary steps use fraction arithmetic, the definitions, or preceding steps with their equations displayed.

For edge cases I checked t=1 (ordinary scalar extension on Hom groups), phi=id and t=u (the usual linear localization), torsion Hom groups (annihilator equations are respected), and nilpotent t. In the last case the unit c is nilpotent, forcing S[1/u] to be the zero ring, so all target Hom groups vanish and the construction still works. Taking u nilpotent gives the same harmless zero-category situation. Empty categories impose no extra condition. The hypothesis cannot be dropped: for R=S=Z, phi=id, t=2, u=3, a unital extension of the one-object ring category would have to invert 2 in Z[1/3], which is impossible. No domain, flatness, faithful scalar action, or idempotent-completeness hypothesis is used. No statement dispute or unfinished mathematical point remains.

## Unfinished work

None in this one-level split. Only the required server dry run and direct push remain at the time of writing this report; their output will be recorded below.
