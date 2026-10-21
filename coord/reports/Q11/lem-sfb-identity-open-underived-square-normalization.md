# Q11 stage-1 delivery: lem-sfb-identity-open-underived-square-normalization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-identity-open-underived-square-normalization.json: existing statement, split into nine proof steps using existing DAG nodes. Mathlib verdict: no match for the whole normalized identity-open assertion.
- citations.json: a verbatim statement quotation for every node cited by every proof step.
- searches.jsonl: actual msearch.py results for the item, with two semantic phrasings, Loogle, LeanSearch and two source greps. The item's earlier searches are retained unchanged; the new Q11 records are appended.

New nodes: 0. New Mathlib leaves: 0. The script write_split.py is sandbox preparation only, not a proposed project file.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint id and by identity/open, localization, adjunction and composition terminology found no declaration proving every clause. The adic constant-sheaf pullback identification and finite-coefficient open base-change declarations address different or partial statements and cannot attach this internal condensed-module assertion. No Lean was written or compiled.

## WANTED

None. The sources used are present locally. The old standing brief's coord/dag-sync.md is absent in the live shared repository; the direct-delivery brief supplies the current read-only/live-DAG policy, which this delivery follows.

## Problems in the imported node and changes

The item was statement-only, with no proof or proof dependencies. Its statement is valid and is unchanged. Its nearest blueprint ancestor is det-sf-comp-composition-base-change, proof (3), specifically the parenthesis about restricting base change for a refinement to its identity open locus. I read that current main-20261015 blueprint proof and the unit record sk-thm-sf-comp-composition and chapter record sec-six-functors-basics. The split stays below that route: it supplies the underived comparison normalization needed by the existing parent lem-sfb-base-change-identity-open-restriction. No compactification route is replaced and no unit record needs realization edits for this non-key node.

The phrase “same equality” in the last sentence refers to the pullback-square equality. Underived h_* need not preserve quasi-isomorphisms; the proof does not try to descend that functor or the underived adjunct equations termwise. All functors occurring in the square equality are exact pullbacks. The derived identity for the base-change mate itself remains in the parent item.

No STATEMENT-DISPUTED correction is needed. The specified coefficient identifications are essential: an arbitrary automorphism of either restricted coefficient ring would not justify the identity normalization. Step 2 uses the existing composition equation for the actual coefficient maps.

## Not duplicates

No new nodes. Searches of the whole DAG for Tags 04J0/07A7, localization of ringed morphisms, conjugates and pullback associativity, and blueprint_refs.py searches for identity open, identity locus, localized adjunction, pullback composition, conjugate and 04J0 were read. They led to reuse of lem-weil-pbc-localize-ringed-site-morphism and lem-pur-ringed-site-pullback-localization-universes instead of new localization or unit-normalization nodes. The existing lem-sfb-module-direct-image-open-pasting concerns direct-image/open comparison pasting, not this complete underived identity-open assertion; the item is proved explicitly rather than relabeled as a new lemma.

## Mathlib search assessment

The new searches returned SheafOfModules.pullbackComp, pullback_assoc, pullback_id_comp, pullback_comp_id, conjugateEquiv_pullbackComp_inv, Scheme.Modules.restrictAdjunction_unit_app_app and CategoryTheory.Adjunction.localization_unit_app, among others. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean, particularly pullbackId at line 139, conjugateEquiv_pullbackComp_inv at line 177 and pullback_assoc at line 193, and CategoryTheory/Adjunction/CompositionIso.lean at line 170. The first family provides generic module pullback composition; Scheme.Modules uses Zariski structural modules, not the current pro-etale condensed coefficient modules; category localization_unit_app concerns inversion of a class of morphisms, not restriction to a site object. None alone or clausewise by one-line specialization gives the two concrete localized module comparisons, both adjunct equations and the square normalization. Their abstract categorical content is already represented by the cited conjugation, composite-adjunction and mate-pasting nodes.

## Review by Q11

I read Stacks sites-modules.tex, Tag 04J0 (lemma-localize-morphism-ringed-sites), including the restricted ring-map construction and the assertion that localization pullback is restriction. I also read Tag 03D8 (lemma-push-pull-composition-modules) and sites-cohomology.tex, Tag 07A7 (remark-base-change). The tag-to-label table confirms these three tags. Stacks does not write the requested unit and reassociation formulas out; the proof_origin is therefore agent, with those explicit calculations supplied here. There are no new nodes needing separate source reviews.

For step 1 I checked the statements of the weakly-etale localization node (using its site-equivalence clause, not its constant-coefficient clause), the internal-module equivalence, the sectionwise pushforward definition and ringed-site localization. They give exactly the site and module identifications used. The sites are small in the coefficient universe as assumed in the item. The base-change functor is continuous by the cited definition and preserves finite limits by the fibre-product universal property; the identity on the slice is induced by the given h-inverse(U)=U identification.

For step 2 the Cartesian-coefficient statement supplies the canonical ring isomorphisms; lem-sfb-eta-comp supplies composition of the actual structural maps; ringed localization supplies identity on sections with the restricted scalar action. Thus this step checks module linearity, not just equality of underlying groups. No discrete or finite coefficient substitution is made.

For step 3 the universe-general localization theorem expressly states that the comparison's adjunct is the restricted global unit and that it is invertible. Its hypotheses (smallness, finite limits, continuity, slice continuity and specified left adjoints) were checked in steps 1 and 3. The adjunction definition explicitly gives the tensor-extension Hom correspondence. For the localized identity map that correspondence is m to 1 tensor m, with inverse multiplication. I did not infer this unit equation from a localization node that merely asserts an unspecified isomorphism.

For step 4 I opened the upper-star and lower-star composition definitions, the section formula in def-sfb-finite-lower-star-comp, the conjugate-isomorphism unit-equation statement and the composite-adjunction unit formula. They apply with L1=j*, L2=i*h*, R1=j_* and R2=h_*i_*. Evaluating that unit equation over T mapping to U removes the units of the open localizations and the sectionwise direct-image compositor. It therefore identifies the already specified b=a_h inverse with d, rather than choosing a new isomorphism. I checked the direction of every comparison. Step 5 is then just naturality of c_h composed with the proved unit equation, so needs no independent lemma or new node.

For step 6 I read the Cartesian-square definition. The pullback of the given identity open is the identity on U prime; the proof writes the fibre products and retains the projections and open inclusions. No density or properness hypothesis was inserted. This also checks the existence and types of both primed adjunct formulas.

For step 7 I read the full statements of the pullback-composition definition, the underlying direct-image compositor, def-sfb-finite-lower-star-comp, mate-pasting and the conjugation bijection. The last two give composition and whiskering of conjugates, which is precisely what is used to transfer the sectionwise triple-composition identity to pullbacks. The fibre-product maps agree because each projection agrees; the formula in this step includes the composite-adjunction normalization. This is an explicit associativity calculation from those tools, not an uncited theorem about arbitrary pseudofunctors.

For step 8 I checked the component types and expanded theta, s and t0 into inverse/forward m maps. The three applications of the step-7 identity are to (i prime,h prime,v), (i prime,w,h), and (v_U,i,h). The middle cancellation is legal because hw=vh prime; the final cancellation uses wi prime=iv_U and hi=j. These are exactly the morphism identities of the specified Cartesian open configuration. I corrected the order of qg in the general three-map associativity formula while doing this check. The step proves the square equation algebraically, with no additional standard-comparison claim hidden in prose.

For step 9 I read the exact-module-pullback theorem and both derived-category definitions. The exact-functor clause gives termwise derived pullback, and the ordinary derived category is localization at quasi-isomorphisms. Naturality supplies differential commutation; localizing an equality of chain maps supplies the derived equality. No K-injective, constructibility, localizing-closure or proper-base-change assertion is smuggled into this step.

I tested the edge cases U empty, h identity, v identity, zero module, and U=Z (which forces h to be the specified isomorphism). All formulas reduce to zero/identity functors or tensor-unit identifications with the stated directions. The proof works for nonproper h and needs no dense open. I checked B--E: no new nodes can be elementary/duplicate/clause restatements; the statement is self-contained via its definitions; every non-elementary input is a cited node whose actual statement was read; there is no appeal to a dependency's proof; no forbidden SGA route is used. Every step is below 2000 characters. Generic tools outside the unit are declared in split_report.tool_uses with their precise role.

## Unfinished work

None in the requested one-level stage-1 split. Existing cited lemmas may remain open as independent DAG items; this delivery does not claim Lean closure of the item.
