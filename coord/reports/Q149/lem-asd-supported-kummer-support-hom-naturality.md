# Stage-1 delivery: lem-asd-supported-kummer-support-hom-naturality

## Files written

- dag/nodes/sec-smooth-purity/lem-asd-supported-kummer-support-hom-naturality.json: item, statement unchanged, ten proof steps, status split; Mathlib verdict no match.
- citations.json: verbatim statements backing all 34 step/node citations.
- report.md: this report. No new DAG nodes and no Mathlib leaves created.

## Attachments

None. Searches of WeilConjectures/ in the read-only slopmaster2 source for the blueprint tag, supported Hom terminology, support cohomology and the relative-cohomology interface did not produce a declaration giving this complete assertion. Existing supported-class adjunction declarations concern exceptional inverse image and do not identify this relative section cone under arbitrary pair pullback. The upstream master checkout was not treated as finished proof evidence.

## WANTED

None. The current blueprint proof and all Stacks tools used are available locally.

## Findings and changes

The imported statement is sound, and no statement dispute or change is needed. Its empty proof did not justify that the relative-section pullback agrees with pullback of a derived morphism. Naturality in K in lem-amb-closed-support-hom alone does not supply change-of-scheme naturality. I kept the source's route through the constant open-closed exact sequence and expanded the actual comparison of resolutions, complexes and maps.

The canonical closed exchange is proved on geometric stalks, including its map rather than just the isomorphism types of its endpoints. Its compatibility with the constant unit is checked on constant generators. The comparison uses an actual resolution a:h^{-1}I -> J and does not assume h^{-1}I remains injective or K-injective. The signed kernel-to-cone quasi-isomorphism, diagonal cone map, homotopy independence and forgetting-support projection are written out. No separate node is made for these short consequences of existing tools and the definitions.

The original search log was preserved and read. It records the original grep, LeanSearch, Loogle and two different LeanFinder phrasings; their hits concern unrelated support conditions, ordinary homology naturality, free module pullback and topological union pullback cones. A targeted logged grep located CategoryTheory.Sheaf.ΓHomEquiv_naturality_left/right at Mathlib/CategoryTheory/Sites/GlobalSections.lean:107 and :121; I read lines 90-135. They assert ordinary global-section adjunction naturality and do not give derived relative cohomology or the closed exchange. Existing item searches have been retained, and new entries reproduce the saved log's tool and query exactly. No searches are invented and no service failure is called absence.

The chapter and unit records and three blueprint levels were read. The item remains in its existing unit and on the supported Cartier Kummer route. The current main-20261015 files are under sec-six-functors-basics: sk-prop-sf-cbc/lem-amb-closed-support-hom.md and .proof.md, and sk-lem-geo-cartier/lem-amb-cartier-kummer-map.md and .proof.md. The existing blueprint ancestry through thm-asd-smooth-tensor is preserved. Whole-blueprint searches for support, support Hom, relative section, stalk pullback and closed immersion exchange, and whole-DAG searches for the relevant interfaces found no second blueprint statement of this comparison. The relative-cone lemma lem-pur-divisor-relative-cone treats degree-zero abelian coefficients and specified etale/proetale comparisons, not this arbitrary scheme pullback for bounded-below A-module complexes. It is neither used nor duplicated.

## Not duplicates

No new nodes. The closed-exchange calculation is a step from existing stalk tools; the injective Hom exact sequence is a step from the existing open-closed sequence and injective definition; the kernel-to-cone comparison is an explicit cycle/boundary calculation. None is renamed as a new child that restates a clause of the item.

## Review by Q149

I read the current blueprint support-Hom proof and the penultimate paragraph of its Cartier Kummer proof, then Stacks etale-cohomology.tex at Tags 03Q1 (lemma-stalk-pullback), 04FX (lemma-stalk-pushforward-closed-immersion), 03PU (theorem-exactness-stalks), 095L (lemma-ses-associated-to-open), and 0A45 (lemma-cohomology-with-support-triangle). I read injectives.tex Tag 079P and derived.tex Tags 070I, 070K and 08BJ. These supply the actual localization/resolution route; no SGA source or purity theorem is used. There are no new-node sources to review.

For step 1 I opened the statements of lem-weil-pbc-closed-immersion-base-change, lemma-openclosed-stalk-upperstar, lemma-openclosed-stalk-lowerstar and lemma-weil-pbc-geometric-stalk-conservative. They give respectively stability, inverse-image stalks, closed-image stalks and detection of isomorphisms. The exchange-definition node gives the restriction formula that identifies the map on stalks, and the direct-image definition evaluates the off-support fibre product as empty. The stalk assertions are about small etale sheaves, rather than the similarly named Zariski module-stalk nodes, which I excluded. The constant-module exactness node supplies the coefficient identification and linearity. There is no finiteness, torsion, smoothness or Cartier hypothesis in this argument.

For step 2 the exchange definition, constant sheaf's sheafification property and the exact-module-pullback node specify the adjunction maps and constant identifications; the displayed unit identity is checked on local constant sections. This is the normalization later needed for forgetting support.

For step 3 I checked that the Grothendieck-abelian assertion covers modules over any commutative constant ring on each scheme, and that the resolution-existence assertion supplies both K-injectivity and injectivity of every term, together with an actual quasi-isomorphism. Exact inverse image makes the pulled-back quasi-isomorphism valid. The same existence theorem is applied a second time, so nothing assumes pullback preserves injectivity.

For step 4 the cited open-closed short exact sequence explicitly includes module coefficients and the specified counit/unit. The injective definition gives surjectivity of Hom restriction. The extension-by-zero adjunction gives Hom on the open with its counit formula, so the displayed map really is restriction of sections. The rest is a termwise kernel/cokernel argument and evaluation on the constant generator 1.

For step 5 the exact extension-by-zero and its adjunction meet the exact-left-adjoint hypothesis of the K-injective-preservation lemma. Exact inverse image supplies the restricted quasi-isomorphisms. The total-derived lemma applies because the termwise additive sections and Hom functors commute with finite sums, shifts and cones. K-injective existence is available on V and V' as well as on T and T'. These statements compute the precise complexes used, with no boundedness assumption on the resolutions.

For step 6 I checked the cone sign against def-weil-abstract-derived-category: Cone(r)[-1] has differential (-d_B b-r(s),d_E s). The two displayed lifts through the degreewise-surjective r prove both surjectivity and injectivity on cohomology. The existing support-Hom assertion supplies the interface, while the proof here specifies its standard kernel inclusion normalization; it does not take an unasserted base-change property from that node's proof.

For step 7 I checked all map types: f_C has source i'_*A_{D'} by precomposition with e^{-1}, followed by pulled-back c and the comparison a. Restriction gives the open map, and step 2 gives the equality on the kernel inclusions. These yield a strict diagonal map of cones, with no appeal to an unspecified cone of a square in a triangulated category. The inverse-image and exact-module nodes supply its adjunction and coefficient identifications.

For step 8 the K-injective Hom-to-derived bijection applies with arbitrary source h^{-1}I and K-injective target J, and thus controls comparison choices. The cone homotopy includes the necessary minus sign in the open summand. For step 9 the same bijection identifies degree-q cocycles modulo boundaries with derived maps for every integer q; the shift convention is explicitly cited. The strict square of step 7 then yields the claimed equality after inverting the two kernel/cone comparisons. For step 10 the cone projection composed with the kernel inclusion is literally precomposition by the unit, which proves the final clause with the same normalization.

I tested D empty (closed source zero and the relative cone of the identity acyclic), D=T (open term zero and the comparison the ordinary global-sections/constant-Hom comparison), K=0, h the identity, h factoring through the complement, A the zero ring, and arbitrary integer q. The formulas retain their types and signs in all these cases. The proof uses ordinary constant A-module coefficients throughout and does not pass to completed or constructible categories.

I checked delivery-errors B-E: no new statements or hidden proof sketches in new nodes, no invented Mathlib leaf, all cited node statements opened, all non-elementary tools cited, no statement weakening, no renamed item clauses, and no hypothesis added. Every step is under 2000 characters; the elementary steps are the displayed stalk, kernel, adjunction, cone or homotopy calculations from cited statements. The generic off-unit tools are declared in split_report.tool_uses; maintainer-owned tool_uses and metadata are untouched. citations.json quotes the actual cited assertions. Independent maintainer review remains to follow delivery.

## Unfinished

None in the mathematical split. Stage 2 and Lean proof construction are outside this dispatch. The required server dry run exited 0 and printed OK (not pushed), preflight passed, for commit b3d222c13b. The final delivery command reruns preflight before pushing.
