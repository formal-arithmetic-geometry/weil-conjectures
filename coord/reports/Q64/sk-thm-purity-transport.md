# Q64 repair: sk-thm-purity-transport

## Files written

- `dag/nodes/sec-smooth-purity/sk-thm-purity-transport.json`: unchanged statement; five assembly steps, 2440 characters total, status split.
- `dag/nodes/sec-smooth-purity/lem-pur-transport-finite-counit-system.json`: statement; unsplit; no Mathlib match. Finite diagonal-purity counit system, ordinary/condensed comparison, coefficient mates, reductions, geometric equations and integration.
- `dag/nodes/sec-smooth-purity/lem-pur-transport-integral-counit-realization.json`: statement; unsplit; no Mathlib match. Actual coherent tower realization, condensed-category identification, fixed counit, trace-family identification and integral coherence.
- `dag/nodes/sec-smooth-purity/lem-pur-transport-rational-hom-counit.json`: statement; unsplit; no Mathlib match. The specified localized Hom bijections, fractional-arrow naturality, representative independence and agreement with the rational trace family.
- `dag/nodes/sec-smooth-purity/lem-pur-transport-qbar-common-stage-counit.json`: statement; unsplit; no Mathlib match. Natural Hom-colimit adjunction, common-stage counit, geometric equality descent and conjugation to the chosen exceptional adjoint.
- `dag/units/sk-thm-purity-transport.json`: only realized and realized_by updated, assigning the recorded unit steps to the new nodes.
- `citations.json`: one verbatim statement quotation for each citation in the five parent proof steps.

## Attachments

None. I searched the project for the blueprint id and declaration name and read `lean/WeilConjectures/EtaleCohomology/Purity/Smooth/Transport.lean:77-114`. `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek` has a complete proof of preservation of derived completeness conditional on existence of the integral adjoint. It gives neither the purity isomorphism nor the adjunction/counit/coherence clauses of the item, so it is not an attachment. The project concept searches and the already attached source interfaces did not supply an exact declaration for any of the four new packages.

## WANTED

None. These are agent-written interface arguments following the current local blueprint, not claims of a theorem from an unread external text. The sources actually used are identified below; no Stacks tag asserts these entire transport packages, so no tag is invented for them.

## What was wrong and what changed

The human's return is about work granularity: the 13-step proof was 9437 characters and left its independent transport arguments in one node. This delivery repairs that by four comparable new work items. They are all statement-only with empty proof, empty proof_deps, null proof_origin, status unsplit, complete hypotheses, blueprint provenance and genuinely run Mathlib searches. They do not each restate the entire target. They can be worked on independently: integral realization has the existing tower inputs; rational localization assumes the existing tower adjunction; common-stage descent explicitly assumes finite-field adjunction data. It does not wait on a proof of either new sibling.

The parent statement is byte-for-byte the current repository statement, including its standing field and coefficient conventions. No imported metadata was changed. The sandbox initially contained only dispatcher marker files, so there was no earlier local proof, report or search log to reuse. I copied the current repository item, ran the requested initial dry run, and received the missing-report diagnostic. The current item is the returned 13-step version; its entire argument is preserved below, grouped by future work item, including all cited ids. The final counit-uniqueness comparison and substitutions remain in the short parent assembly.

## Search record

The required msearch command ran LeanFinder, Loogle, source grep and LeanSearch for each proposed package, and a second natural-language phrasing for each. Full returned answers are retained under research/*-search-output.txt; the command's own searches.jsonl is the authoritative log. I read the hits. The finite and rational first Loogle patterns had unknown identifiers; their notes are recorded honestly, followed by successful corrected searches for CategoryTheory.Adjunction.ofNatIsoRight and CategoryTheory.Adjunction.localization.

Mathlib has transport along a natural isomorphism and localization of an adjunction. I read Adjunction/Basic.lean (the Hom formulas at 521-531) and Localization/Adjunction.lean (the construction and counit formula, 33-135). These are useful formal tools, but do not identify the actual sheaf compactification functors, prove that the condensed categories have the asserted Hom comparison, identify the tower family with the reconstructed trace family, or give the stated coefficient and geometric equations. Hence none of these four geometric/interface statements specializes in one line from them. The other hits are ordinary structure-sheaf adjunctions, condensed free/forgetful adjunctions, algebra smoothness/etaleness, normalized field traces, and colimits of objects rather than an adjunction on the stated two-colimit of coefficient categories.

I searched the whole DAG by the notions and canonical arrows (localized Hom, common-stage adjunction, normalized integration, tower realization, purity counit), and the blueprint index by purity-transport, sp-integral-adjunction, sp-rational, sp-qbar, tower-trace-purity, finite-general-ring and normalized integration. These searches find the ingredients listed in the following distinctions, not an existing theorem with all the specified comparison data. The source Lean search finds only the partial completeness result above for the item's advertised name.

## Not duplicates

lem-pur-transport-finite-counit-system vs sk-thm-purity-transport: the parent treats all six coefficient stages and counit uniqueness; this task is the finite diagonal-purity adjunction system with fixed coefficient mates and normalization only.

lem-pur-transport-finite-counit-system vs det-sp-finite-general-ring: that theorem supplies the orientation and natural purity isomorphism; the new task forms the actual explicit adjunction, relates its counit across arbitrary finite coefficient maps and records the geometric/reduction/normalization equations for that system.

lem-pur-transport-finite-counit-system vs det-sp-reduction-compatibilities: that theorem supplies units, exceptional coefficient compositors and the purity square, not the explicit-adjoint counit equation and integration-normalized adjunction system.

lem-pur-transport-finite-counit-system vs lem-pur-projection-purity-agreement: that theorem compares two finite affine-space purity maps; the new task identifies the induced adjunction counit on condensed categories and its arbitrary finite-ring coefficient system.

lem-pur-transport-finite-counit-system vs det-sp-composition-factors: that theorem is the orientation/tensor composition calculation; the task includes its identification in the explicit counit system.

lem-pur-transport-finite-counit-system vs det-sp-purity-bc-factors: that theorem is the orientation/tensor Cartesian square; the task also assembles actual coefficient adjunctions and their normalized counits.

lem-pur-transport-finite-counit-system vs lem-pur-finite-site-counit-projection-transport: that theorem changes etale and pro-etale sites for a finite coefficient level; this task changes the right adjoint to the explicit twisted pullback and handles arbitrary finite coefficient rings.

lem-pur-transport-integral-counit-realization vs sk-thm-purity-transport: only the integral realization/comparison argument is extracted; no rational or algebraic-closure adjunction is concluded.

lem-pur-transport-integral-counit-realization vs det-sp-integral-adjunction-bijection: that theorem gives F adjoint to H and gamma^H in the completed category; the task identifies both operations on condensed categories, changes the right adjoint to J with its pinned counit, and proves coherent agreement with the reconstructed-trace family.

lem-pur-transport-integral-counit-realization vs det-sp-normalized-equivalence: that is a category equivalence, not the comparison of realized purity adjunctions with the fixed exceptional adjoint and trace family.

lem-pur-transport-integral-counit-realization vs det-sp-integral-direct-image-tower: that compares the compact-support operation with tower realization; the task also treats the right adjoint, the explicit-adjoint counit and the trace family.

lem-pur-transport-integral-counit-realization vs det-sp-field-extension-towers: that supplies actual tower coefficient maps; the task connects them to the fixed condensed explicit adjunction and reconstructed geometric equations.

lem-pur-transport-integral-counit-realization vs lem-pur-tower-trace-purity-comparison: that proves equality of tower and trace-transpose maps for the specified completed coefficients; the task also identifies the condensed categories and ambient left adjoint and specifies the normalized explicit counit and its realized adjunction.

lem-pur-transport-integral-counit-realization vs det-sp-tower-gluing: that constructs the tower adjunction; this task is its integral condensed realization and trace-family comparison.

lem-pur-transport-rational-hom-counit vs sk-thm-purity-transport: this task concerns finite rational coefficient fields, a specified localized Hom construction and its counit, not the theorem for all coefficients.

lem-pur-transport-rational-hom-counit vs det-sp-rational-localized-hom: that supplies Hom localization and F/pullback comparison maps but no adjunction bijection, representative/fraction naturality or comparison of the resulting purity family with the prescribed trace family.

lem-pur-transport-rational-hom-counit vs sk-lem-sp-field-extension: that gives coefficient comparators for raw rationalized operations and adjunctions; this task establishes the precise Hom construction in the condensed categories and its agreement with the specified rational trace family.

lem-pur-transport-rational-hom-counit vs lem-pur-tower-trace-purity-comparison: that identifies integral tower/trace maps and their localized purity maps, not the natural rational adjunction via the four Hom comparisons.

lem-pur-transport-rational-hom-counit vs lem-sf-rational-direct-image-adjunctions: that gives right adjoints to ordinary rational inverse images, rather than smooth twisted pullback as right adjoint to compact-support direct image.

lem-pur-transport-rational-hom-counit vs thm-pur-rational-and-qbar-purity: that asserts purity in the raw rational/common-stage category; this task pins the Hom bijection and integration counit on the condensed categories and checks the particular tower family used to obtain them.

lem-pur-transport-qbar-common-stage-counit vs sk-thm-purity-transport: this is the common-stage descent argument conditional on supplied finite-stage adjunctions, not the all-stage purity theorem.

lem-pur-transport-qbar-common-stage-counit vs sk-thm-sp-qbar: that asserts an adjunction for raw common-stage operations; the task states the presentation-independent Hom construction for the ambient condensed compactification operations, fixes the finite-stage counit, and descends geometric equations and exceptional coefficient mates.

lem-pur-transport-qbar-common-stage-counit vs det-sp-qbar-finite-descent: that supplies descent of diagrams and operation comparisons, not an induced adjunction, its normalized counit or conjugation to the chosen exceptional coefficient system.

lem-pur-transport-qbar-common-stage-counit vs sk-thm-sfb-qlbar-two-colimit: that compares coefficient categories and gives Hom colimits; it does not construct this adjunction or compare its counit/exceptional mates.

lem-pur-transport-qbar-common-stage-counit vs det-sp-unique-adjoint-coefficients: that is a general conjugation theorem given two adjunction systems; the task first constructs the common-stage adjunction and geometric equations in the condensed category and then applies that conjugation.

## Review by Q64

I read the current main-20261015 item _section.md and proof.md in full, and the recorded master unit's four steps. The route is finite diagonal/DNC purity, coherent normalized-tower reconstruction, rationalization and a finite-field two-colimit, then comparison of fixed adjunctions. The four new statements use that route and retain precisely the data the long proof needed. For their sources I also read the local blueprint statements sk-thm-smooth-purity-general-ring.md, sk-prop-sp-integral-adjunction-bijection.md, sk-prop-sp-rational-hom.md and both sk-thm-sp-qbar files. These are the extracted-argument sources, not a claim that their original short statements already supply every new interface clause.

Assembly step 1 cites sk-thm-existence: its clauses (2)--(4) explicitly preserve the indicated constructible finite-Tor subcategories and restrict the adjunction, so G and the finite system live on the same categories. The finite new statement explicitly supplies the section-action identification, t^A=epsilon F gamma, arbitrary finite-ring coefficient counit equation, orientation/tensor squares, trace reductions and affine-line normalization. I checked its underlying finite input det-sp-finite-general-ring(1)--(3), det-sp-reduction-compatibilities(2)--(3), det-sp-composition-factors, det-sp-purity-bc-factors and thm-pur-finite-reduction-of-purity by their actual statements. I read lem-pur-projection-purity-agreement: it is equality with the integration-transposed map, the fact needed to identify the counit. The displayed coefficient counit equation has domain F_B T_X J_A K and codomain K_B; b inverse has exactly that direction. No equality Dctf=Dbc for a general finite A is used.

Assembly step 2 cites the integral new statement, which explicitly supplies the same ambient left adjoint on condensed categories, the actual morphism R lim gamma_bullet, the equality of its two counit expressions, trace-family agreement, integral geometric coherence and the coefficient equations. I checked sk-lem-integral-models(1)--(3), det-sp-normalized-equivalence, det-sp-tower-gamma(2)--(3), det-sp-integral-direct-image-tower(2), det-sp-integral-adjunction-bijection and det-sp-tower-gluing(1),(3). The tower categories and completed coefficient sheaves agree, with finite scalars restricted before R lim. Noetherian hypotheses hold for the standing finite-type schemes. The finite levels are ell-power levels; the statement explicitly uses the canonical cofinal comparison for uniformizer levels. I also read lem-pur-tower-trace-purity-comparison, prop-pur-adic-reconstruction-trace-coherence and det-sp-field-extension-towers: they supply equality with the simultaneous trace family and comparisons of actual tower adjunctions. Equality of separate reductions of arbitrary derived arrows is never substituted for that equality.

Assembly step 3 cites the rational new statement for the exact four-term Hom chain, its naturality for h/ell^s, its representative independence and the pinned localized counit. Its input det-sp-rational-localized-hom states both essential surjectivity of integral models and the natural E-linear Hom comparison, as well as the compact-support and pullback comparisons. Twists localize by def-coefficient-twists-detailed. The new task carries the check that integral naturality extends E-linearly to fractions, so one does not equate two lattices. I checked the last clause of lem-pur-tower-trace-purity-comparison and the statements thm-pur-rational-and-qbar-purity, prop-pur-rational-purity-trace-coherence and sk-lem-sp-field-extension: these fix the same family and give the geometric identities and transitive finite-field unit/counit comparisons used by the next stage.

Assembly step 4 invokes the common-stage statement only after step 3 gives its finite-stage hypotheses. I checked sk-thm-sfb-qlbar-two-colimit(2)--(4), det-prop-scalar-six-compact-support, det-prop-scalar-six-pullback(1),(3) and sk-prop-sfb-cartesian-coefficients(1). These supply the Hom colimit on the actual condensed categories and identify F, pullback and twists there. The new statement explicitly includes independence of common-stage presentations, naturality, integration counits, and descent of the geometric equations. Its final assertion uses exactly the conjugation and transitivity conclusion of det-sp-unique-adjoint-coefficients. This also accounts for old step 11 rather than silently dropping the comparison with the chosen exceptional adjoint. The theorem sk-thm-sp-qbar alone is not enough: its statement is an adjunction in a differently presented common-stage category without these pinned comparison and coherence clauses.

Assembly step 5 uses det-sp-unique-right-adjoint with letters exchanged: its counit equation is epsilon_G F gamma=t_J, so the comparison is J to G. The new stage statements have this exact fixed pair and counit, hence their comparisons are that same map. The last citation, sk-prop-sfb-cartesian-coefficients(1), really states inverse-image compatibility of coefficient sheaves; it gives a^* Z_l=Z_l,C. A dimension-zero twist/shift is the identity, and a sheaf shifted by [2] has its only cohomology in degree -2. These are substitutions, not a new theorem node.

I checked B--E against the written files. The four new objects have independent, fully quantified statements and empty proofs; all notions introduced by named data cite their defining/interface nodes. Displayed identifications are in derived categories or categories of functors, not merely on each cohomology group. New source places point to exact portions of the parent blueprint and the report below preserves the complete prior reasoning. No new node proves the whole parent or asks a future worker to assume the parent. Each replaces a substantial argument block rather than an elementary equation. Existing generic tools are reused, and no new route replaces the unit. Parent proof_deps is exactly the union of uses. Each citations.json quote is copied verbatim from the statement actually cited; a quote was not repaired by paraphrase. The longest parent step is below 2000 characters and the total is below 3000.

Edge cases: d=0 gives the identity shift/twist and etale adjunction; M=0 or K=0 gives zero Hom groups throughout the tensor/colimit chains; empty X or Y causes no nonempty-support assumption. The finite system allows A=Z/ell^2 and never uses all constructible A-modules being perfect. Taking E=Q_l recovers Z_l and Q_l. Ramified E uses the cofinal uniformizer/ell-power comparison, not an identification of quotient rings with matching indices. Three-field chains require actual transitivity of both source and counit maps. The field condition ell!=p is unchanged; none of the new claims concerns characteristic-p coefficients. No statement dispute was introduced in this repair.

## Unfinished work

The four new nodes intentionally have no proofs: they are the independent stage-1 items the human requested other workers to split. The present item's assembly is complete conditional on them. No Lean file was written and no compiler, Lake or build tool was run. No process script was altered.

## Preservation map and complete argument dossiers

This section preserves all thirteen former proof steps verbatim, with their existing citations. It is the working material for the future workers, not a proof field on any new node. None of the original argument is replaced by a shorter paraphrase. Every stage argument is assigned below; old step 1 also contains the short shared-category setup retained at assembly step 1, old step 10 is the final assembly comparison, and old step 13 is the elementary final substitution. Old step 12 is assigned across all four stages: finite integration identification, coherent integral counit realization, scalar localization and common-stage images.

### Argument dossier for lem-pur-transport-finite-counit-system

Former step 1:

Put $F_{f,\Lambda}=Rf_{!,\Lambda}$ and $J_{f,\Lambda}=f^*_\Lambda(-)(d)[2d]$. We first construct an adjunction $F\dashv J$, with counit $t$, and then compare it to $F\dashv G$, where $G=f^!_\Lambda$ is the restriction in the statement. At finite coefficients the section-action/derived equivalence and the restriction of the localizing adjunction are precisely [sk-prop-sf-rf-shriek-preservation]. At the other stages [det-def-localizing-closure-ctf-equals-bc] gives $\Dctf=\Dbc$, and [sk-thm-existence](2)--(4) supplies this restricted $F\dashv G$. Thus comparison of adjoints will take place on the same categories, not on the entire unbounded derived category.

Cited statements: sk-prop-sf-rf-shriek-preservation, det-def-localizing-closure-ctf-equals-bc, sk-thm-existence.

Former step 2:

For finite $A$, choose $r\geq1$ with $\ell^r A=0$. Clause (3) of [det-sp-finite-general-ring] gives a natural isomorphism $\gamma^A:J_{f,A}\to G_{f,A}$, using the diagonal/DNC orientation; clauses (1)--(2) identify its normalization with scalar extension from $\mathbf Z/\ell^r$. Define $t^A_K=\varepsilon^A_K\circ F_{f,A}(\gamma^A_K)$. The Hom bijection for $G$, composed with the inverse of $\gamma^A$, gives $F_{f,A}\dashv J_{f,A}$ with counit $t^A$. The exponent independence in that node makes this independent of $r$. This covers arbitrary finite $A$, including nonregular rings, without assuming $\Dctf=\Dbc$ there.

Cited statements: det-sp-finite-general-ring.

Former step 3:

The finite coefficient comparisons obey the actual equation $c_{A,B}(K)\circ(\gamma^A_K)_B=\gamma^B_{K_B}$ by [det-sp-reduction-compatibilities](3); its clause (2) gives transitivity for $A\to B\to C$. At $A_{E,n}\to A_{E,m}$ this includes [thm-pur-finite-reduction-of-purity], which also transports orientations, traces and the composition/base-change squares. Finite geometric compatibility is supplied on general finite rings by [det-sp-composition-factors] and [det-sp-purity-bc-factors]. Hence the finite maps have all the required compatibilities before any limit is taken.

Cited statements: det-sp-reduction-compatibilities, thm-pur-finite-reduction-of-purity, det-sp-composition-factors, det-sp-purity-bc-factors.

The normalization obligation from former step 12 also belongs here, at this coefficient stage:

The normalization is fixed at finite level: [lem-pur-projection-purity-agreement] identifies the diagonal purity of the affine-line projection with the exceptional transpose of inverse projection formula followed by projective-line integration restricted to $\mathbf A^1$. At general finite $A$ the specified scalar construction in [det-sp-finite-general-ring](1)--(2) gives this same normalization. The tower counit has exactly these finite counits by [det-sp-tower-gluing](1),(3) and [det-sp-integral-adjunction-bijection]; rationalization and the finite-stage counit construction in Steps 7--9 preserve it. Hence $t$ is the normalized integration counit in every coefficient case, and Step 10 identifies it with $\varepsilon\circ F\gamma$.

### Argument dossier for lem-pur-transport-integral-counit-realization

Former step 4:

Fix $E$. By [sk-lem-integral-models](1)--(3), the integral condensed constructible category is the completed, derived-complete constructible category, and its pullback is the integral pullback used in the tower construction. Use the equivalence with normalized constructible towers in [det-sp-normalized-equivalence]. The normalized tower morphism $\gamma_{f,\bullet}$ exists and is natural by [det-sp-tower-gamma](2)--(3), not merely a compatible family in separate derived categories. The integral compact-support functor of the statement is the same functor as the realized tower functor by [det-sp-integral-direct-image-tower](2). These facts identify both source and left adjoint, including their actions on morphisms.

Cited statements: sk-lem-integral-models, det-sp-normalized-equivalence, det-sp-tower-gamma, det-sp-integral-direct-image-tower.

Former step 5:

Apply [det-sp-integral-adjunction-bijection]. It gives $F_{f,\mathcal O_E}\dashv H_f$, the realized tower counit $\varepsilon^H$, and a natural isomorphism $\gamma^H:J_{f,\mathcal O_E}\to H_f$ equal to $R\varprojlim\gamma_{f,\bullet}(\operatorname{red}K)$. Transfer the adjunction to $J$ by the Hom bijection and set $t_K=\varepsilon^H_K\circ F(\gamma^H_K)$. Its finite reductions are the finite counits and purity maps. This proves the integral explicit adjunction and an actual natural isomorphism; it does not infer uniqueness of a lift from equality of its individual reductions.

Cited statements: det-sp-integral-adjunction-bijection.

Former step 6:

For the geometric compatibilities use the coherent reconstruction assertion [prop-pur-adic-reconstruction-trace-coherence]: the trace and the composition and smooth base-change equations reconstruct together with purity. To fix which integral family is meant, [lem-pur-tower-trace-purity-comparison] identifies the trace-transpose family with the actual tower family $\delta\circ\gamma^H$, where $\delta:H_f\to G_f$ is counit-preserving. Thus the reconstruction's coherent maps, rather than arbitrary lifts of their levels, are used here. For finite $E\subset F$, [det-sp-field-extension-towers](2) identifies coefficient change on these actual tower adjunctions, units, counits and purity maps, and asserts the coefficient-composition identity. These are the required integral compatibilities, including reduction to every uniformizer level.

Cited statements: prop-pur-adic-reconstruction-trace-coherence, lem-pur-tower-trace-purity-comparison, det-sp-field-extension-towers.

The normalization obligation from former step 12 also belongs here, at this coefficient stage:

The normalization is fixed at finite level: [lem-pur-projection-purity-agreement] identifies the diagonal purity of the affine-line projection with the exceptional transpose of inverse projection formula followed by projective-line integration restricted to $\mathbf A^1$. At general finite $A$ the specified scalar construction in [det-sp-finite-general-ring](1)--(2) gives this same normalization. The tower counit has exactly these finite counits by [det-sp-tower-gluing](1),(3) and [det-sp-integral-adjunction-bijection]; rationalization and the finite-stage counit construction in Steps 7--9 preserve it. Hence $t$ is the normalized integration counit in every coefficient case, and Step 10 identifies it with $\varepsilon\circ F\gamma$.

### Argument dossier for lem-pur-transport-rational-hom-counit

Former step 7:

For rational coefficients choose integral representatives $M_0,K_0$. The Hom comparison of [det-sp-rational-localized-hom], applied twice, carries the integral adjunction of Step 5 to
$$\operatorname{Hom}(F_E(M_0[1/\ell]),K_0[1/\ell])\cong\operatorname{Hom}(F_{\mathcal O_E}M_0,K_0)\otimes E\cong\operatorname{Hom}(M_0,J_{\mathcal O_E}K_0)\otimes E\cong\operatorname{Hom}(M_0[1/\ell],J_E(K_0[1/\ell])).$$
Its functor comparisons identify $F_E$ and pullback with the module-category operations in the statement; twists are the localized twists of [def-coefficient-twists-detailed]. Every rational object has such a representative. Naturality extends from integral arrows to $h/\ell^s$ by $E$-linearity of the Hom bijections, so replacing representatives by an isomorphic one gives the same bijection. This proves $F_E\dashv J_E$, with counit the localized $t$. No claim that two arbitrarily chosen lattices are literally equal is used.

Cited statements: det-sp-rational-localized-hom, def-coefficient-twists-detailed.

Former step 8:

The rational purity is the scalar extension of integral purity by [thm-pur-rational-and-qbar-purity], and its trace, composition and base-change coherence are [prop-pur-rational-purity-trace-coherence]. Its identification with the tower family used in Steps 5--7 is the last assertion of [lem-pur-tower-trace-purity-comparison]. The coefficient comparisons carry the rational adjunctions and their units and counits to those over $F$ by [sk-lem-sp-field-extension]; they compose for $E\subset F\subset L$. Consequently the preceding Hom bijections and counits commute with the finite-field transition maps. Taking $E=\mathbf Q_\ell$ also gives the $\mathbf Z_\ell$ and $\mathbf Q_\ell$ cases.

Cited statements: thm-pur-rational-and-qbar-purity, prop-pur-rational-purity-trace-coherence, lem-pur-tower-trace-purity-comparison, sk-lem-sp-field-extension.

The normalization obligation from former step 12 also belongs here, at this coefficient stage:

The normalization is fixed at finite level: [lem-pur-projection-purity-agreement] identifies the diagonal purity of the affine-line projection with the exceptional transpose of inverse projection formula followed by projective-line integration restricted to $\mathbf A^1$. At general finite $A$ the specified scalar construction in [det-sp-finite-general-ring](1)--(2) gives this same normalization. The tower counit has exactly these finite counits by [det-sp-tower-gluing](1),(3) and [det-sp-integral-adjunction-bijection]; rationalization and the finite-stage counit construction in Steps 7--9 preserve it. Hence $t$ is the normalized integration counit in every coefficient case, and Step 10 identifies it with $\varepsilon\circ F\gamma$.

### Argument dossier for lem-pur-transport-qbar-common-stage-counit

Former step 9:

For $\Qlb$, use the condensed finite-stage two-colimit of [sk-thm-sfb-qlbar-two-colimit](2)--(4), together with the rational Hom equivalences of Step 7. The ambient compactification functor and pullback commute with extension from finite $E$: these are [det-prop-scalar-six-compact-support] for the listed maps $E\to\Qlb$ and [det-prop-scalar-six-pullback](1); twists have the coefficient comparisons in [sk-prop-sfb-cartesian-coefficients](1). Choose $M_E,K_E$ over one finite field. Then
$$\operatorname{Hom}(F_{\Qlb}M,K)\cong\varinjlim_{F\supset E}\operatorname{Hom}(F_FM_F,K_F)\cong\varinjlim_{F\supset E}\operatorname{Hom}(M_F,J_FK_F)\cong\operatorname{Hom}(M,J_{\Qlb}K).$$
The middle bijections commute with transition maps by Step 8. Objects, arrows and equalities descend to a common finite stage by the cited two-colimit theorem; hence the displayed bijection is natural and independent of presentations. It proves $F_{\Qlb}\dashv J_{\Qlb}$ with the finite-stage counit. In particular the common-stage construction is related to the condensed category by these equivalences, not equated to it by definition.

Cited statements: sk-thm-sfb-qlbar-two-colimit, det-prop-scalar-six-compact-support, det-prop-scalar-six-pullback, sk-prop-sfb-cartesian-coefficients.

Former step 11:

The finite, integral and rational composition/base-change identities of Steps 3, 6 and 8 persist at the $\Qlb$ stage: each equation is represented by the corresponding equation over a common finite coefficient field, where it is already proved. Their images are equal by functoriality of scalar extension and the Hom colimit. Changing the chosen exceptional adjoint does not change the coefficient equations: [det-sp-unique-adjoint-coefficients] identifies its coefficient mate by conjugation with the unique counit-preserving comparisons, and preserves their coefficient-composition equation. This gives the claimed compatibilities for the particular $f^!$ of [sk-prop-sf-existence], not just for an unnamed isomorphic functor.

Cited statements: det-sp-unique-adjoint-coefficients.

The normalization obligation from former step 12 also belongs here, at this coefficient stage:

The normalization is fixed at finite level: [lem-pur-projection-purity-agreement] identifies the diagonal purity of the affine-line projection with the exceptional transpose of inverse projection formula followed by projective-line integration restricted to $\mathbf A^1$. At general finite $A$ the specified scalar construction in [det-sp-finite-general-ring](1)--(2) gives this same normalization. The tower counit has exactly these finite counits by [det-sp-tower-gluing](1),(3) and [det-sp-integral-adjunction-bijection]; rationalization and the finite-stage counit construction in Steps 7--9 preserve it. Hence $t$ is the normalized integration counit in every coefficient case, and Step 10 identifies it with $\varepsilon\circ F\gamma$.

### Final assembly material retained

Former step 10:

At every stage we now have $F\dashv J$ with its prescribed $t$, and $F\dashv G$ with $\varepsilon$ from Step 1. Apply [det-sp-unique-right-adjoint], with its letters $G,J$ replaced by our $J,G$. It yields the natural isomorphism $\gamma:J\to G$ uniquely characterized by
$$\varepsilon_K\circ F(\gamma_K)=t_K.$$
This also shows that the comparisons already constructed at finite level and through the integral and rational stages are this same isomorphism: each is counit-preserving for exactly the adjunction just constructed. Thus both existence and uniqueness in the item refer to a fixed pair of adjunctions with fixed counits.

Cited statements: det-sp-unique-right-adjoint.

Former step 13:

Finally an etale $f$ is smooth of relative dimension zero, so its displayed twist and shift are $(0)[0]$, giving $f^!\simeq f^*$. For a smooth curve $a:C\to\operatorname{Spec}k$, evaluate $\gamma^{-1}$ at $\mathbf Z_\ell$ and use $a^*\mathbf Z_\ell=\mathbf Z_{\ell,C}$, the coefficient pullback of [sk-prop-sfb-cartesian-coefficients](1). The result is $a^!\mathbf Z_\ell\simeq\mathbf Z_{\ell,C}(1)[2]$. A degree-zero sheaf shifted by $[2]$ has its only cohomology in degree $-2$. The same substitution with dimension $d$ gives the dualizing-complex assertion of the source's Step 4.

Cited statements: sk-prop-sfb-cartesian-coefficients.

## Validation

Initial required dry run: missing report diagnostic, before report creation. Server review_split passed. The first complete delivery dry run rejected one citation quote for being shorter than 40 characters; I replaced it with the full coefficient-pullback clause, verbatim. During the same review I corrected the integral statement to say postcomposition by (gamma^H)^(-1), the well-typed direction for Hom(M,H K) to Hom(M,J K). The source rational Lean packaging was also read: it assumes the compatible finite purity tower and only maps an isomorphism to the rational category, so it supplies no attachment for the new rational adjunction package. Final dry-run and push results follow when complete.
