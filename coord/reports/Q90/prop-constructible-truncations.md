# Q90: finer split of prop-constructible-truncations

## Files written

- dag/nodes/sec-poincare-duality/prop-constructible-truncations.json: item, split; same statement, six assembly steps, under 3000 characters in total.
- lem-pod-completed-scalar-extension-texact: statement-only, unsplit; no Mathlib match. Actual completed integral scalar extension identified with an exact derived functor, with t-exact restriction.
- lem-pod-directed-pair-bounded-tstructure: statement-only, unsplit; no Mathlib match. Abstract directed-pair bounded t-structure and coherent canonical truncation construction.
- lem-pod-isomorphism-pullback-texact-coefficients: statement-only, unsplit; no Mathlib match. Exact t-exact actual integral/rational isomorphism pullback with semilinear scalar and shift coherence.
- report.md and citations.json. The sandbox also retains previous-proof.json, resplit.py, write_report.py and searches.jsonl for continuation; only node files and this report are packaged by deliver.py.

## Attachments

None. WeilConjectures/SixFunctors/ProEtale/Adic/Truncation.lean explicitly omits the rationalized E stage and uses an ambient AdicSheaf derived category at the algebraic closure. Its declarations therefore do not cover the whole item. Sheaf/Paper/ConstructibleTruncations.lean:160-165 states the right existence theorem but its proof is sorry. Neither is an attachment.

The general upstream CategoryTheory.StageSystem.tStructure (CategoryTheory/StageSystem/TStructure.lean:52) and its half/heart equations at lines 86, 89, 94 cover part of the new directed-pair lemma. They do not state its boundedness and canonical functor/map/representative comparison clauses together, so there is no exact full attachment for that node either. I read the whole file and the related FieldCoefficient/ConstructibleTwoColimitTStructure.lean; the latter has a different coefficient-category convention.

## WANTED

None. I read both blueprint snapshots' proposition, the chapter and unit records, Stacks homology.tex, homology-section-truncations (0118, starting line 3612), and derived.tex, derived-remark-truncation-distinguished-triangle (08J5, starting line 4076). The extracted assertions are agent-written intermediate statements from the existing corrected proof, explicitly identified as such in source.place. No Stacks tag is invented for abstract t-structure descent; def-weil-t-structure itself explains that Stacks does not state that abstract theorem.

## Assignment and repaired source issues

The live node initially appeared finished for stage 1: status split, pass review dated 2026-10-17. The required first dry run exposed the newer released repair note coord/repair-notes/prop-constructible-truncations.json: the 2026-10-21 human finer-split decision was applied to this item on 2026-10-22. It requires a short assembly, with the previous arguments available as independent nodes. This delivery answers that note rather than replacing an accepted proof without cause.

The statement, all blueprint import fields, unit/chapter, Lean records and existing maintainer metadata are unchanged. There is no blueprint_update on the item, and main-20261015 has the same statement. The proposition is not the unit's key finiteness lemma, so no unit realization is changed. All searches and the earlier accepted proof route are retained. The new searches were actually run with msearch.py; I read each response. LeanSearch's rate-limit response for the scalar-extension query is recorded as unavailable, not no match. Each new node has Loogle, LeanFinder and Mathlib grep searches, and a second semantic formulation. No compilation, Lean writing, git operation or repository modification was performed by me.

Three old blueprint inferences were already corrected in the retained proof, and remain corrected: truncation need not be a triangulated functor (for a nonzero module M, tau<=0 of M[-1] is zero although (tau<=0 M)[-1] is not); integral truncation need not commute with non-flat reduction (K=A/t in degree zero has derived reduction with nonzero degree -1 as well as degree 0); and triangulated exactness alone does not imply t-exactness (the shift [1] is a counterexample). The statement does not assert these false facts. Its coefficient-tower transition compatibility is between finite coefficient fields, not arbitrary non-flat reduction maps.

## Where the previous work now lives

Previous steps 1-3 remain assembly steps 1-2, citing the existing geometric, integral t-structure, scalar localization and canonical-comparison statements. The finite-torsion observation in old step 2 is the kernel/cokernel calculation of 0118: surviving cohomology is unchanged and the rest zero; this checks the finite condition, while the existing integral theorem supplies the full integral truncation restriction without a Tor assumption. The category-identification theorem supplies compatible witnesses and common local models; these are not inferred from notation.

Previous step 4's actual completed scalar-extension identification, exact tensor functor, cohomological bound preservation and integral restriction are the new completed-scalar-extension lemma. Rationalization of bounds and coherent truncation comparison then remain a short application of the existing exact scalar-extension and t-exact comparison statements (assembly step 3).

Previous steps 5-6, including independence of common-field representatives, natural maps, distinguished triangles, orthogonality, both shift inclusions and boundedness, are the new abstract directed-pair lemma (assembly step 4). This is a general construction with all hypotheses explicit, not a renamed clause about this one Y.

Previous step 7 remains the literal cohomology functor definition (assembly step 5). At a rational stage it is a heart object, not an unsupported identification with an arbitrary ambient E-sheaf category.

Previous steps 8-9's completed-to-termwise pullback comparison, integral exactness and t-exactness, rational extension on fractions, and coefficient/shift coherence are the new isomorphism-pullback lemma. Previous steps 10-11 are already the statement of the existing post-note lem-a1-texact-coefficient-stage-descent, created by Q112 on 2026-10-21: in addition to exact/t-exact descent, it explicitly states the uniqueness, finite-stage representability and scalar compatibility of both truncation comparisons and H^i. It has only definition statement dependencies, so its use creates no circular dependence on this item. Reusing this fourth independent argument avoids a duplicate new node. The gate explicitly counts cited nodes landed since the repair-note baseline alongside newly delivered nodes; this delivery adds three and cites that existing fourth argument.

## Not duplicates

lem-pod-completed-scalar-extension-texact vs lem-weil-finite-free-completed-scalar-comparison: the existing node gives the derived ordinary-tensor/strict-completion isomorphism and finite-freeness. The new node makes the actual functor an exact t-exact functor on the full integral categories, with its induced shift structure; it carries the old step's remaining abelian/derived/restriction argument.

lem-pod-completed-scalar-extension-texact vs lem-weil-integral-scalar-extension-constructible: the existing node proves target membership only; it does not give exactness or cohomological bound preservation.

lem-pod-completed-scalar-extension-texact vs lem-per-adic-common-stage-truncations: the latter assumes separated finite-type schemes and concludes rational/common-stage truncations. The new node works integrally on every noetherian finite-dimensional scheme and concludes t-exactness of the completed functor, without assuming separation or a base field.

lem-pod-directed-pair-bounded-tstructure vs lem-sbc-coherent-pair-functor-descent: the existing node descends additive functors and transformations; it states no t-structure, orthogonality, truncation axiom or boundedness. The new statement supplies these for an arbitrary small directed poset and a specified triangulated pair category.

lem-pod-directed-pair-bounded-tstructure vs lem-a1-texact-coefficient-stage-descent: the existing node ASSUMES the pair bounded t-structures and finite-stage canonical truncations, while the new node constructs exactly that input. Its independent existence statement cannot be obtained by applying the existing conditional transport theorem.

lem-pod-directed-pair-bounded-tstructure vs lem-per-adic-common-stage-truncations: the latter is about separated finite-type schemes with a specific coefficient system; the new abstract construction applies to arbitrary directed diagrams, including this item's non-separated Y.

lem-pod-isomorphism-pullback-texact-coefficients vs lem-weil-isomorphism-derived-pullback: the existing node supplies the derived-to-termwise isomorphism and membership; the new statement supplies the exact shift structure, preservation of both integral/rational halves, and exact semilinear scalar comparisons with all tower equations.

lem-pod-isomorphism-pullback-texact-coefficients vs lem-weil-isomorphism-comparison-scalar-extension: the existing square identifies specified INTEGRAL comparison maps; it does not state t-exactness or transport them to all rational morphisms with shift/tower coherence.

lem-pod-isomorphism-pullback-texact-coefficients vs lem-a1-texact-coefficient-stage-descent: the existing generic theorem ASSUMES the integral t-exact functors and exact coherent scalar comparisons; the new node verifies those assumptions for the actual completed pullback. It does not repeat the conclusion about truncations or common-stage cohomology.

lem-pod-isomorphism-pullback-texact-coefficients vs lem-per-adic-stratified-pullback-texact: the latter assumes separated finite-type schemes; this new statement permits every isomorphism of noetherian finite-dimensional schemes and retains the actual integral construction and fractional-map normalization.

The whole DAG was searched for finite-free scalar extension, t-exactness, directed/pair t-structures and isomorphism pullback; blueprint_refs.py searches included integral scalar extension, pair category, t-structure, truncation, isomorphism and coherent pair. Same-tag checks produce no Stacks pairs for the new nodes since their actual sources are precise places in the blueprint's argument, not a tag falsely borrowed from a nearby fact. The chapter prefix and blueprint.from ancestor/place/via are filled on all three nodes.

## Review by Q90

I read the original master proof and the current main proposition; the former is the actual source of the route and the latter is the current statement. I read the statement of every node used by all six assembly steps; citations.json contains its exact statement rather than a paraphrase. In step 1 the finite-type-over-noetherian result and finite-type fibre bound apply to Y -> Spec k, whose base is quasi-compact and noetherian. The comparison theorem explicitly identifies both integral definitions, with compatible witnesses, under precisely the resulting noetherian, finite-dimensional and invertible-l hypotheses. Y need not be separated. I did not use the nearby separated adic theorems by silently adding a hypothesis.

In step 2 I checked that the integral theorem gives ambient restrictions and canonical triangles for every integral object, while its additional reduction comparison has a separate Tor hypothesis. The localized theorem gives the bounded rational halves and integral comparison, the linear-scalar-localization theorem explicitly supplies exactness of Q, and lem-pod-texact-truncation-comparison therefore identifies the canonical maps. The standard-pair definition agrees exactly with those halves. In step 3 the new scalar-extension statement supplies integral t-exactness; its rational bound argument is simply to choose an integral object isomorphic to the given rational half-object and apply integral t-exactness. The existing scalar-extension proposition supplies exact shifts, literal identity transition and unit/pentagon associators. The existing general truncation-comparison lemma supplies naturality and identity/composition, not just objectwise isomorphisms.

For the new scalar node I checked the intended argument against lem-weil-finite-free-completed-scalar-comparison: S is finite free over R and the displayed strict-tower object is naturally ordinary derived tensor in D(S). With an R-basis, forgetting S identifies sheaf tensor with a finite direct sum; kernels and cokernels are preserved. The exact-functor homology node supplies bound preservation, the derived-triangulated node supplies shifts and triangles, and the constructible scalar-extension node supplies target membership. This requires more than knowing the definition of flatness. I checked E=L, ramified L/E, K=0, and torsion cohomology K=A/t. No step claims that reduction modulo a uniformizer is t-exact. The new statement is about the actual completed integral functor, and its isomorphism is in the derived category, not merely a per-degree cohomology assertion.

In step 4 I checked all hypotheses of the new directed-pair statement: FinExt is small in the size convention, nonempty and directed, exact/t-exact transitions and coherent associators come from step 3, and the algebraically-closed-coefficient definition supplies exactly its pair category, common-stage triangles, and shifts. For the new general statement, I tested a one-stage diagram, a constant diagram, zero categories and nonfaithful transition functors. No faithfulness is needed: for orthogonality move representatives and bounds to a common stage, where the morphism is zero; a representative's finite bounds give boundedness. The uniqueness of the truncation comparison with its canonical map gives the associator equations, and conjugation on arrows respects passage to later stages. Thus this statement includes the substantive old steps 5-6, rather than inferring all axioms from functor descent alone. Its source is explicitly the agent's extraction, not a fictitious Stacks theorem.

In step 5 the sign [i] is the cohomological convention moving degree i to degree zero. Its finite/integral agreement uses the kernel/image cohomology definition, and no ambient rational sheaf identification is asserted. In step 6 I checked that the new isomorphism statement provides exactly the integral, rational and coherent comparison hypotheses of lem-a1-texact-coefficient-stage-descent, whose pair-t-structure hypotheses are supplied by steps 2-4. Its full statement gives BOTH truncation comparisons, their canonical maps, their coefficient coherence and their composite with shifts. Its representative action beta_target^{-1} F(u) beta_source is exactly the recorded actual common-stage pullback. This avoids replacing a specified operation by an arbitrary isomorphic functor.

For the new isomorphism node I read the completed-pullback definition, the derived-to-termwise theorem, the site-equivalence theorem, semilinear-localization statement and scalar-extension proposition. The inverse-image equivalence preserves all small limits, so it transports the completed coefficient ring, not just constant coefficients. Transporting module actions gives an exact module equivalence. The canonical derived comparison lets us use its termwise shift structure and cohomology calculus for the actual completed pullback. The raw rational halves then give rational t-exactness; rational transport gives exactness. For E subset L, the existing integral-operation comparison and the scalar-extension proposition supply the actual integral tensor/completion comparison, including its shift and tower equations. Semilinear localization applies since the nonzero image of varpi_E is invertible in L, even when varpi_E differs by a ramification power and unit from varpi_L. It preserves whiskering, transformation equations and shifts, and its fraction formula is exactly the prescribed rational action. I checked g=id, X=empty, E=L and ramified L/E. No inference from triangulated exactness alone to t-exactness is left.

The four independent units of work are the three new statements and the existing generic coefficient-stage descent theorem. None of the new nodes states a truncation/cohomology clause of the original scheme-specific item: they provide the intermediate exact/t-exact functors and an abstract t-structure construction on arbitrary diagrams. All three are statement-only and have empty proof/proof_deps/proof_origin. The intended arguments above explain how another worker can take them up; they are deliberately not hidden inside their statements. The assembly has no step over 2000 characters, and its entire text is under 3000. Only stage 1 was performed. The initial stale-assignment diagnosis was corrected as soon as the dry run exposed the newer released repair note.

## Unfinished work

Proofs of the three new statement-only nodes are the intended next-stage-1 items. They are mathematically supported by the arguments above. No requested Lean work is pending, since no Lean work was authorized.

## Preserved previous proof

The following is the complete pre-repair proof text, retained for traceability so no previous argument is lost by the short assembly. Its steps are assigned above to existing or new nodes; it is not the new item's proof field.

### Previous step 1

Write $A=\mathcal O_E$, $R=\widehat{\mathcal O}_{E,Y}$, and $\mathcal C_A=D^b_c(Y,A)$. The scheme $\operatorname{Spec}k$ is noetherian and quasi-compact: a field has just the ideals $(0)$ and $(1)$. Apply [lem-weil-pbc-finite-type-over-noetherian] to $Y\to\operatorname{Spec}k$. Apply [lem-fin-finite-type-fibre-dimension-bound] to the same morphism; its only fibre is $Y$, so $Y$ is finite-dimensional. Finally $\ell$ is a unit in $k$ because $\ell\ne p$, and its image is a unit in each local ring of $Y$. All hypotheses of [lem-weil-pbc-integral-stratified-perfect-characterization] now hold. Its explicit comparison clause identifies the full subcategory of [def-weil-derived-complete-integral-detailed] with the completed bounded constructible category used by the integral and localized t-structure theorems, with the same ring sheaf and reduction functors. In particular the compatible etale-origin witnesses and uniform local models required there are supplied by this cited theorem; they are not inferred merely from the notation $D^b_c$.

Uses: def-weil-derived-complete-integral-detailed, lem-weil-pbc-finite-type-over-noetherian, lem-fin-finite-type-fibre-dimension-bound, lem-weil-pbc-integral-stratified-perfect-characterization.

### Previous step 2

At a torsion coefficient level, use the standard t-structure of [def-sbc-standard-tstructure-derived-category]. Canonical upper truncation replaces the cutoff term by a kernel and canonical lower truncation replaces its cutoff term by a cokernel, as in Stacks Tag 0118 (homology-section-truncations). Their surviving cohomology sheaves are exactly the original ones and the other cohomology sheaves are zero; the upper calculation is [lem-weil-pbc-truncation-cohomology], and the lower calculation follows directly by taking $\operatorname{coker}d^{m-1}$ in degree $m$. Thus boundedness and the finite partitions in [def-weil-finite-torsion-constructibility] survive truncation. The standard triangles restrict to this full triangulated subcategory. At the integral stage, apply [prop-weil-pbc-integral-tstructure] after step 1: it supplies the bounded t-structure, both ambient canonical truncation restrictions, their maps and their distinguished triangles on all of $\mathcal C_A$. This application uses no flat-cohomology assumption. It also does not identify the reductions of an arbitrary integral truncation with the truncations of the reductions; such an identification has the extra Tor hypothesis recorded in the cited integral theorem.

Uses: def-sbc-standard-tstructure-derived-category, lem-weil-pbc-truncation-cohomology, def-weil-finite-torsion-constructibility, prop-weil-pbc-integral-tstructure.

### Previous step 3

Use the raw scalar localization of [def-weil-rationalization-karoubi], so that $\mathcal C_E=\mathcal C_A[1/\varpi_E]$ has the same objects and localized Hom groups; no idempotent completion is involved. By step 1 the categories and localization functor are exactly those in [prop-weil-localized-tstructure]. That theorem gives the bounded t-structure on $\mathcal C_E$, its natural truncation comparisons $\tau_E^{\le m}QK\cong Q\tau_A^{\le m}K$ and $\tau_E^{\ge m}QK\cong Q\tau_A^{\ge m}K$, and t-exactness of $Q$. Apply [lem-pod-texact-truncation-comparison] to the t-exact exact functor $Q$: its characterizing equations identify the canonical truncation maps with the localized integral maps under these comparisons. The resulting truncation triangle is the image of the integral one, since $Q$ is exact and its two end objects lie in the required halves. This identifies the finite coefficient-field t-structure with the rational standard pair of [def-weil-constructible-standard-tstructure].

Uses: def-weil-rationalization-karoubi, prop-weil-localized-tstructure, def-weil-constructible-standard-tstructure, lem-pod-texact-truncation-comparison.

### Previous step 4

Let $E\subset L$ be finite coefficient fields, and put $S=\widehat{\mathcal O}_{L,Y}$. By [lem-weil-finite-free-completed-scalar-comparison], $S$ is finite free over $R$ and, for a derived-complete $K$, the actual integral scalar extension is naturally $K\otimes_R^L S$. Choose an $R$-basis of $S$ solely to check exactness: after forgetting the $S$-action, tensoring any module sheaf with $S$ is a finite direct sum of copies of that module sheaf. Finite direct sums preserve kernels and cokernels, so this tensor functor is exact. Apply [lem-sp-exact-functor-preserves-homology] to obtain $\mathcal H^r(K\otimes_R^L S)\cong\mathcal H^r(K)\otimes_R S$ naturally. It preserves both cohomological half-categories, and [lem-weil-integral-scalar-extension-constructible] supplies membership in the target integral category. Hence integral scalar extension is t-exact; after localization the same is true of $-\otimes_E L$, since the rational halves are the isomorphism closures of integral halves. This rational functor is triangulated by [lem-weil-scalar-extension-exact-triangulated]. Apply [lem-pod-texact-truncation-comparison] to this t-exact triangulated functor to obtain the two natural truncation isomorphisms, compatible with their canonical maps. Its identity, composition and natural-transformation clauses apply to the canonical scalar associators of [lem-weil-scalar-extension-composition]. The unit and pentagon equations for these associators are explicitly supplied by [prop-weil-pbc-scalar-extension]; the comparison lemma preserves those equations, giving coherence over the coefficient-field tower. These are finite field extensions, not non-flat reductions $A/\varpi^{n+1}\to A/\varpi^n$.

Uses: lem-weil-finite-free-completed-scalar-comparison, lem-sp-exact-functor-preserves-homology, lem-weil-integral-scalar-extension-constructible, lem-weil-scalar-extension-exact-triangulated, lem-weil-scalar-extension-composition, def-weil-constructible-standard-tstructure, lem-pod-texact-truncation-comparison, prop-weil-pbc-scalar-extension.

### Previous step 5

Apply [lem-sbc-coherent-pair-functor-descent] to the additive finite-stage categories and the upper truncation functors, with the coherent scalar comparisons supplied by step 4. The pair category is exactly [def-weil-algebraically-closed-coefficients]. It gives $\tau^{\le m}(E,K)=(E,\tau_E^{\le m}K)$; an arrow represented by $u$ over $L$ is sent to $\tau_L^{\le m}(u)$ conjugated by the step-4 scalar comparisons. The cited lemma proves independence of the representative and common field, and preservation of identities and composition. Apply it again to lower truncation. The step-4 comparisons preserve the canonical truncation maps, so these maps are compatible transformations and descend by the same lemma. The finite-stage truncation triangles then give triangles in the pair category, distinguished by its stated common-stage convention. This constructs the truncations, maps and triangles with every common finite-field presentation.

Uses: lem-sbc-coherent-pair-functor-descent, def-weil-algebraically-closed-coefficients.

### Previous step 6

For $\overline{\mathbf Q}_\ell$, take the two standard classes of [def-weil-constructible-standard-tstructure], namely objects isomorphic to finite-stage nonpositive or nonnegative objects. Shifting such a representative proves the two shift inclusions in [def-weil-t-structure]. For orthogonality, replace the source and target by representatives in degrees $\le0$ and $\ge1$, and extend both to one common field. By step 4 these bounds persist under every further field extension. The finite-stage Hom group is therefore zero at every such stage, and its directed colimit, the Hom group of [def-weil-algebraically-closed-coefficients], is zero. The triangle constructed in step 5 has its end terms in the required halves, giving the truncation axiom. Finally an object $(E,K)$ has upper and lower bounds already over $E$ by step 3; the same bounds work in the common-stage category. This proves all t-structure axioms and boundedness, rather than assuming that functorial descent alone proves them.

Uses: def-weil-constructible-standard-tstructure, def-weil-t-structure, def-weil-algebraically-closed-coefficients.

### Previous step 7

For either field stage define $\mathcal H^i$ to be the composite $K\mapsto(\tau^{\ge i}\tau^{\le i}K)[i]$ displayed in the statement. The truncation maps are functorial, so this is a functor. Its value lies in the heart: before shifting it has only degree $i$, and the cohomological shift $[i]$ moves that degree to zero. At the integral and torsion stages it is the degree-$i$ cohomology sheaf of [def-weil-derived-cohomology-sheaves], placed in degree zero, by the kernel/image descriptions; at a field stage it is its rationalized or common-stage heart object. Thus no identification of an abstract rational heart with an ambient category of $E$-sheaves is assumed.

Uses: def-weil-derived-cohomology-sheaves.

### Previous step 8

Let $h:Y\xrightarrow{\sim}Y$ be a scheme automorphism. By [lem-weil-isomorphism-derived-pullback], with the completed integral coefficient sheaf, the actual integral pullback of [def-weil-derived-pullback-tensor-hom] is naturally isomorphic to termwise $h^{-1}$ on every object of $\mathcal C_A$, and its values remain in $\mathcal C_A$. This is the entire completed-derived-to-termwise comparison; no cone or K-flat argument is needed here. By [lem-weil-proetale-isomorphism-inverse-image], $h^{-1}$ is an exact equivalence of sheaves, with the compatible coefficient identifications. After transporting the module action along the completed coefficient isomorphism, it is also an exact equivalence on module sheaves. By [lem-sp-exact-functor-preserves-homology], $\mathcal H^r(h^{-1}K)\cong h^{-1}\mathcal H^r(K)$, so it preserves both integral half-categories. The termwise derived functor is triangulated by [lem-sf-exact-functor-derived-triangulated]. Use its shift structure on the naturally identified integral pullback. After step 1's identification of integral conventions, [prop-weil-pbc-rational-transport] makes its coefficient-linear rational extension triangulated. Its pure-tensor action is the prescribed action in [def-weil-derived-pullback-tensor-hom], so it is the actual $Lh_E^*$. The rational halves are isomorphism closures of integral halves, hence this functor is t-exact too. Apply [lem-pod-texact-truncation-comparison] to obtain the natural isomorphisms $\alpha_{E,m}^{\pm}:Lh_E^*\tau_E^{\le m,\ge m}\cong\tau_E^{\le m,\ge m}Lh_E^*$, preserving the canonical maps.

Uses: lem-weil-isomorphism-derived-pullback, def-weil-derived-pullback-tensor-hom, lem-weil-proetale-isomorphism-inverse-image, lem-sp-exact-functor-preserves-homology, lem-sf-exact-functor-derived-triangulated, prop-weil-pbc-rational-transport, lem-pod-texact-truncation-comparison, def-weil-constructible-standard-tstructure.

### Previous step 9

Write $F_E=Lh_E^*$ and $T_{L/E}=-\otimes_E L$. The first comparison of [lem-pur-integral-operations-scalar-extension] applied to $h$ gives an integral natural isomorphism between the integral versions of $T_{L/E}F_E$ and $F_LT_{L/E}$, with identity and tower equations. Its hypotheses hold by step 1 and the constructible membership in step 8. Apply [lem-pur-semilinear-scalar-localization] with $R=\mathcal O_E$, $S=\mathcal O_L$, $t=\varpi_E$, $u=\varpi_L$, and the inclusion $R\to S$. The two integral composite functors are semilinear for this inclusion, since scalar extension transports the module action and inverse image preserves it. The image of $\varpi_E$ is nonzero in the field $L=S[1/\varpi_L]$, hence invertible. The lemma extends the integral comparison to $\beta_{L/E}:T_{L/E}F_E\xrightarrow{\sim}F_LT_{L/E}$ on all rational morphisms and preserves its identity and tower equations, including whiskering across different valuation rings. Its fraction formula agrees with the pure-tensor rules of [def-weil-rationalization-karoubi] and [def-weil-derived-pullback-tensor-hom], so these extensions are the actual rational composite functors.

Uses: lem-pur-integral-operations-scalar-extension, lem-pur-semilinear-scalar-localization, def-weil-rationalization-karoubi, def-weil-derived-pullback-tensor-hom.

### Previous step 10

Fix either truncation $\tau$ and its cutoff. Write $T=T_{L/E}$ and $c_K:T\tau_EK\xrightarrow{\sim}\tau_LTK$ for the scalar comparison of step 4. Step 8 gives $\alpha_E:F_E\tau_E\xrightarrow{\sim}\tau_EF_E$. All $T,F_E$ are t-exact triangulated functors. Apply the natural-transformation clause of [lem-pod-texact-truncation-comparison] to $\beta:TF_E\Rightarrow F_LT$ from step 9, and its composition clause to both composites. At every $K$ this gives
$$
 \alpha_{L,TK}\circ F_L(c_K)\circ\beta_{\tau_EK}
 =\tau_L(\beta_K)\circ c_{F_EK}\circ T(\alpha_{E,K}).
$$
Both sides map $TF_E\tau_EK$ to $\tau_LF_LTK$. For the families $\Phi_E=F_E\tau_E$ and $\Psi_E=\tau_EF_E$, their scalar comparisons are respectively $b_K=F_L(c_K)\circ\beta_{\tau_EK}$ and $d_K=\tau_L(\beta_K)\circ c_{F_EK}$. Thus the displayed equation is precisely $\alpha_LT\circ b=d\circ T\alpha_E$, the transformation hypothesis of [lem-sbc-coherent-pair-functor-descent]. The unit and tower hypotheses for $b,d$ follow from steps 4 and 9 and the lemma's composition clause. Descent sends $\alpha$ and its inverse to mutually inverse transformations. Its composition clause identifies the descended families with the composites of the actual common-stage pullback of [def-weil-derived-pullback-tensor-hom] and the truncation of step 5: their representative formulas use exactly $\beta$ and $c$. This proves both truncation comparisons over $\Qlb$.

Uses: lem-pod-texact-truncation-comparison, lem-sbc-coherent-pair-functor-descent, def-weil-derived-pullback-tensor-hom.

### Previous step 11

The integral and rational pullback functors commute with shifts by the triangulated structures established in step 8. For the algebraically closed stage use the final particular assertion of [prop-weil-pbc-descent-functors]: the scalar-compatible family $(Lg_E^*)_E$ descends to an exact functor. Its representative formula is precisely the pullback formula of [def-weil-derived-pullback-tensor-hom]; step 1 identifies its integral and rational conventions, and [def-weil-algebraically-closed-coefficients] identifies the same pair category. Thus this assertion supplies shift compatibility for the actual common-stage pullback, without asserting it for arbitrary natural comparisons. Compose the shift comparison with the two truncation comparisons of steps 8 and 10, at cutoff $i$. For $\Lambda=E$ or $\Qlb$ this gives
$$
 Lh^*((\tau^{\ge i}\tau^{\le i}K)[i])\cong(\tau^{\ge i}Lh^*\tau^{\le i}K)[i]\cong(\tau^{\ge i}\tau^{\le i}Lh^*K)[i].
$$
By step 7 this is the required natural isomorphism $Lh^*\mathcal H^i(K)\cong\mathcal H^i(Lh^*K)$.

Uses: prop-weil-pbc-descent-functors, def-weil-derived-pullback-tensor-hom, def-weil-algebraically-closed-coefficients.
