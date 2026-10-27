# Repair of the returned Q142 delivery

## Files written

- dag/nodes/sec-six-functors/lem-sf-package-exceptional-coherence-realization.json: unchanged statement and statement dependencies; eight-step assembly, 2413 characters, citing existing results directly.
- dag/nodes/sec-six-functors/lem-sf-package-finite-exceptional-domain.json: statement, unsplit, no Mathlib match. Narrowed to the genuine preservation/restriction argument of returned step 3; it no longer includes compactification geometry.
- dag/nodes/sec-six-functors/lem-sf-package-qbar-adjunction-map-descent.json: statement, unsplit, no Mathlib match. The genuine common-field map-descent argument of returned step 7, with explicit colimit Hom bijection, representative formulas and hypotheses on finite-stage comparisons.

Two new nodes, zero Mathlib leaves. The rejected coefficient-passage and common-stage-evaluation-coherence children are omitted; their versions and all their recorded searches survive in the sandbox archive returned-version.json and in the prior report retained below. citations.json now covers every citation in all eight parent steps. No Lean, repository or launcher file was changed. There was no running delivery when the repair began; the initial required dry run of the retained version exited OK (not pushed) at 081f90895cf. That mechanical success did not discharge the mathematical return.

## Attachments

None. The exact parent blueprint-tag search in lean/WeilConjectures found no declaration giving the whole item. Searches by exceptional adjunction, common-stage adjunction and compactification bounds found only components. In particular, UpperShriekFiniteness.lean:247 defines AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction and its preservation lemmas, and AmbientAdjointClass.lean constructs the relative adjunction. The definition alone does not give every clause of the new finite lemma (including geometric preservation and compactification cocycle), still less the complete item. No transitive Lean-closure claim is made from source text alone. The Adic upper-shriek interface likewise does not attach the entire parent or the conditional common-field normalization lemma.

## WANTED

None for this repair. All sources used are archived blueprint sources; there is no new Stacks-source claim or forbidden SGA citation.

## What was wrong and what changed

The maintainer's D1/D2/C5 finding is accepted. The first attempt divided nine steps into three blocks, but the coefficient block merely combined existing coefficient theorems and the final block combined evaluation theorems with the parent's own coherence conclusion. Their extraction created no independent argument. Both rejected blocks are removed. Old steps 4, 5, 6, 8 and 9 now remain as short direct citation steps 3, 4, 5, 7 and 8 of the parent, precisely as requested. No shortened restatement of either block remains as a new node.

For returned point (1), finite-exceptional-domain is narrowed from old steps 1--3 to old step 3 only. A new geometry node would duplicate the geometric paragraph of the existing lem-weil-boundary-etale-adjunction-restriction, discovered in the whole-DAG search. Parent step 1 reuses that paragraph, prop-nagata-compactification-category for the expressly quasi-compact open immersion, and lem-kun-dimension-finite-type for X,Y. The boundary lemma's statement defines Noetherian as locally Noetherian and quasi-compact and states quasi-separatedness; this is exactly the qcqs hypothesis needed for Nagata. Its geometric dimension assertion holds for every compactification. Thus geometry is assigned to an existing node rather than copied into a third new one. The released note requires at least two genuine new nodes; the two delivered nodes meet that count. Nothing from old steps 1--2 is discarded.

For returned point (2), all finite-quotient formulas, the coherent integral derived-limit realization and rational passage are supplied by their existing named theorems directly in the parent. The finite unit/counit equations and quotient cocycle are cited from lem-coef-finite-exceptional, not reissued as a new theorem. Integral residue-Tor control and the uniform output interval are cited from their two existing nodes.

For returned point (3), only common-field descent is extracted. The new node is conditional on the scalar-compatible finite-stage adjunction maps and evaluations, and concludes explicit presentation-independent formulas in the common-stage category. It does not restate the field dual formula, operation preservation at every coefficient stage, Weil equivariance, or the parent's final coherence paragraph. The general finite/integral Hom and finite-extension comparison results remain in parent step 7; fix-prop-coherence remains the sole final coherence citation in step 8.

## Not duplicates

lem-sf-package-finite-exceptional-domain vs thm-sf-ambient-adjoint-class: the existing theorem gives the relative Hom bijection for bounded-below objects of etale origin, not preservation/restriction on finite-Tor constructible subcategories; that preservation argument is the new obligation.
lem-sf-package-finite-exceptional-domain vs thm-sf-preservation-class: the existing theorem gives exceptional preservation and explicit intervals, not the left-functor preservation, restriction of both Hom arguments, and compactification-normalized restricted adjunction.
lem-sf-package-finite-exceptional-domain vs lem-weil-boundary-etale-adjunction-restriction: the latter concerns the ambient ordinary etale adjunction on D+ and comparison units, not the pro-etale finite-Tor constructible adjunction. Its geometric paragraph is reused in the parent instead of duplicated.
lem-sf-package-qbar-adjunction-map-descent vs thm-coef-qbar-verdier: the latter gives actual Verdier anti-equivalence and the exceptional dual formula; the new conditional statement isolates explicit colimit Hom bijections and representative unit/counit/evaluation formulas for any specified coherent finite-stage data, the argument of its proof rather than another assertion of Verdier duality.
lem-sf-package-qbar-adjunction-map-descent vs lem-pur-transport-qbar-common-stage-counit: the latter assumes a smooth map, condensed coefficient categories and a purity adjoint with integration counit and purity/base-change equations. The new node concerns ordinary pro-etale coefficient-passage categories, every separated finite-type f, and the exceptional adjunction together with internal-Hom evaluation; it cannot be obtained by one-line specialization to that smooth condensed assertion.
lem-sf-package-qbar-adjunction-map-descent vs lem-sf-qbar-localization-common-stage: localization concerns j_! adjoint j* and i* adjoint i_* and vanishing, not general f! adjoint f^! and internal-Hom evaluation.
lem-sf-package-qbar-adjunction-map-descent vs lem-sf-tensor-comparison-localization-descent: the latter descends an additive tensor comparison into point perfect complexes, not an exceptional adjunction or the displayed colimit Hom bijection.
lem-sf-package-qbar-adjunction-map-descent vs lem-sf-rational-direct-image-adjunctions and def-weil-common-stage-derived-direct-image: those concern pullback/right direct image, with additional finite-field model data for the latter; they do not give compact-support/exceptional map descent or evaluation. The rational node expressly leaves common-stage quotient adjunction to its consumer.

Whole-DAG statement/title searches, the retained earlier searches and blueprint_refs.py searches for compactification dimension, adjunction restriction and common stage adjunction were read. The only blueprint hit for adjunction restriction was def-sfb-modobj-restrict-coextend-adjunction, a monoid-object restriction/coextension adjunction, not this statement. No blueprint duplicate was found. Both new nodes name prop-functor-package as their nearest blueprint ancestor and the exact exceptional-adjunction sentence, identifying returned steps 3 and 7 in from.place. The parent retains its existing blueprint reference. Neither new source introduces a Stacks tag shared with an existing node.

## Mathlib searches

I read the complete retained searches.jsonl before reusing searches. Changed statements were searched afresh through the required msearch.py command, never by unlogged invented queries. For finite restriction, LeanFinder was run with both 'A class relative compact support adjunction restricts to bounded constructible finite Tor sheaves because both functors preserve those full subcategories' and 'Finite Tor constructible preservation of compact support and exceptional inverse image yields the restriction of the class relative adjunction'. LeanSearch, Loogle restrictFullyFaithful, and the CategoryTheory grep are in its node with exactly their logged query text. For common-field descent, both LeanFinder phrasings, the LeanSearch query, Loogle counit, and CategoryTheory grep are recorded exactly in its node. All these fresh services answered; old unavailable results remain in the historical log and report, not converted into evidence of absence.

The strongest Mathlib candidate was CategoryTheory.Adjunction.restrictFullyFaithful. I read Mathlib/CategoryTheory/Adjunction/Restrict.lean:36--84: it assumes an ambient adjunction and commuting fully faithful inclusions, and constructs the restricted adjunction. It neither proves finite-Tor preservation for Rp_*j_! and the transported exceptional functor nor supplies the class-relative starting domain or compactification cocycle, so the new finite statement is not a Mathlib leaf. It can be useful when that node is proved. The other finite hits are open restriction of structure-sheaf modules or condensed locally constant adjunctions, different coefficients and operations. The common-field search found ordinary module change-of-rings counits, condensed free/forgetful maps and generic category adjunction identities, not the finite-stage sheaf pair construction. The grep Verdier hits are bibliographic references in triangulated theory. Geometry searches found properness definitions and compactness of schemes but no Nagata compactification/dimension package; no new geometry node is consequently issued. No query is recorded unless it is in the actual search log.

## Review by Q142

I read the full return entry, retained item and report, current main item, released keep_plan note, AGENTS, worker brief, GOAL, stages/1-dag, SETUP's three levels and delivery-errors B--E. The current main parent has the original nine-step argument; only proof, proof_deps and split_report differed from the retained rejected parent, so I based the repair on the current main record and retained every other field, including the statement, statement dependencies, blueprint/import history and maintainer-owned tool approvals. The new generic geometry tool use is declared only in split_report for review, not written as a new maintainer approval.

I read main-20261015 prop-functor-package.proof.md, whose exceptional-adjunction sentence cites the finite, integral and rational coefficient results and whose final sentence cites fix-prop-coherence. I also read main-20261015 thm-sf-ambient-adjoint-class.proof.md, thm-coef-qbar-verdier.proof.md, prop-coef-integral-exceptional-adjoint.proof.md and fix-prop-coherence.proof.md, together with the complete live statements of every node cited in the eight assembly steps. These are agent-written proofs, so proof_origin remains agent. Both new nodes are extracted from the actual argument, not promoted external theorems; their full handoff proofs are preserved below, outside their statement-only JSON.

Step 1 uses the boundary lemma only for its explicitly stated geometric paragraph: every ambient compactification is finite type with finite nonnegative bound; Y is Noetherian and quasi-separated. It then invokes Nagata with qcqs Y, separated finite-type f, obtaining the required quasi-compact open j and proper p. The finite-type dimension theorem gives finite bounds for X,Y. I corrected an earlier draft which took quasi-compactness of j from the boundary lemma: that lemma's j is merely stated open, so the explicit Nagata citation is essential. Empty dimensions are minus infinity in the cited definition, hence bounded by zero; no empty maximum occurs. The node supplies no ambient pro-etale adjoint claim.

Step 2 cites the narrowed finite-domain node for exactly preservation and the restricted Hom bijection with units, counits and compactification cocycle. Its handoff uses thm-sf-ambient-adjoint-class for etale-origin Hom bijections including bounded constructibles, lem-trf-open-ctf for j_! preserving constructibility and Tor interval, cor-sf-direct-image-ctf-proetale at the proper map p with source-dimension bound d for p_*, and thm-sf-preservation-class(2) for the right functor. Proper p is separated finite type, Y is separated, and all geometric hypotheses are present. Restricting the bijection between full subcategories then gives the displayed adjunction and the same maps. This genuinely combines geometry-specific preservation inputs; generic Mathlib restriction alone does not do it.

Step 3 cites lem-coef-finite-exceptional, whose statement gives the finite dual formula, b identity and quotient cocycle and both unit/counit equations with q. All indices are positive; K,L lie in the finite-Tor domain established by step 2. No coefficient comparison is taken from an unrelated admissibility definition.

Step 4 cites lem-coef-integral-residue-tor for uniform input Tor bounds from bounded residue cohomology, and prop-coef-integral-exceptional-adjoint for its specified coherent realization before Rlim, the right adjunction, completed pullback formula, finite reductions and unit/counit identification. The live theorem explicitly gives [a-2d_X,b+2d_Y]. All reductions use completed coefficient sheaves. Here ell differs from characteristic p, as required by residue-Tor control. The finite bounds come from step 1. Neither a limit of unspecified arrows nor site-perfectness is substituted for these hypotheses.

Step 5 cites lem-coef-rational-operations exactly for its rational adjunction, formula and preservation of evaluations, units and counits including finite scalar extension. Its use of completed integral tensor is preserved. Step 6 uses thm-coef-qbar-verdier only for the constructible domains, internal-Hom dualizing object and dual formula. The new descent node takes the scalar-compatible rational operations of step 5 as hypotheses and states the precise colimit Hom bijections and representatives that implement their map normalization. Its proof compares representatives at a common enlargement, with operation comparisons on sources and targets; it does not assert literal equalities between maps with different sources, faithfulness of a single scalar stage, or a quotient reduction on a field category.

Step 7 cites lem-fix-operation-reduction for tensor constraints/evaluations on its stated domains. The finite quotient internal-Hom assertion of that node is only site-perfect; I use thm-coef-finite-hom for the general finite-Tor comparison instead. Lem-coef-integral-hom-reduction explicitly says arbitrary first variables and preserves the displayed evaluation transpose. Lem-coef-integral-finite-extension gives internal-Hom and dualizing-object comparisons compatible with evaluation, biduality, identity and field towers. Thus each used fact is a cited statement, not a construction hidden in a proof. Step 8 takes identity/composition/exchange/projection coherence, additional orientation/pairing scope and field Weil equivariance directly from fix-prop-coherence. Restriction of a natural-transformation equation to the common domain is elementary and preserves the equation; Weil equivariance is used only for the descending data in the parent. No new arbitrary-base-change assertion for Verdier duality is added.

For B1--B9 the two new JSONs have empty proof/proof_deps, null proof_origin, self-contained fields/schemes/categories/maps, definition dependencies for the notions actually used, single TeX escaping, precise blueprint source places, honest searches and no claimed Mathlib match. No new definition is introduced. The statements are derived-category/functor/Hom assertions, not per-degree substitutes. citations.json contains verbatim full statements for each parent use, checked against the current live/sandbox statements; broad quotes retain the displayed formulas exactly and do not substitute a proof quote. The graph checks are run on the server only. A read-only dependency traversal found no return path from the reused geometry node, thm-coef-qbar-verdier or fix-prop-coherence to this item. The new nodes have only existing definition dependencies and no proof edges. No SGA is cited.

For D1/D2/C5, the parent now proves the assembly with the five direct existing-theorem citation steps, rather than applying clause-block children. The new finite node is exactly old step 3, and the conditional common-field normalization node is exactly old step 7. Old steps 1--2 are assigned to an existing geometric node and explicit Nagata/dimension citations; they are preserved in full below. This is the only deviation from creating a third new geometry node, forced by the duplicate prohibition. The two new statements have comparable sizes (1805 and 2389 characters). Parent proof text totals 2413 characters and no individual non-elementary step is over 2000; I reviewed all steps for hidden claims. No original argument was discarded, and neither removed clause block is renamed and reintroduced.

For E I checked f=id, X or Y empty (if Y empty then X is empty), zero complexes, n=1, m=n, identity field extension and different representatives enlarged to a third finite field. The finite restriction uses identity Hom bijections and the same class maps for f=id; zero complexes give the zero maps/intervals. Common-field unit/counit formulas reduce to the finite-stage ones at identity extension. If representatives change, their equality is witnessed at a further finite field; scalar compatibility identifies the maps there, and composition/naturality/triangle identities are computed there before taking their classes. No injectivity of an individual Hom transition is needed. The source and parent were not found false or ill-typed, so there is no statement dispute or source correction.

## Preserved original arguments and handoff assignment

The following retains the full current-main nine-step proof, with uses and source places. New workers need not reconstruct any removed prose. Assignment: old 1--2 to the existing geometric tool plus Nagata/dimension citations; old 3 to finite-exceptional-domain; old 4--6 to parent steps 3--5; old 7 to qbar-adjunction-map-descent; old 8--9 to parent steps 7--8.

### Original step 1

The structure map of $Y$ is finite type and separated. By the finite-type definition, the preimage of the affine scheme $\operatorname{Spec}k$ is quasi-compact, so $Y$ is quasi-compact. Its structure map is quasi-separated by separated-implies-quasi-separated; since $\operatorname{Spec}k$ is affine and hence quasi-separated, quasi-separated permanence makes $Y$ quasi-separated as a scheme. Apply the nonemptiness assertion for $\operatorname{Comp}(f)$ with base $Y$ and the assumed separated finite-type map $f$. It supplies a compactification with quasi-compact open $j$ and proper $p$. The assertions below apply to any chosen such compactification, not just the one supplied by nonemptiness.

Uses: def-weil-finite-type-morphism, lem-pc-separated-quasi-separated, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence, prop-nagata-compactification-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Exceptional-adjunction sentence: existence of the chosen compactification; Nagata compactification input to the finite constructible adjunction.

### Original step 2

Properness of $p$ includes finite type. Compose $p$ with the finite-type structure morphism of $Y$ using finite-type composition; thus $\overline X$ is finite type over $k$. The finite-type dimension theorem gives a finite Krull dimension bound. If $\overline X$ is nonempty, choose a nonnegative integer $d\ge\dim\overline X$; if it is empty choose $d=0$. The same theorem also supplies nonnegative finite bounds $d_X,d_Y$ for $X,Y$, using $0$ in the empty cases. These are geometric bounds independent of the finite coefficient index.

Uses: def-weil-proper-morphism, lem-sfb-finite-type-composition-base-change, lem-kun-dimension-finite-type, def-kun-topological-krull-dimension.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Exceptional-adjunction sentence: finite dimension bounds required by the finite class-relative theorem and the integral uniform-interval theorem.

### Original step 3

At $A_n$, use the class-relative adjunction theorem at the chosen $c=(j,p)$ and bound $d$. Its right functor $R_c=\nu_X^*f_c^\times R\nu_{Y,*}$ is precisely the finite exceptional functor of the operation datum. The theorem gives natural bijections $\operatorname{Hom}(Rp_*j_!K,L)\cong\operatorname{Hom}(K,R_cL)$ for bounded-below $K$ of etale origin, explicitly including bounded constructible $K$. For $K\in\mathcal C_{X,A_n}$, extension by zero preserves bounded constructibility and its Tor interval; direct-image finite-Tor preservation applied to the proper map $p$ and $j_!K$ then puts $Rp_*j_!K$ in $\mathcal C_{Y,A_n}$. Exceptional preservation puts $R_cL$ in $\mathcal C_{X,A_n}$ for $L\in\mathcal C_{Y,A_n}$. Restrict the displayed natural Hom bijections to these full subcategories: they give $Rf_!\dashv Rf_n^!$ there, with the same units and counits. The compactification comparison and cocycle are those of the class-relative theorem. This restriction uses no ambient pro-etale adjoint hypothesis.

Uses: thm-sf-ambient-adjoint-class, def-weil-exceptional-inverse-image, lem-trf-open-ctf, cor-sf-direct-image-ctf-proetale, thm-sf-preservation-class.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Exceptional-adjunction sentence: finite constructible adjunction, using the stated class-relative existence and preservation inputs of lem-coef-finite-exceptional.

### Original step 4

Apply finite exceptional coefficient change on the finite-Tor constructible domains just verified. It identifies the finite right functor with $D_{X,n}f^*D_{Y,n}$. For $m\ge n$ it gives $Q_XRf_m^!\cong Rf_n^!Q_Y$, the identity comparison at equal indices and the quotient cocycle. In its unit equation $G_n(q_K)b_{F_mK}Q_X(\eta_{m,K})=\eta_{n,Q_XK}$ and counit equation $\epsilon_{n,Q_YL}F_n(b_L)q_{G_mL}=Q_Y(\epsilon_{m,L})$, take $F_r=Rf_{!,r}$ and $G_r=Rf_r^!$. These are exactly preservation of the adjunction maps by the specified finite compact-support comparison, rather than just isomorphisms of the underlying right functors.

Uses: lem-coef-finite-exceptional.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "The exceptional adjunction and its coefficient comparisons are ...": lem-coef-finite-exceptional.

### Original step 5

First apply integral residue-Tor control: since $L_1$ has bounded cohomology, choose $[a,b]$ containing its support; all $L_n$ then have Tor amplitude in this same interval. Here $\ell$ is invertible on $Y$ because $\ell\ne p$. Apply the integral exceptional-adjoint theorem to the actual coherent coefficient-system realization specified there. Its functor is $G_fL=R\varprojlim_n\operatorname{Res}_n Rf_n^!L_n$, with $L_n=L\otimes^L_{R_Y}(A_n)_Y$. It preserves the stated derived-complete constructible category, is right adjoint to integral compact support, and is canonically $D_{X,R}f^*_{\mathrm{comp}}D_{Y,R}$. The same theorem identifies its reductions with $Rf_n^!L_n$ and identifies the units and counits with the finite ones. For an input reduction Tor interval $[a,b]$, the fixed geometric bounds of step 2 give output interval $[a-2d_X,b+2d_Y]$, independent of $n$. Thus its hypotheses and conclusions use completed coefficient sheaves and a single interval for all reductions, as required by the item; the construction is not an inverse limit of unspecified arrows in an ordinary derived category.

Uses: prop-coef-integral-exceptional-adjoint, lem-coef-integral-residue-tor.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "The exceptional adjunction and its coefficient comparisons are ...": prop-coef-integral-exceptional-adjoint.

### Original step 6

At $E$, apply identification of the rational coefficient-passage operations to the integral functor of step 5. It gives the right adjoint $Rf_E^!$ to $Rf_{!,E}$ on the rationalized constructible categories and the formula $Rf_E^!=D_{X,E}f^*D_{Y,E}$. The integral tensor product used in this passage is the completed one. The rational theorem identifies $\omega_{X,E}$ with $Ra_{X,E}^!E$ and explicitly preserves evaluations, units and counits, also under finite coefficient-field extension. Hence these are the rationalized integral adjunction and its specified comparisons.

Uses: lem-coef-rational-operations.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "The exceptional adjunction and its coefficient comparisons are ...": lem-coef-rational-operations.

### Original step 7

For $\overline{\mathbf Q}_\ell$, use the common-stage Verdier theorem: its internal-Hom dual is into $Ra_X^!\overline{\mathbf Q}_\ell$, and its coefficient passage gives $Rf_!\dashv Rf^!$ and $Rf^!=D_Xf^*D_Y$ on $D^b_c$. To see explicitly that the adjunction maps have the asserted normalization, represent an object or arrow over a finite common extension $L/\mathbf Q_\ell$ in the pair-category definition. Represent the unit, counit and evaluation by their $L$-coefficient versions. Step 6 says that enlarging $L$ preserves all three maps; consequently their classes are independent of the representative. The triangle identities and the equations preserving these maps hold at $L$ and hence in the colimit Hom groups, since composition is represented over a common finite field. This gives precisely the descended constructible adjunction and evaluation comparisons, with no reduction functor on the field category being asserted.

Uses: thm-coef-qbar-verdier, def-weil-algebraically-closed-coefficients, lem-coef-rational-operations.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Exceptional-adjunction sentence and its field coefficient passage: thm-coef-qbar-verdier, as also cited in the package statement.

### Original step 8

Check the defining maps in coefficient comparison, in addition to the exceptional units and counits already handled. Elementary operation reduction preserves tensor associativity, evaluations, units and counits on its stated domains. For general finite-Tor internal Hom use the finite Hom comparison: it is the transpose of coefficient change of evaluation and respects evaluation, tensor-Hom adjunction and composition. For integral Hom use its reduction comparison, whose displayed transpose is the reduced evaluation pairing, so evaluation and its transposes are preserved without a site-perfect first-variable restriction. For finite coefficient-field extension use the integral finite-extension comparisons of internal Hom and the dualizing object; they preserve evaluation and biduality and respect identity and composition of extensions. Together with the rational and common-stage identifications of steps 6 and 7, these give the evaluation normalizations at every stage. The site-perfect restriction of the elementary finite Hom comparison is not used to claim a general Hom comparison.

Uses: lem-fix-operation-reduction, thm-coef-finite-hom, lem-coef-integral-hom-reduction, lem-coef-integral-finite-extension.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "Finally apply [fix-prop-coherence]": its evaluation-defined coefficient-comparison inputs.

### Original step 9

Apply coherence of the proved comparison maps to this operation datum. It gives the identity, composition, exchange and projection equations, includes the exceptional comparisons of steps 4--6, retains exactly the additional smooth-orientation and site-perfect Poincare pairing compatibilities, and gives Weil equivariance at field coefficients. Interpret each equation only where every functor and comparison in it is defined and proved: restricting natural transformations to this common full domain restricts both composites to the same equality. When the data and Weil objects descend to the finite field, the Weil-equivariance clause applies to those maps. This proves the final assertions while retaining every individual domain and purity/pairing hypothesis; it does not add a pullback-commutation assertion for Verdier duality.

Uses: fix-prop-coherence.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "Finally apply [fix-prop-coherence]": domainwise coherence, additional purity/pairing compatibilities and field Weil equivariance.

## Explicit handoff for common-field descent

Given finitely many objects and morphisms, enlarge their fields to one finite L. The left/right operation and tensor comparisons identify the sources and targets of the finite-stage Hom adjunction and evaluation with the chosen common-stage representatives. Scalar compatibility of units and counits makes the adjunction bijection commute with every transition L to M; its inverse also commutes, since each stage map is a bijection. Taking classes therefore gives an inverse pair of maps on the displayed colimit Hom groups. If a representative changes, it agrees after a further finite extension; commuting with transitions gives equal images. Unit and counit are obtained by applying the bijection and its inverse to identity maps, giving precisely the classes written in the new statement. Naturality squares and both triangle composites involve only finitely many arrows: represent them over a common finite field and use the finite-stage equations. The evaluation class is independent in the same way, because the scalar tensor/Hom comparison square commutes with evaluation. Every finite equation built from these maps is consequently represented by the corresponding finite-stage equation. This is the real descent argument isolated from old step 7, with no additional geometric/coherence clauses attached to it.

## Unfinished work

The two new nodes remain unsplit obligations by design; this delivery does not claim Lean proofs for them. Server check_dag and review_split passed before the final report. Full dry run and push are recorded by the delivery command after the completed report.

## Previous report retained for provenance

The following is the rejected report, retained verbatim as historical material. Its counts, Review by Q142 and three-block justification describe the returned attempt and are superseded by the repair above; none is a current acceptance claim.

# Stage-1 repair report

Item: lem-sf-package-exceptional-coherence-realization. Group: Q142. Date: 2026-10-22.
Returned head named by coord/returns/Q142.md: e2a95534abdca96856ae1c3b80c5b78fb624dc06.
The assigned sandbox contained only dispatcher marker files, not an earlier node or report. I therefore copied the live returned node, and read and retained the Q132 report from coord/reports/Q132/lem-sf-package-exceptional-coherence-realization.md below. No git command was run in the shared clone. The current node contains the nine returned steps with exactly the lengths in the handoff. Its statement and provenance fields are retained; this repair changes its proof, proof_deps and split_report only. The original Mathlib searches remain intact.

## Files written

- dag/nodes/sec-six-functors/lem-sf-package-exceptional-coherence-realization.json: statement unchanged; split into three assembly steps.
- dag/nodes/sec-six-functors/lem-sf-package-finite-exceptional-domain.json: statement, unsplit; no Mathlib match. Carries returned arguments 1--3: geometry and restriction of the finite class-relative adjunction.
- dag/nodes/sec-six-functors/lem-sf-package-exceptional-coefficient-passage.json: statement, unsplit; no Mathlib match. Carries returned arguments 4--6: finite quotient normalization and coherent integral-to-rational adjunction passage.
- dag/nodes/sec-six-functors/lem-sf-package-common-stage-evaluation-coherence.json: statement, unsplit; no Mathlib match. Carries returned arguments 7--9: common-field descent of adjunction maps, evaluation comparisons and domainwise coherence.
- report.md and citations.json: repair review, full preservation of the old argument and verbatim statement excerpts for every current step/node citation. searches.jsonl is the unedited msearch command log. repair.py and write_report.py are sandbox-only preparation scripts, not delivered source files.

New nodes: 3. New Mathlib leaves: 0. No unit record changed, since this item is not the unit's key node.

## Attachments

None. Exact-id and exceptional/coherence searches in lean/WeilConjectures found no declaration giving this item in all its clauses. The closest integral declaration, AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint in SixFunctors/Etale/Derived/IntegralCoefficients.lean:324, has explicit ambient left-adjoint assumptions and contains sorry at lines 358--359; it supplies neither an attachment nor a finished proof of a new node. Generic Mathlib adjunctions are not project attachments.

## WANTED

None. All sources used are present. No SGA source is used.

## Findings and repair of the return

The return requires distribution of 7427 characters of proof into at least two comparable statement-only obligations, rather than shortening the prose. I extracted all nine arguments into three independently stated lemmas. The sizes of their inherited arguments are 2245, 2318 and 2864 characters. Each node has empty proof and proof_deps, null proof_origin and mathlib_match, status unsplit, its own self-contained coefficient and scheme hypotheses, source place, definition dependencies, blueprint ancestor and logged searches. The parent proof is 1244 characters, below 3000. Its three uses are exactly these three new lemmas. No single new lemma asserts the entire item: the first has no dual formula or coefficient passage, the second has no compactification existence or common-stage coherence, and the third has no geometric finite-adjunction restriction or coherent integral construction.

All the mathematical work in the old proof is retained verbatim in the handoff sections below, including its cited nodes and sources. Future workers can start on the three interfaces independently: they do not depend on each other or on the parent. They can reuse the original citations while proving their assigned interface. This extraction follows the explicit human re-split instruction, including moving substantial parts of the old assembly into new nodes, rather than the ordinary policy against making a fresh node out of a trivial clause. None of these is an elementary two-line fact: their old proofs respectively require geometry plus two-sided preservation, several coefficient realizations, and descent plus four distinct evaluation comparisons.

There is no statement dispute or route change. The finite stage is ctf, the integral stage uses completed coefficient sheaves and uniformly bounded reductions, rationalization is raw scalar localization, and algebraically closed coefficients use the finite-field pair category. No new unrestricted ambient adjoint or arbitrary-base-change duality statement is introduced.

## Not duplicates

Whole-DAG searches by id, exceptional/adjunction/coefficient keywords, and parsed statement fields were followed by reading the closest statements. Whole-blueprint searches used tools/blueprint_refs.py search with “compactification finite dimension”, “integral rational exceptional”, “constructible adjunction”, “finite Tor compactification”, “uniform reductions adjunction”, “compactification finite Tor”, “completed integral rational exceptional”, “common stage evaluation coherence”, “exceptional coefficient passage”, “finite coefficient adjunction domain” and “coefficient passage evaluation”. Ancestor search returns prop-functor-package; via for every child is [lem-sf-package-exceptional-coherence-realization]. No imported blueprint node states any whole new interface. No new Stacks tag is introduced; the geometric tagged theorems remain the existing nodes quoted in the preserved handoff.

lem-sf-package-finite-exceptional-domain vs thm-sf-ambient-adjoint-class: the latter assumes a compactification and a finite dimension bound and gives a class-relative Hom bijection; the new node establishes those geometric hypotheses and restricts both functors to ctf using preservation on both sides.
lem-sf-package-finite-exceptional-domain vs thm-sf-preservation-class: the latter proves exceptional preservation only, not compactification existence, dimensions, left-functor preservation and restriction of the Hom bijection.
lem-sf-package-finite-exceptional-domain vs lem-sf-constructible-exceptional-adjunction-coefficients: that theorem concerns normalized adjunctions at all stages; it does not state the geometric compactification/bound interface or identify the restriction of the relative etale-origin Hom bijection.
lem-sf-package-finite-exceptional-domain vs lem-sf-constructible-exceptional-coefficient-construction: that construction record has compactification-indexed data, but does not state compactification existence and finite bounds or the relative bounded-below restriction assertion.
lem-sf-package-exceptional-coefficient-passage vs lem-coef-finite-exceptional: only the first portion is the finite comparison theorem; the new node also supplies coherent integral realization, residue-controlled uniform output bounds, and rationalization with its maps.
lem-sf-package-exceptional-coefficient-passage vs prop-coef-integral-exceptional-adjoint: that node starts with a common input Tor interval; the new interface obtains it from residue cohomology, records the finite comparison equations, and reaches the rational adjunction and field extension comparisons.
lem-sf-package-exceptional-coefficient-passage vs lem-coef-rational-operations: the latter identifies rational operations, but does not state the finite cocycle equations, coherent integral construction or residue-to-uniform-Tor/output interval assertion.
lem-sf-package-exceptional-coefficient-passage vs lem-sf-constructible-exceptional-adjunction-coefficients: its stagewise adjunction and scalar coherence do not include the dual-pullback-dual formulas, the residue criterion, coherent integral derived-limit formula and dimension-dependent uniform bound.
lem-sf-package-common-stage-evaluation-coherence vs thm-coef-qbar-verdier: the latter supplies the closed-stage duality and adjunction, but not finite/integral Hom evaluation comparisons and the complete domainwise operation equations with purity/pairing scope.
lem-sf-package-common-stage-evaluation-coherence vs fix-prop-coherence: the latter supplies the final coherence laws and names their comparison inputs; the new node also states the representative-level adjunction/evaluation descent and the normalization properties at finite and integral coefficients that make those inputs applicable.
lem-sf-package-common-stage-evaluation-coherence vs lem-sf-constructible-exceptional-coefficient-coherence: that node assumes a normalized construction record and proves its scalar/refinement equations; it neither identifies all internal-Hom evaluations nor states the orientation, pairing and general operation coherence on their common domains.
lem-sf-package-common-stage-evaluation-coherence vs lem-sf-package-verdier-coefficient-realization: that sibling concerns Verdier exchange, boundary comparisons and anti-equivalences; the new node concerns adjunction-map descent and the comparison/coherence normalizations, not those biduality claims.

## Mathlib search assessment

Every new node has its own semantic searches in two phrasings, a Loogle query and an msearch source grep. The finite-domain and coefficient-passage LeanSearch requests were rate-limited (HTTP response says 60 per minute); their records say unavailable. The closed-stage/coherence LeanSearch succeeded. LeanFinder's first geometry/coefficient queries returned affine-transition and integral-morphism results, and its second phrasings returned ordinary open restriction or condensed module adjunctions. These do not state any exceptional constructible theorem. Loogle returned the generic Adjunction/HasLimit/counit declarations. The initial CategoryTheory.FilteredColimit query was an unknown identifier, explicitly recorded as invalid rather than as absence, and replaced by CategoryTheory.Limits.HasLimit. AlgebraicGeometry greps returned zero matches. The whole-source coherence grep found exceptional Lie/Cartan terminology, polynomial coefficients and Verdier thesis references in generic triangulated theory, not this sheaf package.

I read Mathlib/CategoryTheory/Adjunction/Basic.lean:108 and its constructors, Limits/HasLimits.lean:90, AlgebraicGeometry/Modules/Sheaf.lean:425, and CategoryTheory/Monoidal/Closed/Functor.lean:79--100. The closest apparent candidate expComparison_ev is an equation for Cartesian monoidal closed categories under a product-preserving functor; it does not construct or identify the completed etale Hom comparisons, their constructible domains or six-functor equations. It is not a one-line specialization giving the new node. Searches and verdicts in the JSON are copied from the actual unedited log; no query was invented.

## Review by Q142

I read AGENTS.md, the worker brief, stages/1-dag.md, GOAL.md, the three levels and human requirements in SETUP.md, the worker role, and delivery-errors B--E in full. I opened the chapter and unit records and the main-20261015 prop-functor-package.proof.md, especially its exceptional-adjunction sentence and final fix-prop-coherence sentence. I also read the main-20261015 proofs of thm-sf-ambient-adjoint-class, prop-coef-integral-exceptional-adjoint, lem-coef-rational-operations, thm-coef-qbar-verdier and fix-prop-coherence. These are agent-written sources, so the parent retains proof_origin.by=agent. The older chapter/unit text includes larger ambient claims; the assigned current item and its cited current node statements explicitly restrict the domains. I kept the assigned statement and current route rather than silently enlarging it.

For assembly step 1 I read the complete statement of lem-sf-package-finite-exceptional-domain: it says both that compactifications and all the required bounds exist, and that for every chosen compactification the class-relative Hom bijection restricts to the finite ctf adjunction with its original units/counits. It introduces the field, ring, sites, scheme hypotheses, finite-Tor domain, ordinary etale right adjoint and comparison functors itself. Its source is the exceptional-adjunction sentence expanded by returned steps 1--3, whose exact argument is retained below. I checked the original cited statements: finite type gives qc of Y; separatedness plus the affine qcqs base gives qs; Nagata requires precisely this qcqs base and gives j qc open and p proper. Proper p is finite type, composition gives Xbar finite type, and the dimension theorem applies over k. The finite class theorem explicitly includes bounded constructible etale-origin inputs. Open extension and proper direct image preserve ctf, and thm-sf-preservation-class supplies right-functor preservation with separated Y. Thus restriction really is justified on both sides; it does not use the conditional ambient interface. Empty schemes get bound zero and no empty maximum is taken.

For assembly step 2 I read the complete statement of lem-sf-package-exceptional-coefficient-passage and checked each assertion used in the assembly. It states the finite dual formula, both normalized unit/counit equations and quotient identities/cocycle, then the actual coherent integral derived-limit realization, residue criterion, uniform bound and reduction-compatible maps, and finally rationalization including field-extension evaluation compatibility. All of those have sources in the preserved steps 4--6. I checked lem-coef-finite-exceptional supplies the two equations exactly for positive finite indices on ctf. Lem-coef-integral-residue-tor supplies the common Tor interval from bounded residue cohomology; ell is invertible because ell differs from p. Prop-coef-integral-exceptional-adjoint specifies an actual coefficient-system realization before its derived limit and states the dimension bound [a-2d_X,b+2d_Y]. Lem-coef-rational-operations explicitly identifies the rational adjunction and formula and preserves evaluations, units and counits under finite extension. This interface requires no new uniform-Tor hypothesis from the parent, no site-perfectness, and no inverse limit of unspecified arrows. Its completed pullback and completed tensor conventions are explicit.

For assembly step 3 I read the complete statement of lem-sf-package-common-stage-evaluation-coherence. It says the closed-stage formula and adjunction and representative-independent normalization of all three defining maps, then the finite/integral/scalar-extension evaluation clauses, then domainwise coherence including exact purity/pairing and Weil descent scope. Returned steps 7--9 below are the full inherited argument, not a replacement slogan. Thm-coef-qbar-verdier identifies the internal-Hom dualizing object and gives the closed-stage adjunction; def-weil-algebraically-closed-coefficients defines Hom groups, equality and composition over common finite fields. Lem-coef-rational-operations preserves the maps under enlargement, so their classes and triangle equations descend. I separately checked lem-fix-operation-reduction, thm-coef-finite-hom, lem-coef-integral-hom-reduction and lem-coef-integral-finite-extension: the first's elementary finite Hom comparison is only site-perfect; the second supplies the general finite-Tor comparison with the actual evaluation transpose; the third preserves evaluation and transposes for arbitrary first variables; the fourth preserves evaluation and biduality through finite extension and its identity/composition. Finally fix-prop-coherence states the four equation types and extra orientation/pairing compatibilities, with field Weil equivariance. Restriction to intersections retains those equalities and does not claim base-change commutation for Verdier duality. The new node cites the site-perfect and orientation definitions and introduces all coefficient domains itself.

Against B, the new nodes are statements only, with all objects and hypotheses introduced, definition dependencies checked, single-escaped TeX, actual source places, no proof sketch inside their statements and no manufactured Mathlib leaves. Against C, citations.json quotes the actual statement of each of the three assembly lemmas in full; the assertions the assembly uses occur there. Each original non-elementary input remains named in the retained handoff for the worker proving the extracted node. The children have no proof edges and only existing definition dependencies, so there is no return edge to the parent or between children. These are same-unit children, not replacements of the unit route by outside-unit tools. Inherited maintainer approval/tool fields on the parent were retained untouched, as required by the field-preservation rule; no approval was authored by me.

Against D, all nine arguments were assigned once, in three comparable groups, and preserved word for word below; none was thrown away to meet the length cap, and none was shifted wholesale into a single restatement of the item. Against E, I tested f=id, empty X and/or Y, zero complexes, n=1, m=n, identity coefficient-field extension and enlargement to a further common coefficient field. Adjunction maps specialize to the identity/triangle identities; empty-space dimensions use minus infinity bounded by zero; uniform Tor intervals allow the zero object; no field reduction is used. The source's finite-Tor versus site-perfect distinction and all completed-versus-ordinary coefficient distinctions remain intact. No false statement or ill-typed expression was found. Every parent proof step is under 2000 characters, with no residual long hidden argument. The repair addresses the sole numbered/content demand of the return: actual workload distribution, not a rebase or unchanged re-push.

## Preserved arguments for the next workers

The following is the original proof without shortening, including every uses list and source place. These are handoff arguments in the report, not proof steps in any new statement-only JSON file. Their group assignment is the complete map from the returned nine-step proof to the new obligations.

### lem-sf-package-finite-exceptional-domain

Returned step 1 (697 characters):

The structure map of $Y$ is finite type and separated. By the finite-type definition, the preimage of the affine scheme $\operatorname{Spec}k$ is quasi-compact, so $Y$ is quasi-compact. Its structure map is quasi-separated by separated-implies-quasi-separated; since $\operatorname{Spec}k$ is affine and hence quasi-separated, quasi-separated permanence makes $Y$ quasi-separated as a scheme. Apply the nonemptiness assertion for $\operatorname{Comp}(f)$ with base $Y$ and the assumed separated finite-type map $f$. It supplies a compactification with quasi-compact open $j$ and proper $p$. The assertions below apply to any chosen such compactification, not just the one supplied by nonemptiness.

Uses: def-weil-finite-type-morphism, lem-pc-separated-quasi-separated, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence, prop-nagata-compactification-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Exceptional-adjunction sentence: existence of the chosen compactification; Nagata compactification input to the finite constructible adjunction.

Returned step 2 (536 characters):

Properness of $p$ includes finite type. Compose $p$ with the finite-type structure morphism of $Y$ using finite-type composition; thus $\overline X$ is finite type over $k$. The finite-type dimension theorem gives a finite Krull dimension bound. If $\overline X$ is nonempty, choose a nonnegative integer $d\ge\dim\overline X$; if it is empty choose $d=0$. The same theorem also supplies nonnegative finite bounds $d_X,d_Y$ for $X,Y$, using $0$ in the empty cases. These are geometric bounds independent of the finite coefficient index.

Uses: def-weil-proper-morphism, lem-sfb-finite-type-composition-base-change, lem-kun-dimension-finite-type, def-kun-topological-krull-dimension.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Exceptional-adjunction sentence: finite dimension bounds required by the finite class-relative theorem and the integral uniform-interval theorem.

Returned step 3 (1012 characters):

At $A_n$, use the class-relative adjunction theorem at the chosen $c=(j,p)$ and bound $d$. Its right functor $R_c=\nu_X^*f_c^\times R\nu_{Y,*}$ is precisely the finite exceptional functor of the operation datum. The theorem gives natural bijections $\operatorname{Hom}(Rp_*j_!K,L)\cong\operatorname{Hom}(K,R_cL)$ for bounded-below $K$ of etale origin, explicitly including bounded constructible $K$. For $K\in\mathcal C_{X,A_n}$, extension by zero preserves bounded constructibility and its Tor interval; direct-image finite-Tor preservation applied to the proper map $p$ and $j_!K$ then puts $Rp_*j_!K$ in $\mathcal C_{Y,A_n}$. Exceptional preservation puts $R_cL$ in $\mathcal C_{X,A_n}$ for $L\in\mathcal C_{Y,A_n}$. Restrict the displayed natural Hom bijections to these full subcategories: they give $Rf_!\dashv Rf_n^!$ there, with the same units and counits. The compactification comparison and cocycle are those of the class-relative theorem. This restriction uses no ambient pro-etale adjoint hypothesis.

Uses: thm-sf-ambient-adjoint-class, def-weil-exceptional-inverse-image, lem-trf-open-ctf, cor-sf-direct-image-ctf-proetale, thm-sf-preservation-class.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Exceptional-adjunction sentence: finite constructible adjunction, using the stated class-relative existence and preservation inputs of lem-coef-finite-exceptional.


### lem-sf-package-exceptional-coefficient-passage

Returned step 4 (634 characters):

Apply finite exceptional coefficient change on the finite-Tor constructible domains just verified. It identifies the finite right functor with $D_{X,n}f^*D_{Y,n}$. For $m\ge n$ it gives $Q_XRf_m^!\cong Rf_n^!Q_Y$, the identity comparison at equal indices and the quotient cocycle. In its unit equation $G_n(q_K)b_{F_mK}Q_X(\eta_{m,K})=\eta_{n,Q_XK}$ and counit equation $\epsilon_{n,Q_YL}F_n(b_L)q_{G_mL}=Q_Y(\epsilon_{m,L})$, take $F_r=Rf_{!,r}$ and $G_r=Rf_r^!$. These are exactly preservation of the adjunction maps by the specified finite compact-support comparison, rather than just isomorphisms of the underlying right functors.

Uses: lem-coef-finite-exceptional.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "The exceptional adjunction and its coefficient comparisons are ...": lem-coef-finite-exceptional.

Returned step 5 (1110 characters):

First apply integral residue-Tor control: since $L_1$ has bounded cohomology, choose $[a,b]$ containing its support; all $L_n$ then have Tor amplitude in this same interval. Here $\ell$ is invertible on $Y$ because $\ell\ne p$. Apply the integral exceptional-adjoint theorem to the actual coherent coefficient-system realization specified there. Its functor is $G_fL=R\varprojlim_n\operatorname{Res}_n Rf_n^!L_n$, with $L_n=L\otimes^L_{R_Y}(A_n)_Y$. It preserves the stated derived-complete constructible category, is right adjoint to integral compact support, and is canonically $D_{X,R}f^*_{\mathrm{comp}}D_{Y,R}$. The same theorem identifies its reductions with $Rf_n^!L_n$ and identifies the units and counits with the finite ones. For an input reduction Tor interval $[a,b]$, the fixed geometric bounds of step 2 give output interval $[a-2d_X,b+2d_Y]$, independent of $n$. Thus its hypotheses and conclusions use completed coefficient sheaves and a single interval for all reductions, as required by the item; the construction is not an inverse limit of unspecified arrows in an ordinary derived category.

Uses: prop-coef-integral-exceptional-adjoint, lem-coef-integral-residue-tor.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "The exceptional adjunction and its coefficient comparisons are ...": prop-coef-integral-exceptional-adjoint.

Returned step 6 (574 characters):

At $E$, apply identification of the rational coefficient-passage operations to the integral functor of step 5. It gives the right adjoint $Rf_E^!$ to $Rf_{!,E}$ on the rationalized constructible categories and the formula $Rf_E^!=D_{X,E}f^*D_{Y,E}$. The integral tensor product used in this passage is the completed one. The rational theorem identifies $\omega_{X,E}$ with $Ra_{X,E}^!E$ and explicitly preserves evaluations, units and counits, also under finite coefficient-field extension. Hence these are the rationalized integral adjunction and its specified comparisons.

Uses: lem-coef-rational-operations.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "The exceptional adjunction and its coefficient comparisons are ...": lem-coef-rational-operations.


### lem-sf-package-common-stage-evaluation-coherence

Returned step 7 (934 characters):

For $\overline{\mathbf Q}_\ell$, use the common-stage Verdier theorem: its internal-Hom dual is into $Ra_X^!\overline{\mathbf Q}_\ell$, and its coefficient passage gives $Rf_!\dashv Rf^!$ and $Rf^!=D_Xf^*D_Y$ on $D^b_c$. To see explicitly that the adjunction maps have the asserted normalization, represent an object or arrow over a finite common extension $L/\mathbf Q_\ell$ in the pair-category definition. Represent the unit, counit and evaluation by their $L$-coefficient versions. Step 6 says that enlarging $L$ preserves all three maps; consequently their classes are independent of the representative. The triangle identities and the equations preserving these maps hold at $L$ and hence in the colimit Hom groups, since composition is represented over a common finite field. This gives precisely the descended constructible adjunction and evaluation comparisons, with no reduction functor on the field category being asserted.

Uses: thm-coef-qbar-verdier, def-weil-algebraically-closed-coefficients, lem-coef-rational-operations.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Exceptional-adjunction sentence and its field coefficient passage: thm-coef-qbar-verdier, as also cited in the package statement.

Returned step 8 (1095 characters):

Check the defining maps in coefficient comparison, in addition to the exceptional units and counits already handled. Elementary operation reduction preserves tensor associativity, evaluations, units and counits on its stated domains. For general finite-Tor internal Hom use the finite Hom comparison: it is the transpose of coefficient change of evaluation and respects evaluation, tensor-Hom adjunction and composition. For integral Hom use its reduction comparison, whose displayed transpose is the reduced evaluation pairing, so evaluation and its transposes are preserved without a site-perfect first-variable restriction. For finite coefficient-field extension use the integral finite-extension comparisons of internal Hom and the dualizing object; they preserve evaluation and biduality and respect identity and composition of extensions. Together with the rational and common-stage identifications of steps 6 and 7, these give the evaluation normalizations at every stage. The site-perfect restriction of the elementary finite Hom comparison is not used to claim a general Hom comparison.

Uses: lem-fix-operation-reduction, thm-coef-finite-hom, lem-coef-integral-hom-reduction, lem-coef-integral-finite-extension.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "Finally apply [fix-prop-coherence]": its evaluation-defined coefficient-comparison inputs.

Returned step 9 (835 characters):

Apply coherence of the proved comparison maps to this operation datum. It gives the identity, composition, exchange and projection equations, includes the exceptional comparisons of steps 4--6, retains exactly the additional smooth-orientation and site-perfect Poincare pairing compatibilities, and gives Weil equivariance at field coefficients. Interpret each equation only where every functor and comparison in it is defined and proved: restricting natural transformations to this common full domain restricts both composites to the same equality. When the data and Weil objects descend to the finite field, the Weil-equivariance clause applies to those maps. This proves the final assertions while retaining every individual domain and purity/pairing hypothesis; it does not add a pullback-commutation assertion for Verdier duality.

Uses: fix-prop-coherence.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Sentence "Finally apply [fix-prop-coherence]": domainwise coherence, additional purity/pairing compatibilities and field Weil equivariance.

## Unfinished work

The three extracted nodes are intentionally unsplit stage-1 obligations for future workers. This is the requested work distribution, not a claim that the corresponding Lean proofs are complete. The current parent split is complete subject to server preflight and independent maintainer review.

## Previous report retained for provenance

This is Q132's prior report, before the explicit 2026-10-22 re-split instruction. Its counts and description concern that prior delivery only; the repair and new counts are above.

# Stage-1 worker report

Item: lem-sf-package-exceptional-coherence-realization. Group: Q132. Date: 2026-10-21.

## Files written

- dag/nodes/sec-six-functors/lem-sf-package-exceptional-coherence-realization.json: statement; split into nine proof steps. No Mathlib match for the assembled geometric exceptional/coherence theorem.
- citations.json: 26 step/node entries, each with a verbatim substring of the cited node's statement.
- report.md: this report. searches.jsonl is the unedited search-command log.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: the item is a created prerequisite of prop-functor-package, not the unit's key node.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint id and exceptional/coherence notions found no declaration stating the entire item. The existing ambient-adjoint and composition interfaces concern parts or conditional variants; they do not attach the unconditional theorem at all four stages.

## WANTED

None. The source used is already present. No SGA source is used.

## Findings and changes

The original statement is retained verbatim. Its proof was empty. Added its dimension-definition dependency and a complete argument using existing nodes; retained provenance and the inherited Mathlib search records. The ancestor search identifies prop-functor-package. Whole-blueprint searches for the item title and exceptional adjunction found no other node stating this combined item. The ancestor is deliberately not a proof dependency. No newly coined lemma or restatement of a clause is needed.

A potential C4 error was avoided: fix-prop-adjunctions now makes its exceptional clause conditional on exceptionally admissible f. It cannot discharge this unconditional item. Step 3 instead uses the class-relative adjunction and the independent preservation theorems. Another potential domain error was repaired before delivery: the item assumes uniformly bounded cohomology of integral reductions, not an additional uniform Tor condition. Step 5 explicitly cites lem-coef-integral-residue-tor to obtain the uniform Tor interval before invoking integral exceptional reconstruction. At algebraically closed coefficients, the rational-operations statement alone is insufficient: step 7 also uses thm-coef-qbar-verdier and the common-stage category definition.

Mathlib searches: the new logged LeanFinder searches in two phrasings returned ordinary sheaf pullback/pushforward, condensed functors, local cohomology and generic adjunctions, not constructible exceptional adjunctions or the coefficient coherence package. LeanSearch likewise returned ordinary sheaf and over-category adjunctions. The grep hits for Verdier concern triangulated localization and historical references, not sheaf Verdier duality. The first Loogle query contained the unknown identifier CategoryTheory.NatIso; this is recorded as an invalid query, not absence. The corrected CategoryTheory.Adjunction query returned the generic adjunction definition and constructors. None has the geometric operations and coefficient comparisons of this item. All appended queries and result summaries come from searches.jsonl; no search was invented.

## Not duplicates

There are no new nodes and therefore no new/existing same-tag pairs. The existing finite, integral, rational, algebraically closed and coherence nodes are reused. In particular, no finite-stage formula, coefficient-passage theorem, compactification lemma or elementary common-stage equation was created again.

## Review by Q132

I read the worker contract, stage-1 rules, three-level route rules in SETUP.md, GOAL.md, the chapter and unit records, and delivery-errors B--E (including their merged copy). I read the actual main-20261015 prop-functor-package proof, especially its exceptional-adjunction and final coherence sentences, and the finite-exceptional, integral-exceptional, rational-operations, qbar-Verdier and coherence statements at that snapshot, including the coherence proof. Those sentences prescribe exactly the coefficient-passage and coherence route followed here. The blueprint is agent-written, so proof_origin.by is agent. The current DAG statements supply corrected precise domains and empty-scheme conventions. There are no new-node sources to audit.

For step 1, I opened def-weil-finite-type-morphism, lem-pc-separated-quasi-separated, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence and prop-nagata-compactification-category. Finite type gives quasi-compactness by evaluating over the whole affine base Spec k. The separated structure morphism gives relative quasi-separatedness; permanence with the quasi-separated affine base gives absolute quasi-separatedness of Y. Thus the compactification-category theorem's qcqs base assumption is established before invoking nonemptiness. Its objects explicitly have quasi-compact open j and proper p.

For step 2, def-weil-proper-morphism includes finite type, and lem-sfb-finite-type-composition-base-change explicitly proves finite-type composition; it is a Mathlib leaf, not an uncited algebraic-geometry assertion. Lem-kun-dimension-finite-type then applies to the compactification as well as X and Y. The dimension definition explicitly assigns minus infinity to the empty space, so choosing bound zero in that case and a nonnegative bound otherwise is valid. No maximum over an empty cover is used.

For step 3, thm-sf-ambient-adjoint-class explicitly supplies the natural bounded-below Hom bijections for etale-origin K and says bounded constructible inputs qualify. Its bound is available from step 2. The defining formula in def-weil-exceptional-inverse-image identifies its R_c with the operation used in the item; no theorem was inferred merely from the definition. Lem-trf-open-ctf proves the preservation of j_!, and cor-sf-direct-image-ctf-proetale proves the preservation of Rp_* with source dimension bounded by d. Thm-sf-preservation-class explicitly proves finite exceptional preservation with separated target Y, which is an assumption of this item. These statements justify restricting both functors and the Hom bijections to full finite-Tor subcategories. Restriction retains the same unit, counit and their equations. This does not assume a right adjoint on arbitrary pro-etale objects.

For step 4, lem-coef-finite-exceptional says precisely the dual-pullback-dual formula, quotient cocycle and the two displayed unit/counit equations used in the step. The finite-Tor domain and positive indices were already checked. At m=n its identity normalization agrees with the stated identity comparison; n=1 is included.

For step 5, lem-coef-integral-residue-tor applies because ell is invertible on Y and the integral input is derived complete with bounded residue cohomology. It supplies one finite-level Tor interval for all n, without identifying constructibility with site-perfectness. Prop-coef-integral-exceptional-adjoint specifies the coherent realization before the inverse limit, its constructible adjunction, completed-pullback formula, all finite reductions and compatibility of units and counits. It states the uniform output interval using the nonnegative dimension bounds already obtained. This resolves the actual integral domain rather than introducing an extra input hypothesis.

For step 6, lem-coef-rational-operations explicitly asserts the rational adjunction and formula and preservation of evaluations, units and counits, including finite scalar extension. Its completed integral tensor convention is kept. For step 7, thm-coef-qbar-verdier gives the common-stage internal-Hom identification, constructible adjunction and formula. Def-weil-algebraically-closed-coefficients says arrows, their equality and composition are represented over finite common fields. Thus the unit/counit/evaluation normalization follows by representing them at one common field and using step 6's scalar compatibility; equality of their classes and triangle identities follow from equality at that field. No unsupported limit-of-categories assertion is inserted, and no reduction functor is applied to a field object.

For step 8, I opened each of lem-fix-operation-reduction, thm-coef-finite-hom, lem-coef-integral-hom-reduction and lem-coef-integral-finite-extension. The first explicitly preserves the structural evaluations and adjunction maps but only gives its elementary finite Hom comparison for a site-perfect first variable. The second explicitly removes that restriction on the finite-Tor constructible domain and characterizes its comparison by evaluation. The third says its reduction comparison preserves evaluation and transposes, and the fourth gives the same evaluation normalization for finite coefficient-field extension. These are actual statement clauses, not facts taken from their proofs. They justify the evaluation assertions for general variables on precisely the stated domains.

For step 9, fix-prop-coherence explicitly states the four coherence types, extra smooth-orientation/site-perfect pairing compatibilities and field Weil equivariance. It applies to the same operation datum and the already proved comparisons. Restricting each equation to the intersection of its domains simply restricts equal natural transformations. The item assumes finite-field descent and Weil structures where equivariance is asserted; it does not assert arbitrary-base-change commutation of Verdier duality. The ordinary and exceptional coefficient maps are the normalized ones checked in the preceding steps.

Against B--E: no new statement-only node contains a hidden proof, no elementary fact became a node, no clause was moved into a new restatement, and no Mathlib leaf was manufactured. Every uses entry has its cited statement open and a verbatim quote in citations.json. I checked that the dependency closure of each substantive cited theorem does not return to the item. The source route and the statement have not changed. Generic off-unit tools are declared in split_report.tool_uses, not in a top-level approval field. Each step is shorter than 2000 characters; there is no long step concealing a separate lemma. Edge cases checked are empty X or Y, zero objects, f=id, n=1, identity quotients, identity finite-field extension, and enlargement of the common finite field. All formulas remain typed and use the supplied identity/triangle/cocycle laws. There is no STATEMENT-DISPUTED finding.

## Unfinished work

None in the stage-1 split. Independent maintainer review remains part of the delivery process.

Dry-run repair: expanded three verbatim citation excerpts to include the relevant hypotheses or full formula; the citation gate requires at least 40 characters unless quoting the whole statement. No mathematical change was needed.
