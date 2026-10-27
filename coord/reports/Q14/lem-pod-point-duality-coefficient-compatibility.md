# Stage-1 repair: lem-pod-point-duality-coefficient-compatibility

## Files written

- dag/nodes/sec-six-functors/lem-pod-point-duality-coefficient-compatibility.json: unchanged statement, split assembly of two new obligations.
- dag/nodes/sec-six-functors/lem-pod-point-dual-coefficient-domains.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-pod-point-dual-evaluation-transport.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every parent citation.

## Attachments

None. Searched WeilConjectures by the item tag and point-dual/coefficient terminology, and read Derived/Point.lean and Derived/GlobalDuality.lean. These concern etale point equivalences or an unnormalized existence of an isomorphism; they do not state the stipulated pro-etale integral/rational/common-stage coefficient square. No attachment is claimed from a partial or sorried result.

## Wanted

None.

## What was wrong and what changed

The returned proof had 7509 characters in eight steps. The sandbox initially contained only dispatcher markers, not the delivered nodes, report or search log. I read the current repository version as the returned head; its eight step sizes match the return. The original statement is byte-for-byte unchanged. All imported metadata and prior searches remain. Two new statement-only nodes divide the substantial arguments, and parent steps 1--3 are a short assembly, retaining the final transpose calculation. Each child has empty proof/proof_deps and null proof_origin. This is a new split, not a rebase or unchanged push.

The new domains obligation is not the main coefficient-duality square: it establishes the actual sections comparisons on duality domains, including the missing finite-quotient comparison. The evaluation obligation proves the normalization of j and equality of evaluation pairings, without the module dual comparison b or the final duality-square equation. They distribute different arguments of comparable size (3556 and 2450 characters of old proof). The final 1503 characters of old transposition argument remain in the parent assembly.

## Unfinished

The two new obligations intentionally remain unsplit, ready for separate workers. No Lean was changed or compiled.

## Not duplicates

lem-pod-point-dual-coefficient-domains vs lem-sf-point-ringed-evaluation-model: the latter gives ambient ringed-point tensor representatives and their coefficient tensor squares; the new statement must additionally establish the specified sections/coefficient functor isomorphism in the target coefficient category for every listed passage, including completed integral and rational stages, and verify the domains of the internal dual and coefficient dual comparison. Its finite-quotient argument reuses that general model rather than reconstructing its tensorators.
lem-pod-point-dual-coefficient-domains vs lem-pod-point-sections-derived-reduction: the latter is the integral-to-finite comparison only, with no finite-quotient nonflat passage, scalar extension, duality domains or dualizing normalization.
lem-pod-point-dual-coefficient-domains vs lem-weil-point-sections-scalar-extension: the latter supplies integral scalar extension and its rationalization, not finite-quotient sections comparison or duality domains.
lem-pod-point-dual-coefficient-domains vs thm-sf-ctf-stability: stability does not identify the specific sections/coefficient comparison as an isomorphism in the coefficient-module category.
lem-pod-point-dual-evaluation-transport vs lem-pod-point-dualizing-complex: existence of the canonical point-dual identification is reused; the new obligation states its precise evaluation identity and the equality of pairings under each coefficient passage.
lem-pod-point-dual-evaluation-transport vs lem-coef-finite-point-internal-hom-evaluation: the latter gives finite-stage evaluation normalization, not its integral completed/rational/common-stage form or coefficient transport of pairings.
lem-pod-point-dual-evaluation-transport vs lem-pod-point-derived-hom-evaluation: the latter concerns a particular constant-extension K-flat model and K-injective coefficient resolution with ordinary tensor; the new statement covers the specified duality map for arbitrary C in the stipulated categories, with completed tensors and coefficient comparison.
lem-pod-point-dual-evaluation-transport vs lem-pod-point-completed-evaluation: the latter is integral perfect-model evaluation, not coefficient transport across all listed passages.
lem-pod-point-dual-evaluation-transport vs lem-pod-point-scalar-hom-evaluation: the latter covers integral finite-projective models and field extension; it does not cover finite-quotient and integral-reduction evaluation squares on the stated general domains.
lem-pod-point-dual-evaluation-transport vs lem-coef-dual-formula-scalar-transpose: that statement compares the exceptional counit under an integral field extension along a scheme morphism; it does not give the point-fibre evaluation identity or finite-reduction square.
lem-pod-point-dual-evaluation-transport vs lem-pod-closed-uncurry-laws: the latter is only abstract adjunction calculus and does not identify any specified sheaf comparison or its completion.

lem-pod-point-dual-evaluation-transport vs lem-coef-ringed-pullback-hom-evaluation-comparison: the latter gives abstract ordinary ringed-pullback evaluation preservation, without the prescribed point-duality j, completed integral tensors, rationalized and common-stage sections maps, or their joint pairing equation.
lem-pod-point-dual-evaluation-transport vs lem-coef-internal-adjunction-pairing-change: that is a finite etale locally closed-immersion adjunction/counit square rather than the pro-etale point evaluation comparison at every coefficient stage.
lem-pod-point-dual-evaluation-transport vs lem-coef-derived-system-evaluation-calculus: that describes strict coefficient-system evaluation and its derived adjunction, not sections of the normalized point dual or scalar extension to coefficient fields.
lem-pod-point-dual-evaluation-transport vs lem-weil-finite-duality-site-comparison: that compares etale and pro-etale sites at one finite coefficient stage, not distinct coefficient rings or the specified point fibre duality maps.

Searched the whole DAG and blueprint for sections tensor, point sections, quotient sections, dual comparison, evaluation pairing, evaluation normalization, point dual and coefficient pairing; inspected the pertinent matches above. No blueprint statement coincides with either new obligation, so same_as is empty. Their nearest blueprint ancestor is thm-pod-global-verdier-duality via this item, as the ancestor tool reports.

## Review by Q14

I read the current blueprint thm-pod-global-verdier-duality.proof.md second paragraph, its chapter and sk-thm-sf-package unit, and the statements of every dependency of the returned eight-step proof. For the sections/domains child I read Stacks sites-cohomology.tex, Tag 06YY (lemma-derived-base-change), Tag 07A4 (lemma-pullback-tensor-product), Tag 0G7E (lemma-pullback-K-flat), proetale.tex Tag 0991 (section-points), Tag 098H (lemma-w-contractible-is-weakly-contractible), and sites.tex Tag 00Y8 (lemma-point-pushforward-sheaf). These justify its ambient ringed-point route; the blueprint supplies its remaining coefficient and finite-Tor interfaces. The evaluation child follows the blueprint's same paragraph and the Hom-complex definition, expanded as the agent-written evaluation argument below; I do not attribute these expanded equalities to a verbatim theorem in the blueprint. Neither child uses SGA.

Parent step 1 cites precisely the new domains statement: its t is an isomorphism in D(Lambda'), its duals belong to D^b_ctf, and its final sentence fixes delta and its normalization. Parent step 2 cites precisely the new evaluation statement: both j evaluation identities and the displayed pairing equality occur in its statement. Parent step 3 uses those preceding equalities and only the existing closed-uncurry statement (its adjunction inverse and evaluation naturality formulas) and the definition of the common-stage point category. I checked the quoted parts against the statements, not the cited proofs. The definition of b is already part of the unchanged parent statement; expanding that transpose and naturality of a tensor constraint is elementary. The final argument does not assume b or delta invertible.

I checked that the first child's finite comparison is on unbounded ambient categories and never imposes false finite Tor amplitude on A_m over A_n. At finite stages the unit has amplitude [0,0]; ctf stability (ii) and (vii), including its integral and field clauses, supply the duality domains. Its integral scalar comparison is phi inverse, not phi. Rationalization uses the definition of F_E; the algebraic closure uses one common finite coefficient field. In the second child the dualizing comparison is explicitly normalized by Q_s u, so the claimed pairing equality does not silently choose a different isomorphism of the units.

Edge cases: C=0 makes every pairing zero; C=Lambda_s in degree zero gives multiplication and the coefficient ring unit; shifted units use the Hom differential df-(-1)^rfd and the symmetry sign if the order of factors is changed. Identity reduction m=n and identity field extension give identity t. The nonflat test n=2,m=1 is allowed by unbounded K-flat resolutions and does not appeal to flatness of the quotient. These tests introduce no additional hypothesis or change to the parent. There is no statement dispute.

B--E review: new statements introduce their data and notation and cite their defining nodes, contain no proof steps, and use TeX with one logical backslash. Every cited non-elementary fact remains allocated to a child, and the children retain the original literature route. The two children do not state the final square or move its whole conclusion into a single new node. No cycles or stale dependencies are intentionally introduced. Mathlib searches were executed exclusively by msearch.py and the returned log entries below were read; abstract curry/uncurry and ordinary evaluation hits do not establish the sheaf-specific completed comparisons. I inspected Mathlib Monoidal/Closed/Basic.lean and Monoidal/Rigid/Basic.lean to check their actual categorical scopes. I did not rerun the original item's unchanged searches, which are retained verbatim.

## Preserved arguments and work allocation

The following is the original proof verbatim, retained so the re-split loses no argument. It is work material for the new workers, not proof steps in either unsplit node. Returned steps 1--4 are assigned to lem-pod-point-dual-coefficient-domains; returned steps 5--6 to lem-pod-point-dual-evaluation-transport; returned steps 7--8 are the parent assembly. The first child's worker may reuse the existing ringed-evaluation model for the corresponding subclaims, but must establish the actual coefficient-category maps and domains.

### Returned step 1 — domains child

First identify sections with the inverse image of a ringed topos point, at finite coefficients. In [lem-fix-geometric-stalk-topos-point] take the geometric point $\operatorname{id}_s$ of $s=\operatorname{Spec}k$. The pointed-neighbourhood category has initial object $(s,\operatorname{id}_s)$: its map to $(U,u)$ is precisely the specified lift $u:s\to U$. Its opposite therefore has terminal object $(s,\operatorname{id}_s)$, so the stalk colimit is $\mathcal F(s)$. Thus $p^{-1}=\Gamma(s,-)$. For $A=A_{E,n}$ and any constant $A$-module $M$, [lem-weil-proetale-constant-sheaf-stalk] identifies $\Gamma(s,\underline M)=M$ through the constant-section map. Give $p$ the ring map $p^{-1}A_s=A\xrightarrow{1}A$. Its module pullback is $A\otimes_A\Gamma(s,-)=\Gamma(s,-)$, which is exact on the entire ambient module category by [lem-weil-point-proetale-sections-exact].

Uses: lem-fix-geometric-stalk-topos-point, lem-weil-proetale-constant-sheaf-stalk, lem-weil-point-proetale-sections-exact.

### Returned step 2 — domains child

Apply [lem-weil-pbc-ringed-topoi-derived-pullback] to this ringed point. On a K-flat flat-term resolution its comparison is termwise sections; exactness from step 1 identifies $Lp^*$ with ambient derived sections. Now use [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] with $G=(A_{E,m})_s$, regarded as an $A_{E,n}$-module. It gives, for $1\leq m\leq n$ and any ambient complex $B$,
$$\Gamma(s,B\otimes^L_{A_{E,n}}(A_{E,m})_s)\cong\Gamma(s,B)\otimes^L_{A_{E,n}}A_{E,m}.$$
The inverse is exactly $t_{Q,B}$: the tensor-pullback map on resolutions is the balanced map induced by tensoring sections, and the identification of $\Gamma(s,(A_{E,m})_s)$ is the constant-section map of step 1. This proves the missing invertibility assertion, including for $B=C,D_sC$ once their domains are checked below. The theorem applies on unbounded ambient categories, so no finite-Tor hypothesis on $A_{E,m}$ over $A_{E,n}$ is needed; such a hypothesis would be false when $m<n$.

Uses: lem-weil-pbc-ringed-topoi-derived-pullback, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

### Returned step 3 — domains child

For integral reduction, [lem-pod-point-sections-derived-reduction] gives the stipulated $t_{Q,B}$ as an isomorphism. For integral scalar extension, [lem-weil-point-sections-scalar-extension] gives $t_{Q,B}=\varphi^{-1}$, explicitly the canonical sections-tensor map followed by the completion comparison, and gives its rationalized version at a common coefficient field. For rationalization the two fibre functors give the same module complex by [def-weil-finite-coefficient-point], so $t$ is the identity. Use [lem-sf-point-fibre-derived-tensor] for the fibre tensor isomorphisms, their unit constraints, and their compatibility with these coefficient maps. In particular the comparisons used here are the actual specified maps, with $\varphi$ inverted in the stated direction, rather than unspecified objectwise isomorphisms.

Uses: lem-pod-point-sections-derived-reduction, lem-weil-point-sections-scalar-extension, def-weil-finite-coefficient-point, lem-sf-point-fibre-derived-tensor.

### Returned step 4 — domains child

The domains required in steps 2--3 hold. The isomorphism $u_\Lambda:\omega_{s,\Lambda}\to\Lambda_s$ is the identity-adjunction normalization of [lem-pod-point-dualizing-complex]. Hence $D_sC$ is internal Hom of $C$ into the coefficient unit. The unit has Tor interval $[0,0]$ by the definition [def-weil-finite-tor-amplitude]. For the finite stage, apply (ii) and (vii) of [thm-sf-ctf-stability] to $X=s$, and its integral and field-stage assertions to the other stages. They put $D_sC$, $Q_sC$ and $D_s(Q_sC)$ in the required bounded constructible finite-Tor categories. The evaluation compatibility in (vii), with [lem-fix-operation-reduction] on its stated domains, applies to the canonical internal-Hom arrow $\delta_{Q,C}$. We do not infer that arbitrary constructible finite-Tor sheaves on a positive-dimensional scheme are site-perfect, nor use the site-perfect formula outside its domain.

Uses: lem-pod-point-dualizing-complex, def-weil-finite-tor-amplitude, thm-sf-ctf-stability, lem-fix-operation-reduction.

### Returned step 5 — evaluation child

Fix notation for evaluation and the canonical identifications. Put $d=F_\Lambda(D_sC)$, and let $\mu_\Lambda:d\otimes^L c\xrightarrow{\sim}F_\Lambda(D_sC\otimes^L C)$ be the inverse tensor comparison of [lem-sf-point-fibre-derived-tensor]. Let $e_\Lambda:d\otimes^Lc\to\Lambda$ be $F_\Lambda(u_\Lambda\circ\operatorname{ev}_C)\circ\mu_\Lambda$, with the fibre unit identified with $\Lambda$. Unpack the specified canonical internal-Hom identification $j_{\Lambda,C}$ of [lem-pod-point-dualizing-complex]: its map into the coefficient Hom is the tensor--Hom transpose of evaluation after sections, followed by $u_\Lambda$. Thus
$$\operatorname{ev}_c\circ(j_{\Lambda,C}\otimes1_c)=e_\Lambda.$$
This is the defining adjunct identity, not an extra isomorphism theorem. On Hom-complex representatives [def-pur-hom-complex] it says that a degree-$r$ family $f$ acts on a section $x$ by $u_\Lambda(f(x))$; the differential on both sides is $d f-(-1)^r f d$. The same description defines $j$ after rationalization and at a common field stage. Use the symmetry constraint if evaluation is written with the input first. The adjunction inverse identities of [lem-pod-closed-uncurry-laws] give precisely the displayed identity, and give the corresponding identity for $j_{\Lambda',Q_sC}$.

Uses: lem-sf-point-fibre-derived-tensor, lem-pod-point-dualizing-complex, def-pur-hom-complex, lem-pod-closed-uncurry-laws.

### Returned step 6 — evaluation child

Write $\nu_q:qd\otimes^L qc\xrightarrow{\sim}q(d\otimes^Lc)$ for the scalar-extension tensor constraint and put $E=q(e_\Lambda)\circ\nu_q$, with $q\Lambda=\Lambda'$. Let $e' = e_{\Lambda'}$ be the pairing of step 5 for $Q_sC$. The definition of the canonical internal-Hom comparison $\delta_{Q,C}$ as the transpose of coefficient-changed evaluation gives
$$\operatorname{ev}_{Q_sC}\circ(\delta_{Q,C}\otimes1)=Q_s(\operatorname{ev}_C)\circ\nu_{Q_s},$$
including the stipulated comparison on the dualizing objects. After $u_{\Lambda'}$ this comparison is $Q_su_\Lambda$, since it is the identity-adjunction coefficient comparison. Apply $F_{\Lambda'}$ to this equality. Naturality of $t$ for $u_\Lambda\circ\operatorname{ev}_C$, and the tensor and unit compatibility of [lem-sf-point-fibre-derived-tensor], give
$$e'\circ\bigl((F_{\Lambda'}(\delta_{Q,C})\circ t_{Q,D_sC})\otimes t_{Q,C}\bigr)=E.$$
Here preservation of evaluation under coefficient change is supplied on the finite-Tor domains by [thm-sf-ctf-stability](vii), and at the other stated coefficient passages by [lem-fix-operation-reduction]. This proves an equality of the actual pairings before taking transposes.

Uses: lem-sf-point-fibre-derived-tensor, thm-sf-ctf-stability, lem-fix-operation-reduction.

### Returned step 7 — parent assembly

Let $L$ denote the left side of the asserted equation. Its tensor--Hom transpose is a pairing $qd\otimes^L qc\to\Lambda'$. Precomposition by $t_{Q,C}$ in the dual means that this pairing is
$$\operatorname{ev}_{F_{\Lambda'}Q_sC}\circ\bigl((j_{\Lambda',Q_sC}\circ F_{\Lambda'}\delta_{Q,C}\circ t_{Q,D_sC})\otimes t_{Q,C}\bigr).$$
By step 5 this is the left side of the last equality in step 6, hence is $E$. This uses only the evaluation formula for uncurrying and its naturality in [lem-pod-closed-uncurry-laws]; no invertibility of $\delta$ or of a dual-base-change arrow is used.

Uses: lem-pod-closed-uncurry-laws.

### Returned step 8 — parent assembly

Let $R=b_{Q,c}\circ q(j_{\Lambda,C})$. By definition the canonical module-dual comparison $b_{Q,c}$ is the transpose of coefficient-changed module evaluation. Its evaluation identity is
$$\operatorname{ev}_{qc}\circ(b_{Q,c}\otimes1_{qc})=q(\operatorname{ev}_c)\circ\nu_{q,c^\vee,c}.$$
Naturality of the tensor constraint therefore makes the transpose of $R$ equal to
$$q\bigl(\operatorname{ev}_c\circ(j_{\Lambda,C}\otimes1_c)\bigr)\circ\nu_q=q(e_\Lambda)\circ\nu_q=E,$$
by step 5. The same adjunction bijection [lem-pod-closed-uncurry-laws] gives equal morphisms from equal transposes, so $L=R$. The calculation takes place in each stipulated coefficient category; at $\overline{\mathbf Q}_\ell$ it is performed at a common finite coefficient field, as prescribed in [def-weil-finite-coefficient-point]. Both sides then represent the same morphism in the common-stage category. This proves the square for every listed $Q$.

Uses: lem-pod-closed-uncurry-laws, def-weil-finite-coefficient-point.

## Search results read

- loogle `CategoryTheory.MonoidalClosed, CategoryTheory.Adjunction`: CategoryTheory.MonoidalClosed.ofEquiv; CategoryTheory.MonoidalClosed.internalHomAdjunction₂_adj; CategoryTheory.MonoidalClosed.ofEquiv_curry_def; CategoryTheory.MonoidalClosed.ofEquiv_uncurry_def; CategoryTheory.Monoidal.Reflective.monoidalClosed; CategoryTheory.Monoidal.Reflective.closed; CategoryTheory.Monoidal.Reflective.instIsIsoAppUnitObjIhom; CategoryTheory.Monoidal.Reflective.isIso_tfae. Verdict: no match for the derived point statement.
- leanfinder `At an algebraically closed pro etale point exact sections commute with unbounded derived tensor by a finite quotient coefficient ring via the canonical sections tensor map`: KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale; Algebra.Extension.tensorCotangentSpace; KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply; KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap; Algebra.Generators.CotangentSpace.exact; Algebra.FormallyEtale.instTensorProduct; Algebra.Generators.Cotangent.exact; Algebra.Extension.tensorH1Cotangent. Verdict: no match for the derived point statement.
- grep `(eval|Eval).*(dual|Dual)|(dual|Dual).*(eval|Eval)`: Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean; Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean; Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean; Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean; Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean. Verdict: no match for the derived point statement.
- grep `(sections|globalSections).*(tensor|Tensor)|(tensor|Tensor).*(sections|globalSections)`: 0 hits. Verdict: no match for the derived point statement.
- grep `(eval|Eval).*(comparison|Comparison)|(comparison|Comparison).*(eval|Eval)`: 0 hits. Verdict: no match for the derived point statement.
- leansearch `Exact sections on an algebraically closed pro etale point commute with derived reduction of coefficients by a quotient ring as an isomorphism in the target coefficient derived category`: DerivedCategory.singleFunctorsPostcompQIso; Algebra.FormallyEtale.iff_comp_bijective; AlgebraicGeometry.stalkClosedPointIso; HomologicalComplexUpToQuasiIso.quotientCompQhIso; Algebra.Etale.formallyEtale; AlgebraicGeometry.stalkClosedPointIso_inv; DerivedCategory.quotientCompQhIso; Algebra.FormallyEtale.of_equiv. Verdict: no match for the derived point statement.
- loogle `CategoryTheory.Sheaf, CategoryTheory.MonoidalClosed`: instMonoidalClosedSheafOfHasSheafifyOfFunctorOpposite; LightCondensed.instMonoidalClosedSheafLightProfiniteCoherentTopologyModuleCat. Verdict: no match for the derived point statement.
- loogle `CategoryTheory.Functor.Monoidal, CategoryTheory.MonoidalClosed`: CategoryTheory.MonoidalClosed.ofEquiv; CategoryTheory.MonoidalClosed.ofEquiv_curry_def; CategoryTheory.MonoidalClosed.ofEquiv_uncurry_def; CategoryTheory.Monoidal.Reflective.monoidalClosed; CategoryTheory.Monoidal.Reflective.closed; CategoryTheory.Monoidal.Reflective.instIsIsoAppUnitObjIhom. Verdict: no match for the derived point statement.
- leansearch `Derived coefficient reduction and scalar extension preserve the point dualizing evaluation pairing including tensor and unit constraints`: LinearMap.IsPerfPair.restrictScalars_of_field; IsBaseChange.toDualBaseChange_tmul; LinearMap.IsPerfPair.dualEval; FGModuleCat.FGModuleCatEvaluation; RootPairing.root'In_corootSpanMem_eq_pairingIn; FGModuleCat.exactPairing; Module.DualBases.coeffs_apply; Module.dualPairing_apply. Verdict: no match for the derived point statement.
- loogle `CategoryTheory.MonoidalClosed.uncurry, CategoryTheory.ihom`: CategoryTheory.MonoidalClosed.uncurry; CategoryTheory.MonoidalClosed.uncurry_injective; CategoryTheory.MonoidalClosed.curry_uncurry; CategoryTheory.MonoidalClosed.curry_eq_iff; CategoryTheory.MonoidalClosed.eq_curry_iff; CategoryTheory.MonoidalClosed.uncurry_id_eq_ev; CategoryTheory.MonoidalClosed.uncurry_natural_left; CategoryTheory.MonoidalClosed.uncurry_natural_right. Verdict: no match for the derived point statement.
- leansearch `At a geometric point sections of the internal derived dual evaluate by module evaluation with the normalized point dualizing isomorphism`: Module.Dual.eval_apply; LinearMap.IsPerfPair.dualEval; PresheafOfModules.sections.eval; AlgebraicGeometry.Scheme.evaluation; smoothSheaf.evalAt; Module.Dual.eval; Module.dualPairing_apply; CategoryTheory.sheafSectionsNatIsoEvaluation. Verdict: no match for the derived point statement.
- leanfinder `The canonical identification of sections of a point dualizing internal Hom with the derived module dual is the transpose of sections of evaluation normalized by the identity adjunction`: ModuleCat.ihom_ev_app; Module.apply_evalEquiv_symm_apply; ModuleCat.ihom_coev_app; FGModuleCat.FGModuleCatEvaluation; FGModuleCat.FGModuleCatCoevaluation; Module.Dual.eval_comp_comp_evalEquiv_eq; Module.Dual.eval_naturality; FGModuleCat.FGModuleCatEvaluation_apply'. Verdict: no match for the derived point statement.
- leanfinder `The canonical global sections scalar change map for modules on a ringed topos point is a derived coefficient linear isomorphism for nonflat quotient rings`: Module.flat_of_isLocalized_span; ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat; Module.Flat.of_forall_exists_factorization; Module.Flat.iff_forall_exists_factorization; Module.FaithfullyFlat; Module.Flat.of_retract; Module.Flat.tfae_equational_criterion; Module.flat_of_isLocalized_maximal. Verdict: no match for the derived point statement.
- leanfinder `Coefficient change carries the point duality evaluation pairing to the target pairing through the canonical internal Hom comparison and strong monoidal sections comparison`: CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft; CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight; CategoryTheory.tensorLeftHomEquiv_whiskerRight_comp_evaluation; CategoryTheory.tensorRightHomEquiv_whiskerLeft_comp_evaluation; CategoryTheory.tensorRightHomEquiv; CategoryTheory.coev_expComparison; CategoryTheory.tensorLeftHomEquiv; CategoryTheory.tensorLeftHomEquiv_whiskerLeft_comp_evaluation. Verdict: no match for the derived point statement.
- leanfinder `Global sections of a dualizing Hom complex at a proetale geometric point intertwine the specified evaluation and the ordinary module dual evaluation, including adic completion and rationalization`: AlgebraicGeometry.Scheme.Γevaluation_naturality_apply; smoothSheafCommRing.ι_evalHom; AlgebraicGeometry.LocallyRingedSpace.Γevaluation_naturality_apply; AlgebraicGeometry.LocallyRingedSpace.Γevaluation_naturality; AlgebraicGeometry.Scheme.Γevaluation_naturality; AlgebraicGeometry.LocallyRingedSpace.Γevaluation_naturality_assoc; smoothSheafCommRing.ι_evalHom_apply; AlgebraicGeometry.Scheme.Γevaluation_naturality_assoc. Verdict: no match for the derived point statement.
- leanfinder `For point sheaf complexes of finite Tor amplitude applying sections to coefficient changed evaluation equals scalar extension of the sections evaluation pairing`: AlgebraicGeometry.Scheme.Modules.map_smul; CategoryTheory.Presieve.FamilyOfElements.isCompatible_map_smul_aux; ModuleCat.Tilde.res_const; CategoryTheory.Presieve.FamilyOfElements.isCompatible_map_smul; ModuleCat.Tilde.smul_section_apply; AlgebraicGeometry.Scheme.Modules.Hom.app_smul; ModuleCat.Tilde.toOpen; CategoryTheory.Sheaf.H. Verdict: no match for the derived point statement.
