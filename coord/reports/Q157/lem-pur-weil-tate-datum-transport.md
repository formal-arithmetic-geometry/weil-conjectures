# Q157 repair: lem-pur-weil-tate-datum-transport

## Files written

- `dag/nodes/sec-six-functors/lem-pur-weil-tate-datum-transport.json`: same statement, five assembly steps (1750 characters), status split.
- `dag/nodes/sec-six-functors/lem-pur-canonical-tate-arrow-naturality.json`: statement, status unsplit; no Mathlib match; no proof steps or proof dependencies.
- `dag/nodes/sec-six-functors/lem-pur-finite-tate-source-comparison-calculus.json`: statement, status unsplit; no Mathlib match; no proof steps or proof dependencies.
- `dag/nodes/sec-six-functors/lem-pur-finite-tate-source-structural-coherence.json`: statement, status unsplit; no Mathlib match; no proof steps or proof dependencies.
- `dag/nodes/sec-six-functors/lem-pur-iterated-tate-source-composite.json`: statement, status unsplit; no Mathlib match; no proof steps or proof dependencies.
- `dag/nodes/sec-six-functors/lem-pur-tate-source-field-comparison-descent.json`: statement, status unsplit; no Mathlib match; no proof steps or proof dependencies.
- `dag/nodes/sec-six-functors/lem-pur-tate-source-strict-system-identities.json`: statement, status unsplit; no Mathlib match; no proof steps or proof dependencies.
- `citations.json`: one verbatim statement quotation for every use in the five assembly steps.

## Attachments

None. Searches of the live `lean/WeilConjectures/` for the item tag and Tate/Weil datum notions found no declaration stating all the item. The nearby TraceEquivariance theorem is existential, finite-coefficient and sorried; its docstring explicitly says the library lacks the specified canonical Weil datum. Underived pullback/shift facts and pairing equivariance do not attach this statement. No Lean was written or compiled.

## WANTED

None newly required. The six lemmas are explicitly agent-extracted auxiliary claims from the existing source-datum argument, rather than misattributed numbered results of the literature. The original argument is preserved below.

## What was wrong and what changed

The return requires distributing the 9062-character proof into at least three independent tasks, rather than paraphrasing it. The sandbox contained no node, report or search history on arrival (only dispatcher marker files). I copied the current repository item, which has exactly the eight returned steps and the old reviewed split. That is the available returned baseline; there was no retained delivery to overwrite. No git command was run in the shared clone. All original item fields, including the exact statement, source, blueprint references, import/audit and maintainer metadata, are retained except worker-owned proof/search/split-report fields.

Six new nodes now expose arguments of comparable statement size (approximately 2300–2800 characters each). They are statement-only, not claims that these new proofs are finished. The statement of the item does not change. The full old proof is retained verbatim below, with its original citations and the extraction map. The old proof is neither shortened into a new universal transport lemma nor discarded. The explicit instruction to extract the returned arguments governs the clause-sized finite/composition lemmas: each is a strict part of the item, and none carries all coefficient stages and compatibilities.

## Return repair coverage

| Old step | Argument preserved | Statement-only task |
|---|---|---|
| 1 | Canonical pullback composition, tensor and shift coherence for b | lem-pur-finite-tate-source-structural-coherence |
| 2 | Projection maps on roots, power transitions, coefficient tensors, derived/ordinary line comparison | lem-pur-canonical-tate-arrow-naturality |
| 3 | Tensor powers, zero twist, additivity, degree-zero and even-shift signs | lem-pur-canonical-tate-arrow-naturality |
| 4 | Derived finite reduction of the complete defining composite | lem-pur-finite-tate-source-comparison-calculus (structural part also explicit in lem-pur-finite-tate-source-structural-coherence) |
| 5 | Cartesian square, directions of C_X and C_Y, the explicit transported datum | lem-pur-finite-tate-source-comparison-calculus |
| 6 | Iterated source expansion, three arrow factors, composition b, zero-dimensional cases | lem-pur-iterated-tate-source-composite |
| 7 | Natural simultaneous strict-system transformations and localized roofs before R lim | lem-pur-tate-source-strict-system-identities |
| 8 | Rational arrow action, finite scalar comparison, common-stage descent and domains | lem-pur-tate-source-field-comparison-descent |

## Not duplicates

lem-pur-finite-tate-source-structural-coherence vs lem-trf-derived-pullback-coherence: the latter states the triple pullback associativity equation; the new lemma identifies the b-specific tensor/shift diagrams, including coefficient and commuting-square comparisons.
lem-pur-finite-tate-source-structural-coherence vs lem-pur-derived-pullback-tensor-iso: the latter gives mu and its coherence, not the combined b structural diagram with the G_X and G_Y comparisons.
lem-pur-finite-tate-source-structural-coherence vs lem-trf-frobenius-pullback-comparison-coherence: that node splits powers of a single Galois pullback, not the pullback-tensor comparison of a smooth Tate source.
lem-pur-canonical-tate-arrow-naturality vs lem-wf-tate-twist-compatibility: that statement supplies a scheme-Frobenius E(1) arrow and commutation of the twist functor with finite scalar extension; it does not state geometric-Galois equivariance of the specified roots-derived arrows under arbitrary scheme pullback, finite/integral reduction, and additive tensor powers.
lem-pur-canonical-tate-arrow-naturality vs def-weil-frobenius-coefficient-twists: that is the definition of the arrows, not their naturality equations.
lem-pur-canonical-tate-arrow-naturality vs det-prop-sfb-cartesian-coefficients-twists: that gives underlying twist pullback isomorphisms and Kummer transitions, not the Frobenius-arrow equations.
lem-pur-canonical-tate-arrow-naturality vs lem-pur-roots-of-unity-inverse-image-iso: that gives power-transition compatibility, semilinearity and isomorphism for an isomorphism of schemes, not the resulting composite Frobenius/Tate coefficient and pullback diagrams.
lem-pur-finite-tate-source-comparison-calculus vs lem-fix-operation-reduction: that gives comparison isomorphisms of operations; the new node evaluates them on the specified source datum and states the typed intertwining equation.
lem-pur-finite-tate-source-comparison-calculus vs lem-trf-scheme-galois-coefficient-change: that concerns the kappa comparison between scheme and Galois Frobenii, not the source datum with Tate arrow.
lem-pur-iterated-tate-source-composite vs lem-trf-derived-pullback-coherence: pullback associativity alone has neither the tensor product of the two Tate arrows nor the even shifts and iterated source datum.
lem-pur-tate-source-strict-system-identities vs lem-coef-derived-system-evaluation-calculus: that provides the derived-system reduction functor, not the b/Tate/source identities of transformations before inverse limit.
lem-pur-tate-source-strict-system-identities vs lem-pod-integral-pullback-composition: that provides integral pullback comparison and associativity, not the full source composite as a strict-system identity.
lem-pur-tate-source-field-comparison-descent vs lem-pur-integral-operations-scalar-extension: that states scalar comparisons of the operations, not their equivariance on this canonical Tate source.
lem-pur-tate-source-field-comparison-descent vs lem-weil-integral-twist-scalar-coherence: that gives associators for underlying twist/scalar comparisons, not compatibility of the specified Weil arrows and source b.
lem-pur-tate-source-field-comparison-descent vs lem-wf-constant-twist-coefficient-comparison: that concerns a rescaled constant Weil line in a PBC coefficient equivalence; no PBC coefficient equivalence or scalar rescaling is used here.

The whole DAG and imported blueprint were searched before node creation. In addition to the named near matches above, blueprint searches for `Tate source` and `iterated source` found none; `Tate datum` found the purity and dual definitions only. `Frobenius comparison`, `roots of unity`, and `strict reduction` searches were read as well. Their definitions, compact-support constructions, and underlying comparisons do not state these claims. The new IDs are absent from the current repository; all six have the same blueprint ancestor as the item, via the item, and empty same_as. No new node asserts a Stacks tag, so there are no new same-tag pairs to justify. Sources 07A4 and 0D6D remain existing nodes.

## Mathlib search record

Every query was run with the prescribed msearch.py and retained in searches.jsonl, with the actual outputs saved in the sandbox. Each new node has LeanSearch, LeanFinder, Loogle, and grep. Two distinct natural-language phrasings were tried; for the three nodes whose LeanSearch was rate limited, an additional LeanFinder phrasing was run. Invalid Loogle identifier responses were retained honestly, followed by valid name/substring searches. Rate-limited LeanSearch calls are recorded unavailable. The item retains its historical searches and appends its actual current queries. No search was invented.

The finite-structural candidates Scheme.Modules.pullbackComp and pseudofunctor_associativity concern ordinary structure-sheaf modules, not the pro-etale derived constant-coefficient tensor/Galois diagram. The cyclotomicCharacter and modularCyclotomicCharacter hits concern roots in a ring, not sheaves or comparison transformations. The finite-comparison hits concern scheme pullback carriers and gluing. The composition shift hits only add shifts. The system hits concern Kaehler differentials/adic completion or the embedding singleFunctor, with no realized Tate comparison. The field hits concern free-module pullback or monoid localization. None specializes in one line to a new statement. No Mathlib leaves are claimed.

## Review by Q157

I read the current main-20261015 source-of-purity definition and the constituent-compatibility proof of prop-pur-weil-equivariance-compatibilities. The latter is an assembly paragraph, not a proof of these six auxiliary claims. I therefore label the extraction as agent work, retaining the old detailed arguments below. I also read the chapter and sk-thm-sf-package unit: the purity clause assembles the smooth-purity route; this extraction invokes no SGA source, exceptional base-change theorem, or replacement of that route. Stacks sites-cohomology.tex, labels lemma-derived-pullback-composition (0D6D) and lemma-pullback-tensor-product (07A4), were read at their actual statements and K-flat computations. They support the existing comparison nodes, not an attribution of the full new claims to Stacks.

For the structural node I checked the statement of each composition/tensor node: triple coherence is precisely an equality, the twofold comparison is normalized on flat-term K-flat representatives, and mu explicitly commutes with composition and coefficients. The new a_H uses C_Y in the input factor and G_X-prime(t) C_X in the twist factor, so both sides start at Q_X G_X P_f K. This is the comparison step the original proof expands. The geometric-square hypotheses are over k_0, ensuring commutation with the geometric-Galois maps.

For the canonical-arrow node I read the current roots inverse-image definition, its transition/semilinearity lemma, the underlying Cartesian twist theorem and local-free line theorem, and both twist definitions. The transition lemma alone is not cited for functoriality under a composite: that argument, using successive projection ring maps and adjunction, is retained in old Step 2 and allocated to this node. Nonnegative powers and coefficient units carry old Step 3; no negative powers or parity signs are silently added. Ordinary coefficient tensors are used only for the locally free line. All coefficient stages keep the specified roots construction.

For the finite-calculus node the structural and canonical-arrow nodes state exactly the two identities required to substitute into the defining composite. I checked old Step 4 uses derived reduction on K even though A_n to A_m need not be flat; old Step 5 uses phi-prime = Q_Y(phi) C_Y inverse, not C_Y in the other direction. For the iterated-source node I checked the three explicit factors, pullback composition, twist reassociation, and addition of even shifts in old Step 6. Its map J is oriented from iterated to composite, so the assembly takes its inverse for the orientation of the item. These are independent finite calculations, not one renamed theorem that restates the full item.

For the system node I read the derived-system calculus, integral operation construction, well-definedness theorem and integral composition theorem. The calculus really provides a functor on the derived category of actual coefficient systems. The well-definedness theorem is descent on K-flat representatives, not a theorem that arbitrary levelwise equalities lift. The new task therefore explicitly asserts natural identities of the prescribed system transformations before R lim, including all input arrows/roofs; old Step 7 supplies the retained local tensor and quotient calculation. For the field node I read the scalar-extension theorem and the detailed common-stage arrow prescription. The former states identity and tower compatibility; the latter conjugates operation-applied arrows by scalar comparisons. Old Step 8, now a separate task, includes that scalar comparison calculation and equality after a common finite extension. This does not assert equality of arbitrary lifts or pass to discrete non-torsion etale coefficients.

Assembly Step 1 cites the structural and canonical-arrow statements for their b diagrams and tau equations. Step 2 cites only the finite-calculus statement, whose full displayed equality gives both finite reduction and the exact Cartesian equation after the source C_X identification. Step 3 cites the iterated-source equality, then inverts J. Step 4 cites the system statement for the stronger pre-limit equality and its evaluation/limit consequences. Step 5 cites the field statement for localized equalities, scalar comparison and common-stage independence. I opened each of these six generated node statements and checked these clauses; citations.json quotes the statements verbatim. No assembly step relies on a proof of another node. No non-elementary assembly step exceeds 2000 characters.

I checked the edge cases K=0, empty X or Y, identity square, identity reduction m=n, n=m=1, d=0 and e=0, and identity and successive field extensions. Empty schemes and zero complexes give unique maps; identity comparisons use the canonical unit identifications. The degree-zero twist is the coefficient unit, so no Frobenius or tensor sign remains when d or e is zero. Even shifts ensure sign 1; no odd-shift variant is claimed. Finite reductions keep the stated finite-Tor domain rather than assuming flat quotients. Integral comparisons use one simultaneous reduction system, and common-stage equalities are independent only through the stated scalar associators. There is no statement dispute, counterexample, or statement correction.

I checked delivery-errors B–E: complete hypotheses and notion dependencies; no new proofs on unsplit nodes; actual source/place, valid TeX, honest searches and no false Mathlib match; no duplicate/hidden one-node replacement; every assembly fact comes from the cited statement; no use of a definition for an unstated theorem; no circular dependency introduced; no unjustified hypothesis or coefficient-category identification. The new-node graph is structural/tau -> finite/composition -> systems -> fields; the parent simply assembles it. Maintainer-owned item fields are unchanged.

## Retained original arguments (verbatim)

These are proof material for the assigned statement-only tasks. They are not proof steps in the new JSON nodes. The old statement and citations are preserved; the worker taking a new node can read its statement together with this exact original argument.

### Old Step 1

Allocated to: lem-pur-finite-tate-source-structural-coherence.

First work over $A_{E,n}$. Write $F_f=Lf^*$, $T_{r,X}=\Lambda_X(r)$, and $c_f:G_XF_f\cong F_fG_Y$. Use the canonical composition maps, not chosen isomorphisms between the same functors. Their triple-composition identity is [lem-trf-derived-pullback-coherence]. The tensor comparison $\mu$ of [lem-pur-derived-pullback-tensor-iso] is natural and compatible with composition and associativity. Thus the first arrow in the definition is precisely
$$b_{f,K}=(c_{f,K}\otimes1)[2d]\,\mu_{g_X;F_fK,T_{d,X}}[2d].$$
For a commuting square, its pullback comparison is the composition comparison along one path followed by the inverse comparison along the other. The triple-composition identity identifies the two ways of inserting a further $G$ into this comparison. Splitting a tensor before or after that insertion gives the same map by the composition identity for $\mu$. These are exactly the comparisons needed below for $b$, both for the square $(u,v,f,f')$ and for $(f,h,hf)$. All shifts are termwise shifts of complexes, so their pullback identifications commute with the displayed maps.

Original uses: def-pur-tate-datum, lem-weil-pbc-proetale-derived-pullback-composition, lem-trf-derived-pullback-coherence, lem-pur-derived-pullback-tensor-iso.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum.md; Displayed source-of-purity composite; expanded constituent calculation for prop-pur-weil-equivariance-compatibilities.

### Old Step 2

Allocated to: lem-pur-canonical-tate-arrow-naturality.

Check the Tate-line factor on roots of unity, before forming tensor powers. By [def-pur-roots-of-unity-inverse-image], $c^w_{\mu_N}$ is adjoint to $z\mapsto\operatorname{pr}^\sharp(z)$. For successive scheme maps the successive section maps send $z$ to $(\operatorname{pr}_1\operatorname{pr}_2)^\sharp(z)$, the same as the composite; taking adjoints gives the composition equation for $c^w_{\mu_N}$. In the commuting square $wg_{T'}=g_Tw$, its two paths therefore agree. The power transitions commute with these maps by [lem-pur-roots-of-unity-inverse-image-iso]. Taking their inverse systems and then tensoring with coefficients is precisely the construction of $\tau_1$ in [def-weil-frobenius-coefficient-twists]. The twist pullback isomorphisms exist by [det-prop-sfb-cartesian-coefficients-twists]. Consequently if $t_w: Lw^*T_{1,T}\cong T_{1,T'}$ and $C_w:Lw^*G_T\cong G_{T'}Lw^*$, then
$$t_w Lw^*(\tau_{1,T})=\tau_{1,T'}G_{T'}(t_w)C_{w,T_{1,T}}.$$
Changing coefficients sends a local tensor $z\otimes a$ to $z\otimes\bar a$, or $z\otimes\iota(a)$; applying $c^g$ on $z$ before or after this gives identical tensors. This proves the same coefficient equation for $\tau_1$. The line is locally free by [lem-pur-twist-sheaf-locally-free], so these ordinary coefficient tensors compute the derived coefficient tensors used here.

Original uses: def-pur-roots-of-unity-inverse-image, lem-pur-roots-of-unity-inverse-image-iso, def-weil-frobenius-coefficient-twists, det-prop-sfb-cartesian-coefficients-twists, lem-pur-twist-sheaf-locally-free.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum.md; Displayed source-of-purity composite; expanded constituent calculation for prop-pur-weil-equivariance-compatibilities.

### Old Step 3

Allocated to: lem-pur-canonical-tate-arrow-naturality.

For $r\geq0$, the definition of $T_r$ and $\tau_r$ is the $r$-fold tensor power of the line and its arrow, with the coefficient unit when $r=0$. Tensor the equations of Step 2 $r$ times, using the associativity compatibility of $\mu$. This gives those equations for $T_r$, including the unit case. Grouping the first $d$ and last $e$ tensor factors gives
$$T_d\otimes T_e\cong T_{d+e},\qquad \tau_d\otimes\tau_e=\tau_{d+e}.$$
After pullback this reads $\tau_{d,X}\otimes F_f\tau_{e,Y}=\tau_{d+e,X}$ under the twist identifications, by the pullback equation just proved. These are reassociations of a fixed tensor power of one specified arrow. Twists have degree zero, and all the shifts used are even; moving $[2e]$ past a twist or interchanging the two even shifts introduces sign $1$.

Original uses: def-coefficient-twists-detailed, def-weil-frobenius-coefficient-twists, lem-pur-derived-pullback-tensor-iso.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum.md; Displayed source-of-purity composite; expanded constituent calculation for prop-pur-weil-equivariance-compatibilities.

### Old Step 4

Allocated to: lem-pur-finite-tate-source-comparison-calculus.

Let $R$ denote derived finite reduction $A_{E,n}\to A_{E,m}$. Put $K'=RK$ and give it $R\varphi_K$ through $RG_Y\cong G'_YR$. Let $a_P:RP_fK\cong P'_fK'$ be the coefficient comparison. The pullback and tensor comparisons of [lem-fix-operation-reduction], together with the coefficient compatibility of $\mu$, identify $R(b_{f,K})$ with $b'_{f,K'}$ after inserting $a_P$ and $G'_X(a_P)$. Step 2 identifies $R\tau_d$ with $\tau'_d$. Applying $R$ to the defining composite, and using functoriality of tensor on arrows, therefore gives
$$a_P R\bigl((F_f\varphi_K\otimes\tau_d)[2d]b_{f,K}\bigr)
 =(F'_f\varphi_{K'}\otimes\tau'_d)[2d]b'_{f,K'}G'_X(a_P).$$
This is the required intertwining equation. It uses derived, not ordinary, reduction on $K$; local freeness was used only for the Tate line. All comparisons are restricted to the finite-Tor domains stated in the cited coefficient lemma.

Original uses: def-pur-tate-datum, lem-fix-operation-reduction, lem-pur-derived-pullback-tensor-iso.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum.md; Displayed source-of-purity composite; expanded constituent calculation for prop-pur-weil-equivariance-compatibilities.

### Old Step 5

Allocated to: lem-pur-finite-tate-source-comparison-calculus.

For the square in the statement put $C_Y:Q_YG_Y\cong G_{Y'}Q_Y$ and $C_X:QG_X\cong G_{X'}Q$. Thus $\varphi_{Q_YK}=Q_Y(\varphi_K)C_Y^{-1}$. The map $B_P$ is obtained by distributing $Q$ over tensor, applying $QF_f\cong F_{f'}Q_Y$ and $QT_{d,X}\cong T_{d,X'}$, and retaining $[2d]$. In $B_PQ(\varphi_{P_fK})$, substitute $\varphi_{P_fK}=(F_f\varphi_K\otimes\tau_d)[2d]b_{f,K}$. Naturality of the pullback-square comparison moves $QF_f\varphi_K$ to $F_{f'}Q_Y\varphi_K$. The Tate equation of Step 2 moves $Q\tau_d$ to $\tau_{d,X'}$ and the corresponding $G$-image of the twist comparison. Step 1 moves the remaining pullback/tensor factors of $Qb_{f,K}$ to $b_{f',Q_YK}$; its $Y$-factor is $C_Y^{-1}$ and its $X$-factor is $G_{X'}B_P$. Hence the composite is
$$(F_{f'}(Q_Y\varphi_K C_Y^{-1})\otimes\tau_{d,X'})[2d]\,b_{f',Q_YK}\,G_{X'}B_P,$$
which is $\varphi_{P_{f'}Q_YK}G_{X'}B_P$. The source is identified by $C_X$. This proves exactly the displayed square. This uses only pullbacks for the commuting square of $k_0$-morphisms; no exceptional exchange or scheme-Frobenius Cartesian square is invoked.

Original uses: def-pur-tate-datum, lem-weil-pbc-proetale-derived-pullback-composition, lem-trf-derived-pullback-coherence, lem-pur-derived-pullback-tensor-iso, det-prop-sfb-cartesian-coefficients-twists.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum.md; Displayed source-of-purity composite; expanded constituent calculation for prop-pur-weil-equivariance-compatibilities.

### Old Step 6

Allocated to: lem-pur-iterated-tate-source-composite.

For $X\xrightarrow fY\xrightarrow hZ$, expand the iterated source datum by applying the definition first to $h,K$ and then to $f,P_hK$. It applies $F_f$ to $b_{h,K}$ and to $F_h\varphi_K\otimes\tau_{e,Y}$, tensors the latter with $\tau_{d,X}$, and shifts by $2e+2d$. Use the composition identity of $\mu$ to distribute $F_f$ through this tensor, and the triple-composition identity to replace $F_fF_h\varphi_K$ by $F_{hf}\varphi_K$. The remaining arrow on the three unshifted factors is
$$F_{hf}\varphi_K\otimes F_f\tau_{e,Y}\otimes\tau_{d,X}.$$
The canonical identification $P_fP_hK\cong P_{hf}K$ groups the last two factors into $T_{d+e,X}$; its symmetry if needed has degree-zero twist factors. Step 3 sends their arrow to $\tau_{d+e,X}$. Step 1 identifies the initial pullback and tensor arrow with $b_{hf,K}$, now with shift $2(d+e)$. The result is precisely $(F_{hf}\varphi_K\otimes\tau_{d+e,X})[2(d+e)]b_{hf,K}$. This proves composition compatibility with the identification in either direction, since it is an isomorphism. The argument also covers $d=0$ or $e=0$, using the tensor unit.

Original uses: def-pur-tate-datum, lem-trf-derived-pullback-coherence, lem-pur-derived-pullback-tensor-iso, def-coefficient-twists-detailed.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum.md; Displayed source-of-purity composite; expanded constituent calculation for prop-pur-weil-equivariance-compatibilities.

### Old Step 7

Allocated to: lem-pur-tate-source-strict-system-identities.

At integral coefficients use the specified realized strict towers of [def-pur-tate-datum]. The reduction functor $\mathcal R$ of [lem-coef-derived-system-evaluation-calculus] sends arrows to arrows in the derived category of coefficient systems. Pullback and completed tensor use the simultaneous finite reductions of one flat-term K-flat representative, by [def-pur-integral-derived-operations]. Their descent is [lem-pur-integral-operations-well-defined]; composition has the reduction-compatible integral comparison of [lem-pod-integral-pullback-composition]. The calculations in Steps 1--6 are identities of these system maps: the site projections act on the sheaf variable, coefficient quotient maps on its coefficients, and the tensor maps on factors. For example both orders on a pure tensor send $(x\otimes a)\otimes b$ to the same pulled-back $x$ with coefficient $q_{n,m}(a)b$. Power maps on roots commute with quotient maps by Step 2. These identities are natural in chain maps, so also in their localized roofs, including the specified input datum. They therefore hold as transformations of realized derived systems, before applying $R\lim$. Functoriality then gives the same identities integrally. The integral-to-finite comparison is their evaluation, with the comparisons of [lem-fix-operation-reduction]. This proves the stronger tower assertion in the item; equality is not inferred from equality in the individual derived categories.

Original uses: def-pur-tate-datum, lem-coef-derived-system-evaluation-calculus, def-pur-integral-derived-operations, lem-pur-integral-operations-well-defined, lem-pod-integral-pullback-composition, lem-fix-operation-reduction.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum.md; Displayed source-of-purity composite; expanded constituent calculation for prop-pur-weil-equivariance-compatibilities.

### Old Step 8

Allocated to: lem-pur-tate-source-field-comparison-descent.

Rationalization is a functor on arrows, so applying it to the integral identities preserves both composites and their equality. The rational operations and their arrow action are exactly these localized operations. For a finite extension of coefficient fields, use [lem-pur-integral-operations-scalar-extension] and [lem-fix-operation-reduction] to identify pullback and tensor after extension. On the Tate factor the coefficient equation was proved on $z\otimes a$ in Step 2; on the input factor it is the transported datum, and on $b$ it is the coefficient compatibility of [lem-pur-derived-pullback-tensor-iso]. Thus the same calculation as Step 4 proves the scalar-extension square. These comparisons are compatible with identity and successive field extensions by the scalar-extension lemma. At $\overline{\mathbf Q}_\ell$ represent the finitely many objects, arrows and comparisons over a single common finite field; the equality just proved over that field gives equality of their morphism classes, independently of further extension. This is exactly the common-stage arrow prescription of [def-weil-derived-pullback-tensor-hom]. The bounded constructible finite-Tor domains are those of the input and of the named comparisons throughout; the argument makes no assertion about discrete non-torsion small-etale coefficients.

Original uses: def-weil-derived-pullback-tensor-hom, lem-pur-integral-operations-scalar-extension, lem-fix-operation-reduction, lem-pur-derived-pullback-tensor-iso.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-pur-tate-datum.md; Displayed source-of-purity composite; expanded constituent calculation for prop-pur-weil-equivariance-compatibilities.

## Could not finish

None of the requested repair is omitted. The new proof obligations are intentionally left unsplit for parallel stage-1 work, as the return requires. The first dry run rejected the phrase “as in the item” in assembly Step 3. I replaced it by the explicit identification $P_{hf}K\cong P_fP_hK$ and corrected the assembly source-step cross references; no mathematical statement or argument changed. The next dry run checks this repair before push.
