## Worker report

Files written:

- `dag/nodes/sec-proper-base-change/prop-weil-pbc-descent-functors.json`: existing statement unchanged; four-step assembly, below 3000 characters.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-pair-functor-shift-coherence.json`: one new statement-only lemma, status `unsplit`; six genuine Mathlib searches, no exact match, no Mathlib leaves.
- `citations.json`: a literal statement quotation for every use in each parent proof step.

Attachments: none for the whole item. The search of `lean/WeilConjectures/` by blueprint tag and descent/functor terminology found `CategoryTheory.StageSystem.Morphism.functor`, `tr_mapAt`, `Hom.mapAt_naturality`, `descNatTrans`, and the functor-composition comparisons. They cover the additive and transformation parts. `lean/Sheaf/Paper/PbcDescentFunctors.lean` has the general theorem `AlgebraicGeometry.Scheme.pbcDescentFunctors` but its concrete operations theorem `pbcDescentOperations` ends in `sorry` at line 593. There is no complete project declaration giving every clause of this item without an unfinished operation application. This is the explicitly requested re-split, rather than a request to reprove or rewrite those Lean files. The new statement packages shift descent and its inclusion comparison together; the private implemented constructions at lines 172–273 are useful reference material, not a new Lean delivery.

WANTED: none. All sources used were available. No compiler, Lake or build command was run, and no Lean was written.

What was wrong: the previous reviewed proof concentrated 5328 characters in one item. This delivery follows the 2026-10-21 human decision to expose a genuine independent subargument. It does not change any statement, hypothesis, source field, blueprint update, Lean record, review record or unit/chapter route. The current main-20261015 statement and separate `.proof.md` were read, and agree with the preserved statement. Old sources remain intact in the item's metadata.

Nothing mathematical is left unfinished in the assembly. The new shift lemma deliberately has no proof or proof dependencies: it is work available to the next stage-1 worker. Its argument is recorded below for that worker and the independent reviewer.

## Argument allocation

The new lemma isolates the shift construction and its zero/addition and inclusion compatibility; it has no conclusion about distinguished triangles, transformation descent, or geometric operations, so it does not restate the item or its exactness clause. A second new lemma for the additive construction or transformation descent would duplicate `lem-sbc-coherent-pair-functor-descent`. A further node for triangle preservation would consist of the three-line application of lifting, stage exactness, and closure under triangle isomorphism, so it stays in the assembly.

Previous steps 1–3 (typing the composite, transport/equivalence independence, functor laws and additivity) are the additive-functor portion of the existing `lem-sbc-coherent-pair-functor-descent`. Previous step 5 is its compatible-transformation and composition/equation portion. They are reused by statement, with no loss of their arguments. Previous step 4 is divided between the new shift-coherence node and the explicit triangle argument in new step 2. Previous step 6 remains new step 4, using the same rational transport and scalar comparisons. The old proof is retained verbatim at the end of this report so that these allocations can be checked against every original equation.

### Argument for the new statement-only node

Write $G$ for the already supplied representative-formula functor. For each integer $n$, consider the two stage families $K\mapsto\Phi_E(K[n])$ and $K\mapsto(\Phi_EK)[n]$. Their comparison maps are the composites of $\beta$ with the source and target scalar shift comparisons. Expanding the compatibility equation for the family $s_{E,n}$ gives exactly the displayed beta/shift equation in the new statement. Thus the existing compatible-transformation construction supplies a natural transformation between the corresponding pair functors. The comparison between a descended composite and the composite of the descended functors has identity components; identify the two functors in this way. The result has component $j_E^S(s_{E,n,K})=[E,s_{E,n,K}]$. Applying the same construction to the inverse components, or composing the components and using the identity law at $E$, gives a natural isomorphism.

For completeness the zero/addition check is a separate part of this argument, not hidden in the word natural. At $X=(E,K)$, all components of the zero equation are included $E$-stage components. Naturality of $\beta$ at an ordinary $E$-stage map $f$ gives $G(j_E^T(f))=j_E^S(\Phi_E(f))$; apply this to the source zero-shift identification. The pair zero-shift and the target zero-shift identifications are the images of the stage ones. The zero equation therefore is $j_E^S$ applied to the zero equation for $s_{E,0,K}$.

For addition, the source addition comparison at $(E,K)$ is the included stage comparison $K[n+m]\to(K[n])[m]$. The first factor $G(c^{\mathcal P_T})$ is its stage image by the preceding formula. The second factor is $j_E^S(s_{E,m,K[n]})$. The third factor, the $m$-shift of $j_E^S(s_{E,n,K})$, is $j_E^S((s_{E,n,K})[m])$ under the canonical inclusion comparisons. The final inverse addition comparison is also the included stage one. Their composite is therefore $j_E^S$ of the finite-stage addition equation, in exactly the order written in the statement. Equality at each object proves the natural-isomorphism coherence equation. This also handles negative integers; no induction restricted to positive shifts is used.

Lastly $G(j_E^T f)=j_E^S(\Phi_E f)$ makes the identity components a natural isomorphism $\kappa_E$. The two composite shift comparisons at $K$ both reduce to $j_E^S(s_{E,n,K})$, since the inclusion comparisons have identity components in the normalized pair models. Substituting the identity components of $\kappa_E$ gives the final displayed shift-compatibility square. This is the condition needed on the third arrow of an image triangle, not merely an isomorphism of underlying additive functors.

This argument follows the current blueprint's exactness sentence, with the details exposed by the already present `shiftHom`, `shiftIso`, `descendedCommShift` and `inclusionComp_commShift` in `lean/Sheaf/Paper/PbcDescentFunctors.lean:172–273`. I also read the pair-shift calculus and pseudocone propositions in `literature/blueprint/slopmaster2/src/version/sketch/42_qbarl_triangulated_colimit.tex:365–394,779–855`; these explain the comparison convention. That older document's outer envelope is not used. The new source stays the current main-20261015 proof. No Stacks tag claims to state this pair-category theorem; the source note's localization tags 05R7/05RJ are not substitutes for it and are not proof citations. No prohibited literature route is used.

## Not duplicates

lem-weil-pbc-pair-functor-shift-coherence vs lem-sbc-coherent-pair-functor-descent: the existing node constructs additive functors and transformations and extends to an envelope; it has no integer-shift structure or zero/add coherence or shift-compatible inclusion comparison. The new node assumes the prescribed additive functor and proves those shift assertions only.

lem-weil-pbc-pair-functor-shift-coherence vs prop-weil-pbc-common-stage-calculus: the existing node defines the pair categories' own shifts and the shift comparisons of their inclusions; it does not equip an arbitrary prescribed inter-system functor with a coherent shift structure.

lem-weil-pbc-pair-functor-shift-coherence vs prop-weil-pbc-scalar-extension: the existing node constructs scalar transition functors and their comparisons at finite coefficient stages, rather than the shift structure on a pair-category functor.

lem-weil-pbc-pair-functor-shift-coherence vs lem-zl-field-shriek-lower-bound-common-stage-exactness: the existing node concerns normalized geometric compact-support coefficient actions and depends on this parent item; using it here would be circular. It does not give this arbitrary additive stage-family shift lemma.

lem-weil-pbc-pair-functor-shift-coherence vs prop-weil-pbc-descent-functors: the new lemma assumes an additive representative-formula functor and concludes its shift laws and inclusion compatibility only. Exactness, descent of transformations/equations, and the geometric operation application remain separate arguments of the parent.

Searches before creation: the whole DAG was parsed for titles/statements mentioning pair categories, stage systems, finite/common stages, functors/transformations, and shift coherence. I searched the relevant Lean files for `tr_mapAt`, `mapAt_naturality`, `descNatTrans`, `shiftIso`, `descendedCommShift` and the item tag. Whole imported-blueprint searches used `pair categor`, `coherent functor`, `descent of coefficient`, `shift`, `shift comparison`, `shift coherence`, `natural transformations`, `commutes with shifts`, `pair-functor-shift`, `pseudocone`, and `exact pseudocones`; the ancestor command returned the item itself. No existing imported node states the new assertion. The new node's `from.place` identifies the exactness sentence and the old step 4 it refines, with empty via and same_as. The parent was already a blueprint node, so its from remains null.

Mathlib searches are the six entries in `searches.jsonl` and in the new node, exactly as executed. Both natural-language phrasings were read. LeanSearch was available and returned shift structures/fully faithful transfer/descent-data hits, not this assertion; it is not recorded as down. The Loogle results state formal CommShift compatibility operations, not the filtered pair construction. Read `Mathlib/CategoryTheory/Shift/CommShift.lean:138–169,470–507` and `Shift/Induced.lean:20–135`: the fully faithful and induced-shift constructors have additional universal/faithfulness hypotheses and change the shift structure, so they do not specialize in one line to this functor between already fixed pair shifts. No Mathlib leaf is claimed.

## Review by NP

I read the current blueprint statement and its separate proof file, the whole old six-step split, the statement of every cited node, and the exact Lean implementations noted above. The item's schemes, finite fields, scalar comparisons, raw rationalization convention, and pair-category coefficient interpretation agree with the current source. The new node states its own prime, closure, schemes, coefficient categories, functor $G$, object and representative formulas, all integer shift maps, the explicit beta tower and shift equations, and the complete zero/addition conclusions. Its additive-functor and triangulated terminology cites the corresponding definition nodes. It carries no proof sketch or steps in its statement. I removed the need for duplicate transport/transformation nodes after reading the existing generic additive result.

For step 1 I read `lem-sbc-coherent-pair-functor-descent` through its full statement. Its normalized transition and associator data are precisely those of the source and target scalar systems. The parent's exact $\Phi_E$ are additive; its beta unit and associator assumptions are the lemma's $b$ hypotheses. The statement explicitly gives the same object and conjugated-arrow formulas and independence of representative and stage. I checked the 28-node transitive dependency closure of that lemma: it does not contain this item. It is an off-unit generic tool, declared in split_report.tool_uses; its optional envelope conclusion is unused.

For step 2 I read the new statement's three conclusions: actual natural shifts, both coherence laws, and the shift compatibility of $\kappa_E$. These are what the step takes from it. `lem-weil-pbc-distinguished-diagram-lifting` explicitly lifts selected distinguished triangles, with the third arrow using $\sigma$, and recovers them through vertex isomorphisms; unlike ordinary finite-diagram lifting, it supplies distinguishedness at the chosen stage. `thm-weil-pbc-verdier-axioms` explicitly says every stage inclusion is exact. The exactness definition and the triangle-morphism definition justify the short assembly: naturality checks the first two squares, the new shift square checks the last, finite-stage exactness then gives a distinguished target stage triangle, and closure under triangle isomorphism concludes. This argument retains the original triangle comparison, including the third arrow. The Qbar definition explicitly identifies the pair category with the coefficient category; no completion or extension to an envelope is inserted. The existing triangle-lifting and Verdier nodes are in the coefficient construction unit and are used for exactly that construction; they do not replace the PBC unit route.

For step 3 the existing generic statement explicitly gives the compatibility equation for $\eta$, its components, functor-family composition with composite comparisons, and equations of transformations. I checked its formulas against the original naturality calculation. Vertical composition follows directly from the included component composite. Whiskering and horizontal composition use the lemma's functor-composition identification together with the included components; these are finite-stage categorical operations, and equations are checked at each $(E,K)$, not at an unspecified eventual stage. The proof text spells out these operations instead of silently assuming a stronger Yoneda or localization result.

For step 4 `prop-weil-pbc-rational-transport` says exactly that supplied exact integral operations and their supplied exchange extend to rationalized functors and a transformation. It does not claim arbitrary morphisms preserve integral constructibility. `prop-weil-pbc-scalar-extension` supplies coherent coefficient comparisons and explicitly identifies scalar extension of the exchange with the exchange at the larger coefficient stage; it also keeps the constructibility-preservation qualification. These are exactly the hypotheses needed for the first three steps, on all four schemes in the exchange square. The proof retains that qualification and does not prove an unwarranted geometric preservation theorem.

Small cases for the new assertion: at a single stage all beta comparisons are identities and $G=\Phi_E$, so the conclusion reduces to the original shift laws. For repeated fields the normalized unit and the associator equations give the same formulas, without an extra automorphism. At $n=0$ the stated zero equation has domain $G(X[0])$ and target $GX[0]$; for $n+m$ the four factors successively land in $G((X[n])[m])$, $(G(X[n]))[m]$, $((GX)[n])[m]$, and $(GX)[n+m]$, so their types and order match. Negative shifts and $m=-n$ use the full integer stage coherence. The zero object and zero maps give the included zero-map and shift isomorphisms, and an empty scheme is harmless. For the exactness assembly, zero/identity triangles are covered by the same lifting and stage exactness argument. No extra nonempty-scheme, positive-shift, faithful-transition, idempotent-completeness or common cohomological-bound assumption is used.

B–E checked substantively: the new node is statement-only with all objects/hypotheses introduced, single TeX escaping, honest searches and current blueprint provenance (B); every cited result was read by statement and quoted literally in citations.json, with the specialized finite-diagram/triangle distinction checked (C); no duplicate, parent-clause restatement or single replacement of the entire parent was made, and the genuinely routine triangle assembly remains inline (D); shift directions, associator order, repeated-stage units, arbitrary integers, the third triangle square and geometric preservation hypotheses were checked above (E). No statement dispute was found. The original report's claim that no auxiliary node was needed is superseded by the human's re-split request and the exposed shift subargument. No non-elementary parent step exceeds 2000 characters.

## Validation

The initial server `review_split` passed. The first full dry run required a longer quotation for the Qbar category identification in steps 2 and 4; both now quote the whole identifying paragraph. The full server dry run then exited successfully: `OK (not pushed) deliver/NP/prop-weil-pbc-descent-functors at 7134eb35bd9: preflight passed`. The final delivery command records the pushed commit.

## Previous proof retained for comparison

### Previous step 1

On objects set $\Phi(E,K)=(E,\Phi_EK)$. For a morphism represented by $(M,u)$, use the composite
$$
T^S_{M/E}\Phi_EK\xrightarrow{\beta_{M/E,K}}
\Phi_MT^T_{M/E}K\xrightarrow{\Phi_M(u)}
\Phi_MT^T_{M/F}L\xrightarrow{\beta_{M/F,L}^{-1}}
T^S_{M/F}\Phi_FL.
$$
Its source and target are the $M$-stage scalar extensions of the assigned objects, so it is a target morphism representative by the finite-stage pair-category definition. The comparison components are isomorphisms by hypothesis, and $\Phi_M$ is a functor.

### Previous step 2

Write $d_M(u)=\beta_{M/F,L}^{-1}\circ\Phi_M(u)\circ\beta_{M/E,K}$. For $M\subseteq N$ and $A\in\mathcal C_H(T)$ with $H\subseteq M$, the assumed associator equation for $\beta$ reads
$$\beta_{N/H,A}=\Phi_N(a^T_{N,M,H,A})\circ\beta_{N/M,T^T_{M/H}A}\circ T^S_{N/M}(\beta_{M/H,A})\circ(a^S_{N,M,H,\Phi_H A})^{-1}.$$
Naturality at $u$ reads
$$\Phi_N(T^T_{N/M}u)\circ\beta_{N/M,T^T_{M/E}K}=\beta_{N/M,T^T_{M/F}L}\circ T^S_{N/M}(\Phi_Mu).$$
Substitute the first equation at $(H,A)=(E,K),(F,L)$ and the pair-category formula $u_N=a^T_{N,M,F,L}\circ T^T_{N/M}(u)\circ(a^T_{N,M,E,K})^{-1}$ into $d_N(u_N)$. The inverse $\Phi_N(a^T_{N,M,F,L})$ cancels the left associator in $\Phi_N(u_N)$, and its right associator cancels $\Phi_N(a^T_{N,M,E,K})$. The displayed naturality equation then cancels the two remaining $\beta_{N/M}$ components, leaving
$$d_N(u_N)=a^S_{N,M,F,\Phi_FL}\circ T^S_{N/M}(d_M(u))\circ(a^S_{N,M,E,\Phi_EK})^{-1}.$$
This is exactly the target transport of $d_M(u)$. If $u_P=v_P$ witnesses equivalence, this equality gives equal target representatives $d_P(u_P)=d_P(v_P)$, so the assignment is well defined.

### Previous step 3

For the identity representative at $E$, the assumed unit equation $\beta_{E/E}=1$ gives $d_E(1_K)=1_{\Phi_EK}$. For composable maps $u:A\to B$ and $v:B\to C$ represented at one common stage $P$, the adjacent factors $\beta_{P/F,L}\circ\beta_{P/F,L}^{-1}$ cancel, giving $d_P(v)\circ d_P(u)=d_P(v\circ u)$. The transport equality of step 2 makes this calculation apply to the pair-category composition formula even when the initial stages differ. Also $d_P(u+v)=d_P(u)+d_P(v)$, since exact functors are additive and composition is bilinear. The common-stage calculus supplies the additive categories on which this is an additive functor.

### Previous step 4

Descend the stage shift comparison as a compatible transformation between the composites of the shift stage morphism and the given morphism. The betaCommShift equation is exactly Hom.comm after expanding the two composite comparisons. Its components are images of the finite-stage shift isomorphisms, hence yield a natural isomorphism on pair categories. Check zero and addition componentwise using the finite-stage CommShift laws and functor_map_ι. The comparison ιCompFunctorIso is compatible with this shift structure, because its components and the inclusion shift components are identities. By the common-stage distinguished-triangle criterion from [thm-weil-pbc-verdier-axioms], every distinguished source triangle is isomorphic to an included distinguished stage triangle. At that stage, the functor is exact, and the target inclusion is exact by the same Verdier theorem. Transport exactness through ιCompFunctorIso, then through mapTriangleCompIso and the given triangle isomorphism. Thus the descended functor preserves distinguished triangles. By [def-weil-pbc-qbar-category] these are the required coefficient categories.

### Previous step 5

For another compatible family $\Psi$ with comparison $\gamma$, let $\eta_E:\Phi_E\to\Psi_E$ be a compatible natural transformation. Compatibility means
$$\eta_{M,T^T_{M/E}K}\circ\beta_{M/E,K}=\gamma_{M/E,K}\circ T^S_{M/E}(\eta_{E,K}).$$
Define $\eta_{(E,K)}=[E,\eta_{E,K}]$. At stage $M$ the naturality square for $[M,u]$ is the equality
$$T^S_{M/F}(\eta_{F,L})\circ d_M^\Phi(u)=d_M^\Psi(u)\circ T^S_{M/E}(\eta_{E,K}).$$
Indeed, the left side is $\gamma_{M/F,L}^{-1}\circ\eta_{M,T^T_{M/F}L}\circ\Phi_M(u)\circ\beta_{M/E,K}$. Naturality of $\eta_M$ replaces its middle two factors by $\Psi_M(u)\circ\eta_{M,T^T_{M/E}K}$; compatibility then gives the right side. Step 2 ensures the equality defines an equality of classes independent of the chosen stage. Identity transformations descend to identities and vertical composites descend to composites because their components are $[E,1]$ and $[E,\theta_{E,K}\circ\eta_{E,K}]$. For horizontally composed families, the comparison is $\Phi_M(\gamma_{M/E,K})\circ\beta_{M/E,\Psi_EK}$; substituting it into $d_M$ gives precisely the composite of the two descended assignments. Whiskering and horizontal composition therefore agree with finite-stage operations as well. Every equation between compatible transformations, formed with these operations, holds componentwise already at $E$, hence holds between the descended classes.

### Previous step 6

The finite-stage rational transport proposition supplies the exact functors $Rf_{*,E}$ and $Lg_E^*$ and their exchange transformation on $\Dbc(-,E)$ (with the integral-operation hypotheses required there). The scalar-extension proposition supplies their coherent comparison isomorphisms and states that scalar extension of the exchange map is the exchange map at the larger stage. These are respectively the hypotheses for steps 1–4 and the compatibility equation in step 5, so they give the asserted exact functors and exchange transformation on the Qbar categories.
