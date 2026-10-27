# Worker report

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-normalized-immersion-comparison-coherence.json (statement unchanged, split); lem-sfb-normalized-comparison-binary-restriction.json (new statement, unsplit, no Mathlib match); lem-sfb-normalized-comparison-tower-restriction.json (new statement, unsplit, no Mathlib match). citations.json supplies literal statement excerpts for every parent citation.
2. Attachments: none. The module Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence ends with `sorry` in normalizedImmersionComparisonCoherence (theorem line 296, sorry line 303); upstream WeilConjectures has no exact declaration for the item. The existing helper composite merely defines the arrow; it does not prove its normalization.
3. WANTED: none.
4. The returned head has 6055 proof characters in seven steps, making this item too large for one worker. The sandbox initially held only dispatcher brief markers, with no node/report/search log to continue. I recovered the delivered text from the current repository, preserved its statement and other metadata, and split two separate calculations. No statement dispute or route change is involved.
5. Nothing mathematical is left unfinished in the parent assembly; the two new nodes deliberately have no proofs so separate workers can prove them. Validation and push are recorded below after completion.

## Return repair and workload distribution

The binary node is the argument of former steps 1 and 3 (1989 characters); the tower node is the restriction calculation of former steps 6 and 7 (1750 characters), with equality detection left in the parent. Both have self-contained categorical statements, no proof steps, no proof dependencies, and status unsplit. They can be worked independently. They depend only on the definition of a category, not the parent. The parent assembly has 2651 characters and no step exceeds 2000. Former steps 2, 4, 5 and the final Hom-detection argument of step 7 remain in the parent. The exact old calculations are copied below rather than discarded or summarized.

The new nodes assert identities of whole natural transformations; neither is a degreewise consequence. The binary lemma does not assert equality with any chosen comparison for the composite; that requires parent uniqueness. The tower lemma deliberately asserts only equality after restriction without faithfulness; that is weaker than the parent's tower square and leaves its decisive extension-image argument in the parent. Neither new node restates a clause of the item.

## Sources and searches

Read main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md, especially (2)'s composition compatibility and (3)'s coefficient associativity, plus the chapter and unit records. These are the source route for the parent and both formal calculation nodes. The blueprint does not print the detailed normalization calculations: they are explicitly agent-extracted. No separate Stacks tag is claimed for these purely categorical identities. The geometric extension and its Hom bijection come exclusively from lem-sfb-locally-closed-extension-coherence, whose full statement I read; the parent's source already records the relevant proetale tags. No prohibited SGA route is used.

Searched the whole DAG by normalized comparison, restriction-normalized, binary normalization/restriction, tower paths and relevant source tags; searched the imported blueprint by tools/blueprint_refs.py for normalized comparison, restriction normalization, coefficient tower comparison and whisker. The nearest blueprint ancestor is det-prop-scalar-six-pullback; both new nodes have via=[lem-sfb-normalized-immersion-comparison-coherence]. No matching blueprint statement was found, so same_as is empty. Read the nearest candidate statements listed under Not duplicates. The exact parent tag and notion were searched in lean/WeilConjectures and the existing Sheaf module was read, including its proof placeholder and its comparison/composite/tower structures.

Every new node has two LeanFinder phrasings, a Loogle search, a grep through CategoryTheory, and a LeanSearch attempt, all actually executed by msearch.py and retained in searches.jsonl and search-*.txt. LeanSearch returned its rate-limit error and is recorded unavailable. LeanFinder found Dold--Kan equivalence cancellations, localCohomology.diagramComp, right Kan-extension comparison identities, CatCommSq naturality, ModuleCat.restrictScalarsComp' naturality, and small-object restrictions. Loogle and grep found basic naturality/whiskering statements. I read NatTrans.lean, Whiskering.lean, NatIso.lean and CatCommSq.lean around their naturality, composition, cancellation and horizontal/vertical-square definitions. None supplies the two specified normalization substitutions and their compositor/tower compatibility by a single specialization; the calculations require several distinct substitutions. These are not Mathlib leaves.

## Not duplicates

lem-sfb-normalized-comparison-binary-restriction vs lem-sfb-normalized-immersion-comparison-coherence: binary restriction normalization only; does not construct the family or prove factorization independence, composition equality, or tower coherence.
lem-sfb-normalized-comparison-tower-restriction vs lem-sfb-normalized-immersion-comparison-coherence: the common restricted value of two tower paths, with no faithfulness or conclusion that the unrestricted square commutes.
lem-sfb-normalized-comparison-binary-restriction vs lem-sfb-locally-closed-extension-coherence: the latter constructs geometric extensions, normalized compositors and Hom bijections, but has no functors F, q or comparison h.
lem-sfb-normalized-comparison-tower-restriction vs lem-sfb-locally-closed-extension-coherence: the latter has no coefficient functors or tower associator and supplies only the detection step used afterwards.
lem-sfb-normalized-comparison-binary-restriction vs lem-sfb-equivalence-square-inverse-mate-coherence: that statement requires equivalences and specified adjunctions and compares their mates; here F is arbitrary and L E is only supplied with rho, without an adjunction.
lem-sfb-normalized-comparison-tower-restriction vs lem-sfb-scalar-inverse-image-tower-diagram: that node proves the actual balanced-scalar q/t compatibility, which is a hypothesis (Q) here; it has no extensions E or comparisons h.
lem-sfb-normalized-comparison-binary-restriction vs lem-sfb-ringed-projection-tensor-composition: projection mates and their tensor coherence require ringed-topos adjunctions and tensor data absent here.
lem-sfb-normalized-comparison-tower-restriction vs lem-sfb-coherent-right-adjoint-comparisons: that node constructs comparisons between right adjoints from left-adjoint isomorphisms; these comparisons are already supplied, with no adjunction hypothesis.
lem-sfb-normalized-comparison-binary-restriction vs new-e5-normalized-fibre-comparisons: that node needs a preorder with least element and bijective restriction on natural endomorphisms to construct a global family; this node only computes one pair without faithfulness.

## Review by NN

I checked the actual parent statement and the two new statements against the source (2)-(3) and the returned argument, rather than treating the blueprint's word canonical as a proof. The parent has exactly the old scheme, coefficient, F/q, supplied open/closed comparison and conditional single-triple tower hypotheses. I retained its statement verbatim and did not require towers for all triples simultaneously. Both new statements introduce every category and arrow, explicitly define functional composition and canonical associators, and spell out (N), (G), (Q), and the conclusions; category is linked to def-nagata-category, whose statement is the ordinary category axioms. Other categorical notions mean the usual identity/composition-preserving maps, natural families, and invertible natural families used throughout the project.

Step 1 uses the extension statement's exact unbounded derived extension and canonical restriction isomorphism; the same statement says its gamma restricts to the identity, precisely (G). The Noetherian hypothesis is checked as quasi-compact plus locally Noetherian, and the supplied cartesian coefficient maps identify each restriction ring. Step 2 uses only the displayed Hom bijection in that statement. Conjugating by u and v explains detection for isomorphic extension images; this is an elementary three-line argument and does not assume global faithfulness. Step 3 cites the binary node's actual normalized-composite conclusion and the extension statement's factorization independence and alternate open-then-closed identification. The factor comparisons are isomorphisms and satisfy (N) by hypothesis. Uniqueness compares transformations with exactly the same source and target after gamma insertion, including those already open or closed. Step 4 cites the same binary conclusion for arbitrary immersions; normalization plus Step 2 proves equality and precomposition by invertible F(gamma) gives the precise displayed composition equation. Step 5 cites the tower node's common restricted-value conclusion, using all three proven normalizations and the given q/t equation; it then cites the extension Hom bijection with source object F_S^st F_S^rs M and target F_S^rt M. These objects need not coincide. The explicitly written source isomorphism is a composition of the constructed comparisons, so Hom detection applies. All citations quote the statements themselves in citations.json; none uses a proof of a dependency as an interface.

For the binary node I type-checked (G) as a transformation L_ab E_a E_b to the identity, (N) as L_k^s F E_k^r to F, and (B) as L_b^s L_a^s F_X E_a^r E_b^r to F_T. The q composition law has exactly this orientation; naturality with gamma^r removes its inverse. For the tower node both paths run from A=F_X^st F_X^rs E^r M to B=E^t F_S^rt M; every term of (L) runs from L^t A to F_S^rt M. Naturality of t at rho supplies the second path calculation, not an unassumed compatibility theorem. This is where the former long work now lives, as two independent queue items.

Small cases checked: all categories terminal and all functors identities make both lemmas tautological; identity immersions reduce the parent to supplied (N); a zero coefficient category causes no cancellation problem because rho stays invertible; coincident labels r=s=t impose only the explicitly specified maps. For a nonfaithful restriction, the tower node promises only equal images and therefore does not falsely infer equality of arbitrary arrows. For the parent its Hom detection is restricted to extension images and their isomorphic copies. No nonempty-scheme, nonzero-ring, boundedness, support preservation, or new comparison-existence assumption is introduced. There is no appeal to a common refinement or a globally faithful restriction.

I repaired the single numbered return by moving the two multi-substitution calculations to statement-only nodes of comparable original workload, preserving the remaining assembly and all original equations below. I checked delivery-errors B1-B10 (shape, self-contained notions, TeX, honest source/searches, no attachment), C1-C8 (all nonformal inputs cited, statements actually sufficient, no cycle or route substitution), D1-D5 (neither result is the whole item or a clause restatement), and E1-E7 (hypotheses, arrow types, small cases, explicit calculations). No proof step exceeds 2000 characters. No repository, launcher file or Lean source was written, and no compiler/build was run.

## Preserved argument plan for lem-sfb-normalized-comparison-binary-restriction

These are the returned proof's exact steps 1 and 3, retained as the plan for the statement-only binary node. Its generic categorical statement exposes precisely their data and assertions; the geometric applicability check remains parent Step 1.

Write $L_a^r=a_r^*$ and $\rho_a^r:L_a^rE_a^r\xrightarrow{\sim}1$. The cited extension theorem applies: quasi-compact and locally Noetherian is precisely its Noetherian hypothesis, and the cartesian coefficient identifications allow its inverse-image rings at every factor. We insert the coherent restriction-composition isomorphisms throughout, so $L_{ab}^r=L_b^rL_a^r$ denotes an identification, not a literal equality. Normalization of its composition maps says, at $M$,
$$\rho_{ab}^r\circ L_{ab}^r(\gamma_{a,b}^r)=\rho_b^r\circ L_b^r(\rho_a^r E_b^r).\tag{G}$$
For fixed $r,s$, a comparison $h_a:F_X^{rs}E_a^r\to E_a^sF_S^{rs}$ is normalized exactly when
$$\rho_a^s F_S^{rs}\circ L_a^s(h_a)=F_S^{rs}(\rho_a^r)\circ(q_a^{rs}E_a^r).\tag{N}$$
This gives a typed meaning to the statement's restriction requirement. The supplied open and closed comparisons satisfy (N) by hypothesis.

Here is the binary restriction calculation, for any normalized comparison isomorphisms $h_a,h_b$ for two composable immersions. Suppress $rs$ on $F,q$. Before inserting $\gamma$, set
$$H=(E_a^s h_b)\circ(h_aE_b^r),\qquad \eta^r=\rho_b^r\circ L_b^r(\rho_a^rE_b^r).$$
Naturality of $\rho_a^s$ with respect to $h_b$, followed by (N) for $a$, gives
$$\eta^s F_T\circ L_b^sL_a^s(H)=\rho_b^s F_T\circ L_b^s(h_b)\circ L_b^sF_S(\rho_a^rE_b^r)\circ L_b^s(q_aE_a^rE_b^r).$$
Apply (N) for $b$ and the naturality identity
$$q_b\circ L_b^sF_S(\rho_a^rE_b^r)=F_TL_b^r(\rho_a^rE_b^r)\circ(q_bL_a^rE_a^rE_b^r).$$
The result is
$$F_T(\eta^r)\circ(q_bL_a^rE_a^rE_b^r)\circ L_b^s(q_aE_a^rE_b^r).\tag{B}$$
The two $q$ factors are $q_{ab}E_a^rE_b^r$ by the assumed composition law. Equation (G) for each coefficient and naturality of $q_{ab}$ with respect to $\gamma_{a,b}^r$ therefore show that
$$\gamma_{a,b}^sF_T\circ H\circ F_X((\gamma_{a,b}^r)^{-1})$$
satisfies (N) for $ab$. This is a calculation with the supplied natural transformations and the cited normalized $\gamma$, valid for either order of open and closed factors.

## Preserved argument plan for lem-sfb-normalized-comparison-tower-restriction

These are the exact former steps 6 and 7. Their restricted-path calculation is the new node; their final cancellation and extension-image detection remain the parent assembly.

For the tower square fix $a:S\hookrightarrow X$ and $M\in D(S,r)$. Let $A=F_X^{st}F_X^{rs}E_a^rM$, $B=E_a^tF_S^{rt}M$, and let $h_L:A\to B$ be the left-hand path in the square. By naturality of $\rho_a^t$ with respect to $t_S$ and then (N) for $st$,
$$\rho_a^t F_S^{rt}M\circ L_a^t(h_L)=t_S(M)\circ F_S^{st}(\rho_a^s F_S^{rs}M)\circ q_a^{st}(E_a^sF_S^{rs}M)\circ L_a^tF_X^{st}(d_a^{rs}(M)).$$
Naturality of $q_a^{st}$ at $d_a^{rs}(M)$ moves the last arrow across $q_a^{st}$; functoriality and (N) for $rs$ give
$$\rho_a^t F_S^{rt}M\circ L_a^t(h_L)=t_S(M)\circ F_S^{st}F_S^{rs}(\rho_a^r(M))\circ F_S^{st}(q_a^{rs}(E_a^rM))\circ q_a^{st}(F_X^{rs}E_a^rM).\tag{L}$$
Each arrow has source $L_a^tA$ and the entire composite ends at $F_S^{rt}M$. This calculation uses the normalization already proved, not any additional coefficient-comparison theorem.

Let $h_R=d_a^{rt}(M)\circ t_X(E_a^rM)$ be the other tower path. By (N) for $rt$ and the given compatibility between $q$ and $t$,
$$\rho_a^t F_S^{rt}M\circ L_a^t(h_R)=F_S^{rt}(\rho_a^r(M))\circ t_S(L_a^rE_a^rM)\circ F_S^{st}(q_a^{rs}(E_a^rM))\circ q_a^{st}(F_X^{rs}E_a^rM).$$
Naturality of $t_S$ at $\rho_a^r(M)$ says
$$F_S^{rt}(\rho_a^r(M))\circ t_S(L_a^rE_a^rM)=t_S(M)\circ F_S^{st}F_S^{rs}(\rho_a^r(M)).$$
Substitution gives exactly (L). Cancel the invertible target map $\rho_a^t F_S^{rt}M$ to obtain $L_a^t(h_L)=L_a^t(h_R)$. To apply Step 2 here, the source is identified with $E_a^t(F_S^{st}F_S^{rs}M)$ by the isomorphism $d_a^{st}(F_S^{rs}M)\circ F_X^{st}(d_a^{rs}(M))$; the target is already $E_a^tF_S^{rt}M$. The Hom bijection for coefficient $t$ detects equality of these arrows even though these two objects on $S$ differ. Hence $h_L=h_R$, which is the required tower equation, naturally in $M$.

## Preserved remaining assembly

For comparison with the return, these are the exact former steps 2, 4 and 5; their arguments are retained in parent Steps 2-4.

Restriction detects equality between any objects already isomorphic to extension images. Indeed, for isomorphisms $u:A\xrightarrow{\sim}E_a^sP$ and $v:B\xrightarrow{\sim}E_a^sQ$, two arrows $f,g:A\to B$ with $L_a^s(f)=L_a^s(g)$ give equal restrictions of $vfu^{-1},vgu^{-1}$. Injectivity of the cited Hom bijection makes these conjugated arrows equal, hence $f=g$. In particular, if there is one comparison isomorphism $h_0:F_X^{rs}E_a^rM\xrightarrow{\sim}E_a^sF_S^{rs}M$, there is at most one comparison with the restriction prescribed by (N): use $u=h_0$ and $v=1$. Applying this argument at every $M$ proves equality of the natural transformations. No global faithfulness of $L_a^s$, and no support-preservation hypothesis on $F_X^{rs}$, is used.

For the closed-then-open factorization $a=vc$, define, with all functor arguments understood,
$$d_a=\gamma_{v,c}^sF_S^{rs}\circ(E_v^sd_c^{rs})\circ(d_v^{rs}E_c^r)\circ F_X^{rs}((\gamma_{v,c}^r)^{-1}).$$
It is an isomorphism, and Step 3 proves its normalization. The cited theorem identifies every other closed-then-open extension presentation with $E_a$, restricting to the identity on $S$. The comparison constructed with another factorization thus has the same domain, codomain and (N). Step 2, using the first constructed $d_a$ as its source isomorphism, proves equality. For a supplied open-then-closed factorization $a=iu$, repeat the displayed formula with $(i,u)$; the cited theorem supplies exactly its normalized extension identification. Step 3 normalizes this composite and Step 2 identifies it with $d_a$. This also handles immersions already open or closed: their supplied comparison satisfies (N), so agrees with the assembled one.

For arbitrary composable $a,b$, use their now constructed normalized $d_a,d_b$. Step 3 shows that
$$\widetilde d_{ab}=\gamma_{a,b}^sF_T^{rs}\circ(E_a^sd_b)\circ(d_aE_b^r)\circ F_X^{rs}((\gamma_{a,b}^r)^{-1})$$
is a normalized isomorphism. Both $\widetilde d_{ab}$ and $d_{ab}$ have domain $F_X^{rs}E_{ab}^rM$ and target $E_{ab}^sF_T^{rs}M$. Step 2 therefore gives $\widetilde d_{ab}=d_{ab}$. Precomposing with $F_X^{rs}(\gamma_{a,b}^r)$ gives precisely the immersion-composition equation of the statement. Thus no common refinement of factorizations, nor a separately assumed mixed-composition equation for $d$, is needed.

## Validation

The first required deliver.py --no-push invocation exited 0 with server preflight passed, at b88cae3f583. Its checks include check_dag and review_split. The only subsequent edit is this validation record and correction of the report’s Lean line reference to theorem line 296 / sorry line 303; a final dry run follows before the authorized push. Two new unsplit nodes, zero new Mathlib leaves.
