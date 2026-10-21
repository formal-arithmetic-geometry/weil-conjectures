# Stage-1 repair: lem-pur-composite-integration-counit

1. Files written:
   - dag/nodes/sec-smooth-purity/lem-pur-composite-integration-counit.json: existing statement, unchanged verbatim; four-step assembly, 2705 characters, status split.
   - dag/nodes/sec-smooth-purity/lem-pur-tensor-action-trace-contraction.json: new statement-only generic contraction lemma, status unsplit, no Mathlib match, no proof or proof dependencies. This is work for another worker, not a completed proof.
   - citations.json: a verbatim statement quotation for every citation of each parent proof step.
   - report.md and searches.jsonl: this report and the actual msearch output log. repair.py and write_report.py are sandbox-only editing helpers, not delivery content.
2. Attachments: none. The recorded theorem WeilConjectures.PurityIntegration.compositeIntegrationCounit in lean/Sheaf/Paper/CompositeIntegrationCounit.lean ends in sorry. Searching the actual WeilConjectures source for the exact blueprint tag and the notion did not find a finished statement of the complete assertion. Its generic projection and monoidal-adjunction lemmas provide ingredients, not the assertion.
3. WANTED: none. The blueprint and Stacks sources needed here are available locally. The detailed calculation is explicitly agent-written, not attributed to a theorem of Stacks or to an omitted SGA proof.
4. The returned defect was granularity: 4984 proof characters in one node, despite seven short steps. The retained claim and all hypotheses are correct for the supplied-data assertion. The repair redistributes a real argument; it does not weaken or shorten the statement. The initial sandbox contained only .brief marker files, no retained node, report, citations or search log. I copied the current live node whose proof has exactly the returned 4984 characters. The original proof is preserved verbatim below for review and handoff.
5. Unfinished: the new lemma's Lean proof, intentionally deferred. Stage 1 alone is authorized. No Lean file was written, and no compiler, Lake or build command was run.

## Repair allocation

The new contraction lemma has no adjunctions, no compact-support compositor and no third pushforward functor. It concerns arbitrary functionals t_f and t_g, not specifically counits. It proves the factorization BEFORE composition comparison. The parent still proves that the actual counit is the corresponding expression, transports it through the actual compositor, and proves its unit value, naturality and both site clauses.

- Old Step 1: the actual composite-adjunction formula stays in parent Step 1, justified by the existing composite-adjunction Mathlib leaf. Its twist-first source reassociation is now the explicitly typed sigma_K in the new lemma and is applied in parent Step 1.
- Old Step 2: the new lemma's forward tensor-action hypothesis specializes at (L_f,L_g,P_g K). Inverting it gives the inverse-action identity from the old proof; applying t_f to its first factor gives d_{f,L_g tensor P_g K} = (a tensor 1) q_{f;L,P_g K} after sigma_K. This entire coefficient extraction is assigned to the new node.
- Old Step 3: the new lemma defines d_f and d_g with their actual unitors, so substituting these and using F_g's composition law produces exactly q_g F_g(a tensor 1) F_g(q_f). This is assigned to the new node.
- Old Step 4: the new lemma assumes natural projection isomorphisms, so their inverses are natural by multiplying the square by the inverses. Its first-variable square at a is q_{g;L_g,K} F_g(a tensor 1) = (F_g(a) tensor 1) q_{g;F_f L,K}. Combining t_g with F_g(a) gives its explicitly defined b. This is the remaining argument assigned to the new node. The displayed conclusion, not just its proof, gives precisely the factorization used by parent Step 1.
- Old Step 5 is retained in parent Step 2, with only the reference to the preceding step renumbered. It includes the inverted compositor equation, cancellation, substitution, the four-arrow trace and the two tensor symmetries.
- Old Step 6 is retained in parent Step 3, renumbered only. At the unit, the action identity gives q=q^2; invertibility forces q=1. This is not asserted by the new contraction lemma.
- Old Step 7 is retained in parent Step 4: inverse-projection naturality is written as its explicit square for h:K to K', composed with the trace and symmetries; the very same substitutions are made at the ordinary site under its own assumptions. The omitted introductory words only repeated that functors, counits and the compositor are natural. No comparison or transfer of a projection identity between sites is used.

This leaves 2705 characters of assembly in the parent. The old Steps 1--4 totaled 2531 characters; their algebraic calculation is now a separate task of comparable size to the parent's remaining compositor/unit/naturality task. I deliberately did not turn the elementary cancellation in old Step 5 into a second new node. No non-elementary parent step exceeds 2000 characters (the sole such step has 476).

## Search record

Before creating the new node I searched the whole DAG, the imported blueprint via tools/blueprint_refs.py, and both read-only project source roots. Blueprint searches included 'projection formula', 'inverse projection', 'tensor action', 'tensor-action', 'coefficient factorization', 'trace contraction' and 'counit'; statement-level DAG searches included projection/compositor, coefficient/counit, successive projection and trace contraction phrases. I opened the closest candidate statements listed below. The blueprint ancestor command returns lem-pur-projection-purity-agreement; the new node's via list contains the current item. No imported statement gives this generic contraction identity.

Seven searches actually ran via msearch.py: two LeanFinder phrasings, one LeanSearch query, two Loogle patterns and two source greps, copied verbatim with their actual log records into the new node. Both Loogle patterns and both source greps returned zero hits. LeanSearch returned monoidal-action associator naturality and module tensor associators. LeanFinder returned module endomorphism traces and rigid-dual-pair Hom identities. I read Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean around lines 491--505 and LinearAlgebra/Trace.lean around the trace_eq_contract declarations: they require a dual pair or finite free modules and compute a different kind of trace. They do not contract arbitrary functionals through arbitrary functors F_f,F_g with supplied projection maps. I also read Monoidal/Functor.lean:1036, map_mu_comp_counit_app_tensor: it concerns a monoidal adjunction's lax/oplax structure, absent from this lemma, and is not the required identity. Thus there is no exact match or one-line specialization. All services responded; no unavailable search is reported as absence.

The generic monoidal category and strong monoidal functor notions already have Mathlib definition nodes. They are reused as the only statement dependencies of the new node, without creating substitute definitions.

## Not duplicates

lem-pur-tensor-action-trace-contraction vs lem-pur-composite-integration-counit: the new statement contracts two arbitrary functionals through two projection actions before any compositor and assumes no adjunction; the parent identifies the actual composite counit through a specified third functor's compositor, proves its unit value and naturality and addresses both actual geometric sites. The parent retains those separate arguments.
lem-pur-tensor-action-trace-contraction vs lem-pur-composite-tensor-transpose: that statement compares adjoint transposes involving G_h(1), tau_h and arbitrary right adjoints; the new statement assumes no right adjoints at all, and contracts arbitrary L_f,L_g and functionals t_f,t_g. An adjunction with a prescribed arbitrary coefficient contraction is not supplied by that existing statement.
lem-pur-tensor-action-trace-contraction vs lem-pur-system-tensor-transpose-composition: that statement compares specific exceptional-adjoint transposes in normalized strict coefficient-system categories, with an invertible comparison rho; it does not state the arbitrary-functor contraction identity without adjoints or rho.
lem-pur-tensor-action-trace-contraction vs lem-pur-finite-projection-action-laws: the latter establishes the action law for the actual geometric maps and shares the blueprint source; the new lemma assumes this law and proves its consequence for two arbitrary trace functionals. They do not assert the same equality.
lem-pur-tensor-action-trace-contraction vs lem-pur-projection-formula-coefficient-coherence: the latter establishes unit and associativity for one geometric projection formula; the new lemma uses such associativity plus naturality of a second projection to contract two functionals.
lem-pur-tensor-action-trace-contraction vs lem-pur-tensor-trace-transpose: the latter identifies the adjoint transpose of one coefficient trace map through the dualizing object; the new lemma assumes neither a dualizing object nor an adjunction, and treats two functors.
lem-pur-tensor-action-trace-contraction vs lem-pur-trace-transpose-base-change: the latter transports trace transposes through a geometric base-change square; the new lemma has no base-change square or exceptional adjunction.
lem-pur-tensor-action-trace-contraction vs lem-amb-shriek-tensor-composition: the latter establishes compatibility of projection maps with the actual ordinary-etale compact-support compositor; the new lemma does not involve a compositor and instead uses tensor-action associativity to contract coefficient functionals.
lem-pur-tensor-action-trace-contraction vs lem-sf-composition-projection-mate: the latter establishes a geometric composition/projection identity; the new lemma contracts arbitrary trace maps before there is any third functor or composition comparison.
lem-pur-tensor-action-trace-contraction vs lem-pur-system-level-projection-formula-coherence: the latter constructs and proves the system-level projection/compositor identity; the new statement is a generic calculation in three monoidal categories, with no inverse limit, systems or compositor.
lem-pur-tensor-action-trace-contraction vs lem-pur-coprojection-composition-mate: the latter compares exceptional coprojection mates with an invertible coefficient twist; the new lemma has neither mates nor invertibility assumptions on L_f,L_g.
lem-pur-tensor-action-trace-contraction vs lem-trf-relative-kunneth-counit: the latter computes the ordinary adjoint transpose of the relative product Kunneth comparison for a Cartesian product; the new lemma has no product square or Kunneth map.

## Review by Q78

I read the current main-20261015 proof of lem-pur-projection-purity-agreement, in particular its final canonical-reassociations sentence, and the current live item's entire seven-step expansion. The snapshot does not print an 'Expanded Step 6': that historical locator describes the maintained expansion, not an extra paragraph of the source file. For the new node I read the same source paragraph and explicitly label its formula an agent expansion, keeping its proof_origin null because it is delivered unsplit. For the composite counit I read Stacks categories.tex, Tag 0DV0, lemma-compose-counits and equation-compose-counits, and the full existing definition node's statement. No SGA source is used.

For parent Step 1 I checked BOTH cited statements: def-weil-pbc-composite-adjunction explicitly gives epsilon_g composed with F_g(epsilon_f); the new contraction node explicitly gives d_g F_g(d_f) as (b tensor 1) times the iterated inverse projection. Substituting the supplied counit formulas makes d_f,d_g the actual counits in twist-first coordinates. Its arbitrary t_f,t_g may be the given unit counits, and a has the required type F_f(L_f tensor P_f L_g) to L_g. The domain assumptions include L_f,L_g,L, P_g K and every intermediate tensor/pushforward. The tensor comparisons of actual pullback supply the strong monoidal comparison used in sigma_K; this is an argument about their fixed maps, not a choice of a new adjunction.

For parent Step 2 I checked the equation's types before cancellation: both sides of the assumed projection/compositor equation go from F_gF_f L tensor K to F_gf(L tensor P_fP_g K). Its inverse really yields q_g F_g(q_f) alpha_source^{-1} = (alpha_L^{-1} tensor 1) q_gf. Postcomposition by t_g F_g(a) yields exactly the t_gf defined in the unchanged statement. The source and target symmetry maps restore coefficient-first order by naturality. This uses an explicit hypothesis and tensor functoriality, so the retained cancellation step is elementary and has no missing non-elementary citation.

For parent Step 3 I checked that the tensor unit lies in the supplied domains and that the gf action identity may be evaluated at both coefficient units. The canonical strong monoidal unit comparison and unitors identify its two sides as q and q^2. Invertibility, already a hypothesis, forces q=1. Thus the counit at the unit is the same four-arrow trace, with no need for faithfulness of evaluation at the unit.

For parent Step 4 I opened def-exchange-projection and read its statement, including that the maps are composites of specified natural transformations. It supplies naturality only; invertibility comes from the item's assumptions. Inverses are natural by composing the naturality square with their inverses. The explicit square in this step has source F_gf(L tensor P_gf K) and target F_gf L tensor K'. Composing with t_gf and symmetries gives the requested naturality in K. The ordinary-site clause imposes its own action/composition identities and its own closure conditions, so the same generic lemma applies there directly: no equivalence of sites or unproved comparison identity is inferred.

I checked the new statement independently of the parent: the forward action equation includes the correct associator directions; sigma_K goes from L_f tensor P_f(L_g tensor P_g K) to (L_f tensor P_f L_g) tensor P_fP_g K; each q and each functor image in the conclusion has the next factor's domain as its codomain. Its a and b are explicitly constructed, so there are no hollow objects. All nonstandard notions are defined in the statement or linked to the two existing definition leaves. It is a genuine lemma with a multi-stage coherence calculation, not a clause asserting the final composite counit and not the elementary inversion of a single assumed equality.

Small-case checks: with identity functors and the usual tensor projection in modules over a commutative ring, the equality sends x tensor y tensor z to t_f(x)t_g(y)z on both sides. Either zero functional makes both sides zero in this additive example. Taking K or L_g to be the tensor unit respects all displayed unitors and leaves the single remaining contraction. In a non-strict monoidal category the typed sigma_K and explicit lambda_B prevent an illicit strict identification; no braiding is needed by the new lemma itself. The parent's symmetries are the prescribed derived symmetries, not unsigned swaps. No smoothness, properness, invertibility of a trace, or restriction on the sign of a shift was added.

I checked delivery-errors B--E: the new node is self-contained and statement-only; its source locator distinguishes agent expansion from the printed blueprint; all searches are actual logged calls; the new generic result is distinguished from the closest existing statements above; every parent citation has a verbatim quote in citations.json; the elementary steps use only explicit hypotheses and functor/tensor laws; and the new node has no dependency on this item, so no new cycle is introduced. The full old argument below documents that no work disappeared in the re-split. The initial remote review_split check passed; the complete dry run and delivery result are recorded separately below when they finish.

## Original returned argument, preserved verbatim

### Original Step 1

Write composites right to left. By [def-weil-pbc-composite-adjunction] the actual composite counit before the compositor is
$$c_K=\varepsilon_{g,K}\circ F_g(\varepsilon_{f,G_gK}).$$
Put $L=L_{gf}$ and $B=P_gK$. Use the canonical tensor symmetries to write $G_uK$ as $L_u\otimes P_uK$, and put $q_{u;M,N}=\operatorname{PF}_{u;M,N}^{-1}$. The supplied factorization of each counit then reads
$$\varepsilon_{u,K}=(t_u\otimes1_K)q_{u;L_u,K}.$$
Here and below this formula includes the source symmetry and the target unit constraint. The source of $c_K$ is thereby $F_gF_f(L_f\otimes P_f(L_g\otimes B))$. Pullback's tensor comparison and the associator identify its inner argument with $L\otimes P_fB$. These are precisely the source identifications in the assertion; no adjunction different from the supplied one is chosen.

### Original Step 2

Invert the assumed tensor-action identity for $f$ and substitute $M=L_f$, $N_1=L_g$, $N_2=B$. With the preceding pullback/tensor identifications it gives
$$q_{f;L_f,L_g\otimes B}=(q_{f;L_f,L_g}\otimes1_B)q_{f;L,B}.$$
Define the particular morphism
$$a=(t_f\otimes1_{L_g})q_{f;L_f,L_g}:F_fL\longrightarrow L_g.$$
Substituting the supplied formula for $\varepsilon_{f,G_gK}$ and using bifunctoriality of tensor now gives
$$\varepsilon_{f,G_gK}=(a\otimes1_B)q_{f;L,B}.$$
The first equality is just the inverse of the hypothesis, and the second composes $t_f$ with its first tensor factor. Both formulas have domain $F_f(L\otimes P_fB)$ and codomain $L_g\otimes B$ in the second case.

### Original Step 3

Substitute the preceding equality and the supplied formula for $\varepsilon_{g,K}$ into $c_K$. Functoriality of $F_g$ gives the equality
$$c_K=(t_g\otimes1_K)q_{g;L_g,K}\,F_g(a\otimes1_B)\,F_g(q_{f;L,B}).$$
In particular $F_g(q_{f;L,B})$ ends at $F_g(F_fL\otimes P_gK)$, $F_g(a\otimes1_B)$ ends at $F_g(L_g\otimes P_gK)$, and $q_{g;L_g,K}$ ends at $F_gL_g\otimes K$. Thus every displayed factor is on the domains assumed closed under these composites.

### Original Step 4

The projection maps of [def-exchange-projection] are natural transformations in their two inputs; their inverses on the stated domain are therefore natural too (multiply the naturality square on both sides by the inverses). Apply this naturality in the first input to $a:F_fL\to L_g$:
$$q_{g;L_g,K}F_g(a\otimes1_{P_gK})=(F_g(a)\otimes1_K)q_{g;F_fL,K}.$$
Consequently Step 3 simplifies, by tensor bifunctoriality, to
$$c_K=(t_gF_g(a)\otimes1_K)q_{g;F_fL,K}F_g(q_{f;L,P_gK}).$$
Naturality supplies exactly this square, not an identification inferred only from an equality at $K=A_S$.

### Original Step 5

Invert the projection/compositor identity assumed in the statement, and multiply by the compositor inverses. At $M=L$ this gives
$$q_{g;F_fL,K}F_g(q_{f;L,P_gK})\alpha_{L\otimes P_fP_gK}^{-1}
=(\alpha_L^{-1}\otimes1_K)q_{gf;L,K}.$$
Indeed inverting the hypothesis first gives $\alpha_L\otimes1_K=\operatorname{PF}_{gf;L,K}^{-1}\alpha_{L\otimes P_fP_gK}F_g(\operatorname{PF}_{f;L,P_gK})\operatorname{PF}_{g;F_fL,K}$, and cancellation of its three right-hand invertible factors gives the displayed equality. Precompose Step 4 by $\alpha_{L\otimes P_fP_gK}^{-1}$ and use it:
$$c_K\alpha^{-1}=(t_gF_g(a)\alpha_L^{-1}\otimes1_K)q_{gf;L,K}=(t_{gf}\otimes1_K)q_{gf;L,K}.$$
The last equality expands the definition of $a$, giving exactly the four arrows defining $t_{gf}$ in the statement. Finally insert the source symmetry $P_{gf}K\otimes L\cong L\otimes P_{gf}K$ and the target symmetry $F_{gf}L\otimes K\cong K\otimes F_{gf}L$. Naturality of the latter symmetry changes $t_{gf}\otimes1_K$ into $1_K\otimes t_{gf}$, so this is the claimed formula with $\Pi_{gf;L,K}$.

### Original Step 6

Take $K=A_S$. With pullback's unit comparison and the tensor unitors, $q_{gf;L,A_S}$ is the identity. One can check this from the assumed action law alone: specialize it to $N_1=N_2=A_S$ and identify $L\otimes P_{gf}A_S$ with $L$; it says $q=q^2$. Since $q$ is invertible, cancellation gives $q=1$. Thus Step 5 at the unit is $\varepsilon^{\mathrm{comp}}_{A_S}=t_{gf}$ under the same compositor and unit identifications.

### Original Step 7

Every expression used in Steps 1--5 is natural in $K$: the counits and compositor are natural, $P_f,P_g,F_f,F_g$ are functors, and $q$ is the inverse of the natural projection transformation [def-exchange-projection]. More explicitly, for $h:K\to K'$ its naturality in the second input gives $(1_{F_{gf}L}\otimes h)q_{gf;L,K}=q_{gf;L,K'}F_{gf}(1_L\otimes P_{gf}h)$; composition with $t_{gf}$ and the two symmetries gives the claimed naturality square. The calculation has used only the stated adjunctions, tensor action, naturality and projection/compositor equation. For ordinary etale categories repeat Steps 1--6 with their own functors, adjunctions, compositor and projection maps. The assertion expressly imposes the same identities and closure assumptions on those actual maps, so each displayed substitution has the same type there. This proves the ordinary-site clause without identifying the two sites or transferring an unproved projection identity between them.

