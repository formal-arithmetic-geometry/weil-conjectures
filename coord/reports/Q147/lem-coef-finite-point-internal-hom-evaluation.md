# Worker report

1. Files written: the item `dag/nodes/sec-six-functors/lem-coef-finite-point-internal-hom-evaluation.json` (statement unchanged, status split); three new statement-only nodes in the same directory, listed below; `citations.json`; and this report. Search evidence is retained in `searches.jsonl` and the sandbox `search-results/`. The initial sandbox contained only dispatcher brief markers, so I recovered the returned proof from the current read-only repository. No earlier sandbox node, report or search log was overwritten. The live Q05 and NN reports are preserved verbatim in the last appendix.

- lem-coef-finite-point-counit-unit-normalization: statement, unsplit, no Mathlib match; old step 1, 1244 characters of argument.
- lem-coef-finite-point-reconstructed-hom-model: statement, unsplit, no Mathlib match; old steps 2 and 3, 2283 characters of argument, with the same resolution calculation stated also for arbitrary target complexes.
- lem-coef-finite-point-reconstructed-evaluation-square: statement, unsplit, no Mathlib match; old steps 4 and 5, 2196 characters of argument.

2. Attachments: none. I searched `lean/WeilConjectures/` for the exact blueprint tag, finitePointInternalHom names, and the point/Hom notions. The current etale declaration `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual` at `lean/WeilConjectures/SixFunctors/Etale/Derived/Point.lean:436` is now a proof without a local sorry, contrary to the historical Q05 report. I read its statement and its auxiliary theorem at line 398. It asserts an existential object isomorphism on the etale site; it does not state the specified pro-etale comparison counit, the actual evaluation transpose, or its naturality equation. It is not an exact attachment. The project's own theorem in `lean/Sheaf/Paper/FinitePointInternalHomEvaluation.lean` still has `sorry` as its whole proof and is not an attachment either. No Lean source was written or compiled.

3. WANTED: none. All sources used here are present locally.

4. The return requests distribution of a 5723-character argument, not abbreviated prose. I kept the entire item statement, all existing provenance and historical search records, and extracted three independent tasks with comparable proof workloads. The parent now assembles their actual statements in three steps, below 3000 characters. Each child has `proof: []`, `proof_deps: []`, `proof_origin: null`, status unsplit and no hidden proof sketch inside its statement. No child asserts the entire item: normalization contains no Hom comparison; the resolution-model node contains no exceptional normalization or evaluation assertion; the evaluation-square node assumes a supplied normalization and asserts its compatibility, leaving invertibility to the other two nodes.

5. Nothing remains unhandled in this one-level split; proofs of the new tasks deliberately remain for subsequent workers. The required dry run and push follow this report. No agent was started; no repository/launcher file was edited; no git command, Lean compiler, Lake or build tool was run by me.

## Repair mapping and preserved arguments

The returned/current-repository proof is reproduced verbatim below, partitioned by the new task that carries it. These are worker handoff arguments in the report, not proof fields in statement-only children. No argument was removed: finite coefficient finiteness and the actual triangle-identity inverse go to the normalization task; exact sheafification, exact ambient sections, constant values, adjunction formulas, bounded finite sections, reconstruction, K-flat/K-injective models and Hom differential go to the Hom-model task; finite-Tor typing, canonical tensor balancing, the sign calculation, cancellation by the reconstruction triangle and naturality for inverse quasi-isomorphisms go to the evaluation task.

The resolution-model statement permits an arbitrary ambient target V. This is the same argument as the old B-target computation: choose V -> J, exact sections preserves this quasi-isomorphism, exact L makes Gamma J K-injective by Stacks 08BJ, and the degreewise adjunction gives the identical q formula with J instead of I. For V=B it is exactly the returned calculation, including A -> Gamma I. No constructibility or finite-Tor hypothesis on an arbitrary V is silently assumed. The final signed task uses an arbitrary supplied alpha:V~B; it does not reconstruct the exceptional object and hence can be proved independently of the normalization task. Only the parent substitutes the required actual counit.

## Searches and sources

Read the six-functors chapter and the unit sk-prop-sf-biduality-general. Read main-20261015's `lem-pod-point-dualizing-complex.proof.md` opening paragraph and `prop-coef-integral-dualizing.proof.md` second paragraph. The latter is the nearest blueprint ancestor returned by `tools/blueprint_refs.py ancestor`. All children record this ancestor, the precise clause, and the item in `via`; `same_as` is empty after searching.

Before creating nodes I searched the whole DAG by point/Hom/normalization/counit/evaluation words, exact new ids and Hom-comparison symbols, and ran the blueprint search for point/internal, identity/dualizing, evaluation/counit and broader point/Hom words. I opened the closest matching node statements, including all lem-pod point reconstruction, Hom evaluation, integral normalization, dual evaluation transport, identity compact support normalization and ringed evaluation model results discussed below. No existing node states one of these three whole tasks. No existing node was modified.

For each new node the authorized msearch.py command ran LeanFinder twice with different phrasings, Loogle, source grep, and LeanSearch. The exact query text and full returned results are in each node and the authenticated search log. I read all hits. The normalization searches find GammaSpec, restriction, constant-sheaf and condensed counits plus generic adjunction lemmas, not this exceptional/site-comparison composite. The Hom-model searches find constantSheafGammaAdj, GammaHomEquiv and constantness criteria, not the derived arbitrary-target reconstruction comparison. The evaluation searches find light-condensed underived ihom sections and generic currying; the apparent `expComparison_ev`/`MonoidalClosedFunctor.comparison_iso` match was checked in `Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean:43-130`: it assumes Cartesian monoidal structures. Here tensor is derived module tensor, so that is not a one-line specialization. The existing mathlib currying inverse laws only handle the final formal uniqueness. LeanSearch was rate-limited for the first two tasks and is recorded as unavailable, not no-match; the evaluation LeanSearch succeeded. Both other semantic services and all three greps ran. The parent already had three-kind historical searches, retained unchanged.

I also read Stacks `sites-modules.tex`, Tag 03EI, label lemma-sheafification-exact; `sites-cohomology.tex`, Tag 06YS, label lemma-K-flat-resolution, and Tag 07A4, label lemma-pullback-tensor-product; and `derived.tex`, Tag 08BJ, label lemma-adjoint-preserve-K-injectives (and the K-injective localization criterion). These validate the models and hypotheses of the existing tools. The new nodes' source is the blueprint opening paragraph, whose omitted computations are expanded by the existing tools; their sources do not pretend that Stacks states the entire finite-exceptional normalization. No SGA source is used.

## Not duplicates

lem-coef-finite-point-counit-unit-normalization vs lem-pod-identity-compact-support-normalization: the existing node gives compact support identity, including the integral reduction-limit unit; the new node identifies the finite exceptional object's transported presentation and specifies its pro-etale comparison counit and inverse, which are not the former's conclusion.
lem-coef-finite-point-counit-unit-normalization vs lem-sf-point-identity-admissibility: the existing assertion concerns an optional ambient identity adjunction/admissibility datum and all stages; the new task computes the unconditional finite etale-adjoint transport and its comparison counit on B only, without identifying the ambient transported functor with identity.
lem-coef-finite-point-counit-unit-normalization vs lem-pod-point-dualizing-complex: the existing all-stage point duality statement does not specify the comparison-counit presentation and its exact inverse proved here.
lem-coef-finite-point-reconstructed-hom-model vs lem-pod-point-derived-hom-evaluation: the existing statement assumes exactness and Gamma B=A and takes target B; the new node verifies the finite-point realization hypotheses, reconstructs C, and computes the natural derived comparison for every ambient target V.
lem-coef-finite-point-reconstructed-hom-model vs lem-pod-point-sections-reconstruction: the existing conditional counit theorem does not compute any arbitrary-target derived Hom comparison or its resolving representatives.
lem-coef-finite-point-reconstructed-hom-model vs lem-pod-point-hom-complex-adjunction: the existing node gives q for ordinary complexes without deriving, exactness or reconstruction; the new statement includes the K-injective target argument, localization independence and the reconstructed derived map Q.
lem-coef-finite-point-reconstructed-hom-model vs lem-pod-point-integral-evaluation-normalization: the existing finite/integral coefficient-unit duality theorem does not give the arbitrary ambient target derived comparison of this task.
lem-coef-finite-point-reconstructed-evaluation-square vs lem-pod-point-derived-hom-evaluation: the existing signed square is for the extension input Lc and target B under conditional hypotheses; the new task identifies the square for reconstructed C and an independently supplied alpha:V~B, verifies the restricted tensor domain and asserts the derived naturality after transport.
lem-coef-finite-point-reconstructed-evaluation-square vs lem-pod-point-integral-evaluation-normalization: the latter gives the coefficient-unit kappa isomorphism and relates it to a specified duality map j; this task concerns the explicit arbitrary-normalized-target Q-composite and its evaluation/naturality squares, without assuming j or concluding kappa invertibility.
lem-coef-finite-point-reconstructed-evaluation-square vs lem-pod-point-dual-evaluation-transport: the latter starts with the specified point-duality isomorphism j and proves coefficient-change compatibility; this task assumes no j, uses no coefficient change, and identifies the reconstruction-defined comparison itself.
lem-coef-finite-point-reconstructed-evaluation-square vs lem-pod-point-tensor-hom-evaluation: the existing chain-level square assumes IsComparison on extension complexes; this new task carries its derived reconstruction transport, alpha normalization and finite-Tor domain checks.
lem-coef-finite-point-reconstructed-evaluation-square vs lem-sf-point-ringed-evaluation-model: the existing node gives tensor balancing/braiding for the ordinary ringed point, not internal-Hom evaluation under the reconstruction counit and arbitrary target normalization.

## Review by Q147

I checked the unchanged item and the three new statements against the two blueprint paragraphs named above, with the returned proof and every old cited statement open. The return has one substantive demand: spread all arguments among at least two comparable, unsplit tasks while keeping the parent assembly under 3000 characters. This repair supplies three tasks (old proof workloads 1244, 2283 and 2196 characters); the whole former proof is retained below and assigned clause by clause. The added arbitrary-target formulation isolates a genuine resolution argument instead of renaming the original theorem. It is checked by replacing B -> I with V -> J throughout; exactness of L and Gamma, not finite cohomology of V, is what the proof needs.

Parent step 1 cites only lem-coef-finite-point-counit-unit-normalization. Its statement explicitly gives the finite ring, the identity-compactification presentation and alpha=epsilon_B with inverse nu*(eta_G). These are exactly the claims the step takes. All finite-field, ell!=p, finite extension and positive exponent hypotheses are those of the item. The normalization task preserves the nonarchimedean hypothesis of lem-weil-l-adic-extension-absolute-value, the DVR/finite residue assertions of lem-weil-l-adic-extension-integers-dvr, and clause (2) of lem-weil-valued-dvr-finite-quotients. The bounded-below unit of thm-weil-pbc-site-comparison applies to G in degree zero. The triangle identity is used on nu*G, not on every arbitrary pro-etale object. The identity etale adjoint is normalized by its identity Hom bijections.

Parent step 2 cites only lem-coef-finite-point-reconstructed-hom-model. Its statement supplies actual exact functors, the fixed constant-value isomorphism, the actual reconstruction counit, resolving-model q and derived isomorphism Q for arbitrary V. At V=B its target is RHom(c,A), exactly as used. Composing with the isomorphism alpha from step 1 has the correct covariant Hom direction; precomposition with e_C has the correct contravariant direction. No non-elementary fact is hidden in saying that a functor carries an isomorphism to an isomorphism. The task retains old step 2's explicit adjunction formulas: L is exact from sectionwise exact constant presheaves plus 03EI; Gamma is exact on all point modules by lem-weil-point-proetale-sections-exact; clause (1) of lem-pod-connected-constant-h0 applies because Spec k is nonempty, connected, separated and finite type. The conditional lem-pod-point-sections-reconstruction then applies to bounded constructible C. The fibre/sections-finiteness definition supplies bounded finite c. For q the flat-term K-flat representative exists on the one-object ringed site by 06YS; the K-injective module target follows by 08BJ from exact L. The existing chain adjunction statement says q is exactly h evaluated on 1 tensor x; its Hom differential is the same on both sides. This is why the derived formula is meaningful even for an unbounded, nonconstructible arbitrary target.

Parent step 3 cites only lem-coef-finite-point-reconstructed-evaluation-square. Its statement actually gives H in D^b_ctf, the exact pairing equation, identification as transpose and the naturality equation, so this step does not cite a definition for an unstated theorem. I corrected the provisional citation of def-weil-derived-pullback-tensor-hom: its public statement does not itself say the needed adjunction uniqueness. The signed task now names the actual closed-structure definition def-coef-ringed-tensor-hom-model, which does define the adjunction, evaluation and transposition. The parent merely identifies the uniquely specified map. In the task's argument, cor-weil-finite-constructible-hom applies on the pro-etale point with X=s, d=0 and L=B; B has one finite constant stratum and Tor amplitude [0,0]. Thus the restricted point tensor theorem really applies to (H,C). The given alpha transports this membership from RHom(C,B); V is not assumed constructible without justification. The old q evaluation formula and canonical sections balancing are in lem-pod-point-derived-hom-evaluation; the explicit chain analogue in lem-pod-point-tensor-hom-evaluation covers ordinary q. On x of degree i and h of degree j both sides give (-1)^(ij)h(1 tensor x); the Hom-first formula follows by the same braiding. Gamma(e_C)u_c=1 removes the reconstruction insertion. Naturality f e_C=e_C' L(Gamma f) gives the displayed contravariant square in the correct direction. Since Q is natural in the derived categories, the argument covers inverse quasi-isomorphisms, not just chosen complex maps.

B--E checks: each child is self-contained, introduces its coefficient objects, supplies definition dependencies, and has no proof fields filled. TeX is encoded once. All searches are actual recorded command results; no returned hit was silently declared absent. Duplicates and potential specializations were inspected as above. The parent uses exactly the three new statements and its proof_deps is their union; citations.json quotes the full actual statement of each, so every clause taken is verifiable verbatim. Child statement dependencies point only to existing definitions/comparisons and the Hom-model task as needed for Q; no child depends on this parent. No cycle back to the item is introduced. No old proof argument is hidden in a long parent step: all parent steps are below 2000 characters, and their total is below 3000. The unit/chapter route and all target statements are unchanged.

Small cases: n=1 gives the residue field quotient without using n=0. For C=0 all Hom/evaluation maps are the unique maps on zero objects. For C=B[0], q sends multiplication by a to a by evaluation at 1, and the pairing uses the supplied alpha rather than an arbitrary unit identification. Shifts C=B[-r] check the same Koszul sign on both sides. The two-term complex [A --varpi--> A] checks the nonzero differential for n>1 and the zero differential for n=1. Nonprojective finite cohomology is allowed: no finite A-module is assumed free, and K-flat resolutions need not be bounded. The arbitrary-target Hom task allows V=0 and shifts/unbounded targets; Gamma J remains K-injective by exact-adjunction preservation, not by boundedness. For the signed task an arbitrary alpha can be multiplied by a unit a of A: both beta and its normalized evaluation then multiply by a, so the equality is genuinely normalized, not independent of alpha. Naturality was checked for zero, identity, composable maps and inversion of a quasi-isomorphism. No new false statement, missing hypothesis or statement dispute was found.

## Original returned argument, assigned without deletion

### lem-coef-finite-point-counit-unit-normalization

Original step 1:

Write $A=A_n$, $B=A_s$, $G=A_{s,\mathrm{et}}$ and $\nu=\nu_s$. The absolute value of $E$ extending $|\cdot|_\ell$ is nonarchimedean by the extension-absolute-value theorem, and the valuation-ring theorem makes $R$ a DVR with finite residue field; the finite-quotient theorem, clause (2), then makes $A=R/\varpi^n$ a finite ring. For the identity compactification on the etale point, $R\operatorname{id}_!^{\mathrm{et}}=R\operatorname{id}_*\operatorname{id}_!=\operatorname{id}$ by the compact-support definition. Its right adjoint is canonically the identity: its adjunction bijections are $\operatorname{Hom}(U,V)=\operatorname{Hom}(U,V)$. The finite exceptional-inverse-image definition therefore gives $\omega_{s,n}=\nu^*R\nu_*B$. The constant-ring comparison identifies $B=\nu^*G$. Let $\eta$ and $\epsilon$ be the unit and counit of $\nu^*\dashv R\nu_*$. The bounded-below site-comparison theorem makes $\eta_G$ invertible, since $G$ is in degree zero. The triangle identity $\epsilon_{\nu^*G}\circ\nu^*(\eta_G)=1_{\nu^*G}$ now shows that $\epsilon_B$ is the inverse of $\nu^*(\eta_G)$. Thus the normalization $\alpha:\omega_{s,n}\xrightarrow{\sim}B$ is precisely the counit required in the statement, not an arbitrary unit identification.

Cited statements: lem-weil-l-adic-extension-absolute-value, lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, def-amb-etale-compact-support, def-weil-exceptional-inverse-image, lem-sf-comparison-pullback-exact, thm-weil-pbc-site-comparison.

### lem-coef-finite-point-reconstructed-hom-model

Original step 2:

Put $L(M)=B\otimes_{\underline A}\underline M=\underline M$ for an $A$-module $M$. A short exact sequence of modules gives a sectionwise short exact sequence of constant presheaves. Exact module-presheaf sheafification therefore makes $L$ exact. The sections functor $\Gamma=\Gamma(s,-)$ is exact on all $B$-modules by point-sections exactness. Since $s$ is nonempty, connected, separated and of finite type over $k$, clause (1) of the connected constant-$H^0$ lemma gives $A\xrightarrow{\sim}\Gamma B$, $a\mapsto a\cdot1$. The adjunction used in point reconstruction is exactly $L\dashv\Gamma$: its maps send $h:LM\to F$ to $m\mapsto h_s(1\otimes m)$ and send $t:M\to\Gamma F$ to $b\otimes m\mapsto b\,t(m)|_U$. Thus all the exactness and constant-value hypotheses of that reconstruction statement hold. Its natural counit $e_C:Lc\to C$, where $c=\Gamma C$, is an isomorphism, since $C$ is bounded constructible. The fibre definition places $c$ in the bounded finite-cohomology module category. Denote the derived adjunction unit by $u_c:c\to\Gamma Lc$; its triangle identity is $\Gamma(e_C)u_c=1_c$.

Cited statements: lem-weil-pbc-site-r-module-presheaf-sheafification-exact, lem-weil-point-proetale-sections-exact, lem-pod-connected-constant-h0, lem-pod-point-sections-reconstruction, def-weil-finite-coefficient-point.
Original step 3:

Choose a K-flat flat-term module complex $P$ representing $c$, by the K-flat-resolution lemma on the one-object ringed site, and a K-injective resolution $B\to I$ as in the definition of derived internal Hom. Apply the finite case $(R,B)=(A,A_s)$ of the point-derived-Hom-evaluation lemma, whose hypotheses were verified in Step 2. It gives a K-injective module resolution $A\to\Gamma I$ and the natural isomorphism of complexes
$$q_{P,I}:\Gamma\mathcal Hom_B^\bullet(LP,I)\xrightarrow{\sim}\operatorname{Hom}_A^\bullet(P,\Gamma I),\qquad h\mapsto(x\mapsto h(1\otimes x)).$$
Both sides use the same Hom differential $dh=d_Ih-(-1)^{\deg h}hd_P$. Consequently it induces an isomorphism $q_c:\Gamma R\mathcal Hom_B(Lc,B)\xrightarrow{\sim}R\operatorname{Hom}_A(c,A)$. Composing the target change by $\alpha$ of Step 1, precomposition with $e_C$ of Step 2, and $q_c$, gives an isomorphism
$$\beta_C:\Gamma R\mathcal Hom_B(C,\omega_{s,n})\longrightarrow R\operatorname{Hom}_A(c,A).$$
Here $\operatorname{Fib}_s$ on the internal-Hom object is the ambient termwise-sections functor of the point-exactness lemma; no assumption that the pro-etale topos itself is the category of sets is used.

Cited statements: lem-pc-kflat-resolution, def-pur-derived-internal-hom, lem-pod-point-derived-hom-evaluation, lem-weil-point-proetale-sections-exact.

### lem-coef-finite-point-reconstructed-evaluation-square

Original step 4:

Identify the map, retaining $\alpha$ as the specified normalization. First, the point-fibre tensor comparison applies to the pair $(R\mathcal Hom_B(C,\omega_{s,n}),C)$: the constant sheaf $B$ is constructible on the single stratum $s$ with finite stalk $A$ and has Tor amplitude $[0,0]$, since $B\otimes^L_AM=M$; so the finite-coefficient internal-Hom corollary, applied on $s_{\mathrm{proet}}$ to the separated finite-type $k$-scheme $s$ with $d=0$, puts $R\mathcal Hom_B(C,B)$ in $D^b_{ctf}(s,A)$, and $\alpha$ of Step 1 transports this to $R\mathcal Hom_B(C,\omega_{s,n})$. The point-derived-Hom-evaluation lemma says that $q_c$ carries sheaf evaluation to module evaluation under the canonical sections-tensor balancing map. For the convention with factors ordered $P\otimes\operatorname{Hom}$, both maps on $x\in P^i$ and homogeneous $h$ of degree $j$ give $(-1)^{ij}h(1\otimes x)$; symmetry gives the corresponding equality with Hom first as in the statement. Precomposition with $e_C$ evaluates this formula on $\Gamma(e_C)u_c(x)$, which is $x$ by Step 2. Thus after the point-fibre tensor and unit comparisons, evaluation composed with $\beta_C\otimes1_c$ is exactly the fibre of sheaf evaluation followed by $\Gamma\alpha$. Those tensor and unit comparisons are the ones of the point-fibre-derived-tensor lemma: at finite level they are the canonical balancing maps just used. By uniqueness of the tensor-Hom transpose this identifies $\beta_C=\kappa_C$. In particular the actual specified map, rather than merely its source and target objects, is invertible.

Cited statements: lem-pod-point-derived-hom-evaluation, lem-sf-point-fibre-derived-tensor, lem-pod-point-sections-reconstruction, cor-weil-finite-constructible-hom.
Original step 5:

For a morphism $f:C\to C'$, naturality of reconstruction gives $f e_C=e_{C'}L(\Gamma f)$. Precomposition with this equality and naturality of $q$ give
$$R\operatorname{Hom}_A(\Gamma f,A)\,\kappa_{C'}=\kappa_C\,\Gamma\bigl(R\mathcal Hom_B(f,\omega_{s,n})\bigr).$$
The equality is in the derived category: $q$ is the natural comparison of derived functors in the cited evaluation lemma, and $e$ is the natural derived counit in reconstruction, so it applies to derived morphisms, including inverses of quasi-isomorphisms. The normalization $\alpha$ is fixed independently of $C$. This proves the asserted contravariant naturality.

Cited statements: lem-pod-point-sections-reconstruction, lem-pod-point-derived-hom-evaluation.

## Earlier reports preserved verbatim

### Historical Q05 report

# Worker report

1. Files written: `dag/nodes/sec-six-functors/lem-coef-finite-point-internal-hom-evaluation.json` (statement, split, no exact Mathlib match), `citations.json` (20 verbatim step/node quotations), and this report. No new nodes or Mathlib leaves. `searches.jsonl` records the searches actually run; the existing item's older search records were retained. `write_split.py` is sandbox-only scratch work.
2. Attachments: none. I searched the full `WeilConjectures/` checkout by the item's blueprint tag and by point/internal-Hom/fibre notions. `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual`, `WeilConjectures/SixFunctors/Etale/Derived/Point.lean:157`, ends in `sorry` at line 164. Its statement is an etale coefficient-dual object isomorphism, with no specified pro-etale comparison-counit normalization or evaluation equation. It is not a finished attachment for this item.
3. WANTED: none. The cited blueprint and Stacks sources are present.
4. The imported item was statement-only. Its statement is retained verbatim. The short blueprint source says that the identity exceptional functor is the identity, then treats point internal Hom as coefficient Hom by a definition; this omits the finite transported normalization and the actual Hom/evaluation comparison. The split supplies both using existing statements. In particular, it computes the identity adjoint first on the **ordinary etale** category and uses the comparison counit on its etale-origin coefficient unit; it does not infer that the transported exceptional functor is the identity on the whole ambient pro-etale category. It also does not assert that every pro-etale sheaf on the algebraically closed point is constant.
5. Nothing mathematically unfinished in this one-level split. Its cited prerequisites retain their own DAG states and are not re-split here. No Lean was written or compiled; no library/global build was run.

## Searches and reuse

There was no sandbox item or previous split/report to recover. The five searches now in `searches.jsonl` comprise two LeanFinder phrasings, Loogle, grep, and LeanSearch. I read their returned results. LeanFinder and Loogle give light-condensed underived internal-Hom/evaluation formulas, while LeanSearch gives constant-sheaf/global-sections adjunctions. These do not identify the particular derived pro-etale finite-coefficient comparison or its exceptional normalization. The Mathlib grep for right-derived-sections/internal-Hom/coefficient-dual names returned no hits. I recorded actual queries and returned names, retaining the inherited evidence rather than replacing it. The searches completed; no unavailable service was recorded as absence.

Whole-DAG searches by point-fibre, finite-coefficient-point, internal Hom, finite free complexes, and K-injective notions found the existing tools. `tools/blueprint_refs.py search` was run for point/internal-Hom, coefficient-module dual, evaluation-transpose, and Hom-complex sections phrases, as well as a broad point search. The broad search found `lem-pod-point-dualizing-complex` and `lem-sf-point`; neither is cited as the proof, and neither states precisely this item's evaluation-normalized comparison. The crucial reusable node is `lem-pod-point-derived-hom-evaluation`, which handles a general coefficient-module input and both finite/integral rings under explicit exactness hypotheses. `lem-pod-point-sections-reconstruction` supplies the actual counit on constructible inputs. No node was created for a specialization of either.

The blueprint ancestor command returned `prop-coef-integral-dualizing`. I read its proof in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`: its second paragraph requires precisely the finite-level mapping-complex adjunction transported through the point identification. I also read the unit `sk-prop-sf-biduality-general` and the six-functors chapter record. This is coefficient-point algebra below that route, not a substitute for its geometric stratification argument. The inherited specific `blueprint.from.place` was preserved and `same_as` remains empty after searching.

## Not duplicates

There are no new-node/existing-node pairs. `lem-pod-point-derived-hom-evaluation` is reused as a conditional Hom-complex/evaluation computation; this item verifies its exactness and coefficient-section hypotheses, reconstructs the sheaf input, and fixes the exceptional normalization. `lem-pod-point-dualizing-complex` gives the broader coefficient-stage object comparison but not the complete specified evaluation-transpose assertion. `lem-pod-point-scalar-hom-evaluation` instead concerns integral scalar extension and its quotient-normalized square. None is recreated.

## Review by Q05

I checked the item against the opening paragraph of `lem-pod-point-dualizing-complex.proof.md` in main-20261015, and the second paragraph of the ancestor proof just named. I read every cited node's statement, not merely its proof or name. For the generic construction I also read Stacks `sites-cohomology.tex`, section 08J7 (`section-internal-hom`), where the K-injective-target Hom-complex formula is defined, and `derived.tex`, Tag 08BJ (`lemma-adjoint-preserve-K-injectives`), explaining why an exact left adjoint makes the right adjoint preserve K-injectives. For exact constant realization I read `sites-modules.tex`, Tag 03EI (`lemma-sheafification-exact`). No new node needs an additional source. No prohibited SGA source is used.

Step 1 first uses `lem-weil-l-adic-extension-integers-dvr` (DVR and finite residue field) and `lem-weil-valued-dvr-finite-quotients` (clause (2): the quotient is finite). This explicitly verifies the finite-ring hypothesis of site comparison for every n>=1; it was made explicit during the final hypothesis audit after the first successful dry run. It then uses `def-amb-etale-compact-support` for the formula at the identity compactification and `def-weil-exceptional-inverse-image` for the finite composite `nu^* f^times Rnu_*`. These are actual formulas in the two statements. `lem-sf-comparison-pullback-exact` states the constant-ring identification, not just exactness. `thm-weil-pbc-site-comparison` states invertibility of the bounded-below adjunction unit. The coefficient unit is in degree zero and is thus bounded below. The rest is the written triangle-identity argument: the inverse of the counit on `nu^*G` is `nu^*(eta_G)`. I checked the direction of each arrow; no ambient pro-etale right adjoint to its identity compact-support formula is assumed.

Step 2 uses the **exact module-presheaf sheafification** statement, which includes sectionwise exactness of presheaves, to prove exactness of the constant-module functor in a few lines. The coefficient ring sheaf is constant at finite level, so `B tensor_underlinedA underlinedM = underlinedM` by the tensor unit. `lem-weil-point-proetale-sections-exact` supplies exactness on all module sheaves. Clause (1) of `lem-pod-connected-constant-h0` supplies precisely the constant-value map `A -> Gamma B` as an isomorphism, rather than some unnormalized identification: the point is nonempty and connected and its structure map to Spec k is the identity, hence separated and of finite type. Only that H0 clause is used, not finiteness of higher cohomology or any trace/duality theorem. With those hypotheses verified, the statement of `lem-pod-point-sections-reconstruction` really gives the natural **actual** counit `L Gamma C -> C`; the fibre definition gives bounded finite module cohomology. The adjunction formulas and triangle identity are written explicitly.

Step 3 uses `lem-pc-kflat-resolution` on the one-object ringed site, so it produces a module K-flat representative with flat terms, exactly as required by `lem-pod-point-derived-hom-evaluation`. The K-injective target and its use in internal Hom are in `def-pur-derived-internal-hom`. The existing evaluation lemma says that sections of that target are K-injective, gives the displayed chain isomorphism and differential convention, and asserts the derived isomorphism. Thus this step does not silently infer derived Hom from an underived adjunction. Precomposition with the reconstructed counit has the correct contravariant direction. Exact sections is defined on the ambient derived category, so evaluating the internal-Hom object here does not require a false equivalence of the entire pro-etale topos with sets, nor an unstated boundedness assertion about that ambient functor.

Step 4 uses the evaluation clause and signed formula of `lem-pod-point-derived-hom-evaluation`, together with the monoidal/unit comparisons of `lem-sf-point-fibre-derived-tensor`. The former specifies the canonical sections-tensor balancing map; the latter is the same finite-stage balancing constraint in the item's point-fibre notation. The pairing can be computed with ambient sections on the K-flat/K-injective models before restriction to the finite-Tor categories. The equation `Gamma(e_C) u_c = 1` explains why replacing C by Lc changes neither input of evaluation. The common sign for the order `P tensor Hom` is `(-1)^(ij)`; symmetry handles the Hom-first order of the item. Uniqueness of the tensor-Hom transpose then proves that the constructed isomorphism is the stipulated kappa, not just an unnamed object isomorphism. This is a short calculation from the cited statements, marked elementary.

Step 5 uses the actual derived naturalities in reconstruction and Hom-evaluation. I checked the square's orientation for contravariant Hom: both routes start at the dual of C' and end at the coefficient dual of Gamma C. The written equation follows from `f e_C = e_C' L(Gamma f)`. These are natural derived functors, so naturality includes inverses of quasi-isomorphisms; it is not asserted only for chosen chain maps. This step too is elementary from the stated naturalities.

Against delivery-errors B--E: no new statement-only node is needed (B1--B3), TeX is encoded once, all non-elementary inputs are cited statements (C1), and each of the 20 step citations has an actual verbatim quotation in citations.json (C4). The item is proved by combining two independent generic constructions after verifying their hypotheses, with no new node restating its conclusion (D1--D2). I checked the transitive dependencies of the principal reconstruction/evaluation tools for a return to this item; there is none. I did not change another node, unit binding, source field or maintainer field. Cross-unit statement tools are declared in `split_report.tool_uses` with their particular use. Every step is under 2,000 characters.

Small-case checks: C=0 makes the comparison the unique map between zero objects. C=A[0] gives the identity after the **specified** counit normalization, since q evaluates a scalar endomorphism at 1. Finite direct sums give the same matrix entries. For C=A[-r], the written signed formula has the identical sign in the sheaf and coefficient evaluations. A two-term complex `[A --varpi--> A]` uses the same Hom differential on both sides, so the map respects its nonzero differential for n>1; n=1 also works when this differential is zero. At no point is a nonprojective finite A-module assumed free, nor is finite Tor amplitude of an arbitrary cohomology module inferred from that of C. Indeed the exact-adjunction calculation works for bounded constructible C without using that stronger hypothesis. No statement dispute or source correction is needed; the omitted computation, rather than the item's statement, was repaired.


### Historical NN report

## Worker report

Item: lem-coef-finite-point-internal-hom-evaluation. The module
`Sheaf.Paper.FinitePointInternalHomEvaluation` states
`WeilConjectures.finitePointInternalHomEvaluation`, with `sorry` as its whole proof.
Its six helper definitions have actual data. No node statement or dependency list
is changed, and there are no new or repaired dependency nodes.

The source read is the opening paragraph of main-20261015's
`sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`.
The node's five proof steps are reproduced in the theorem docstring, including
the finite quotient, exact reconstruction, K-flat/K-injective Hom calculation,
finite-Tor closure, signed evaluation and derived naturality steps.

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Global finite-field datum and algebraic closure k | `D : FiniteFieldDatum.{u}`, with the site of `Spec (.of D.k)` |
| Prime ell distinct from p | `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| Valuation ring, uniformizer, positive quotient level | The dependency's `Padic.coefficientExtensionRing l E (n + 1)` uses exactly its valuation ring and chosen uniformizer; `n : ℕ` runs over all positive exponents by this successor indexing |
| C in bounded constructible finite-Tor complexes | `finiteTorConstructibleCategory l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))` |
| c = Fib_s C | `finitePointFibreTensorSource D l E n`, the existing finite-Tor inclusion followed by `pointFiniteSections ... .mapDerivedCategory` |
| The coefficient sheaf B = (A_n)_s | `finitePointCoefficientUnit`, the unit of the existing intrinsic derived tensor, i.e. the coefficient sheaf in degree zero |
| Identity-point dualizing object | `finitePointComparisonOmega` is exactly the identity-adjoint formula `nu^* Rnu_* B`, conjugated through `sfIntrinsicDerivedEquivalence` |
| Normalization is the comparison counit | `finitePointComparisonNormalization` maps `(derivedComparisonAdjunction ...).counit.app ...` through intrinsic realization, followed by realization's own counit isomorphism |
| This normalization is invertible | The first conjunct is `IsIso (finitePointComparisonNormalization D l E n)` |
| Derived sheaf internal Hom into omega | `finitePointSheafDual` uses `finiteIntrinsicDerivedInternalHom`, whose definition is the recorded `derivedInternalHomOfUniverses` on the actual small pro-etale site |
| Point tensor and unit comparisons | `pointFiniteTensorComparison ... S` and `S.unitIso`, constrained by `PointFiniteSourceConstraints` and `PointFiniteTensorCanonical` |
| Canonical evaluation-transpose map | `finitePointDualPairing` is inverse tensor comparison, sections of sheaf evaluation followed by normalization, then unit comparison. `finitePointInternalHomKappa` curries this pairing after the recorded Koszul braiding |
| Target RHom_A(c,A) | Mathlib/upstream `(ihom c).obj (𝟙_ _)`, over the same lifted coefficient ring used by the recorded fibre |
| Kappa is an isomorphism | `∀ C, IsIso (finitePointInternalHomKappa ... C (h C))` |
| Natural in C | The second final conjunct quantifies every `f : C ⟶ C'` and equates sections of contravariant sheaf Hom followed by kappa with kappa followed by `MonoidalClosed.pre` of the fibre map |
| Characterized by evaluation | The last conjunct is `(kappa ▷ c) ≫ DerivedCategory.perfectTraceEvaluation c = finitePointDualPairing ...` |

The tensor comparison is an existential witness with the already recorded
canonical normalization predicate, rather than an extra hypothesis of the
lemma or a new monoidal structure selected from mere existence. The map kappa
itself is a concrete composite and transpose. Its source's finite-Tor membership
witness `h` is supplied in the conclusion; it imposes no additional condition on C.
That membership is the proof's application of finite constructible Hom on the
zero-dimensional point. Proof irrelevance removes any dependence on its proof.

For the identity compactification, the node explicitly specifies identity etale
compact support and the identity as its normalized etale right adjoint. Accordingly
omega is written using the node's explicit `nu^* Rnu_* B` formula. This computes
the exceptional-inverse-image dependency in those identity-adjoint coordinates;
it does not assume that pro-etale sheaves are just sets, replace omega by B, or
select an arbitrary isomorphism with B. The realization equivalence and its
counit are the recorded coefficient presentation transport.

The fibre lives in modules over `ULift.{u + 1, u} A`, precisely as in
`pointFiniteFibre` and the tensor comparison dependency. The site retains object
universe `u + 1` and morphism universe `u`; no equality between these is imposed.
The Hom-first evaluation is the existing `perfectTraceEvaluation`, which uses
the same Koszul braiding and coefficient closed evaluation for every derived
module object; no perfectness hypothesis is introduced by that definition.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its imported
  `CoefficientExtension`): `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, valuation ring and uniformizer constructions.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`
  and `finiteTorConstructibleCategory`.
- `Sheaf.Paper.FiniteCoefficientPoint`: finite clause `pointFiniteFibre` and
  the exact ambient functor `pointFiniteSections` from `PointSectionsFiniteness`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`,
  whose literal finite-level formula is Rnu_*, etale right adjoint, nu^*;
  its publicly imported intrinsic interface gives `sfIntrinsicDerivedEquivalence`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteIntrinsicClosed`,
  `finiteIntrinsicDerivedInternalHom`, `finiteIntrinsicEvaluation`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` (through the intrinsic Hom).
- `Sheaf.Paper.PointFibreDerivedTensor`: `pointFibreDerivedTensor`,
  `PointFiniteSourceConstraints`, `PointFiniteTensorCanonical`, and its imported
  `PointFiniteTensorData`, `pointFiniteTensorComparison`, `unitIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `proEtaleSiteComparisonModules`, realized by the same comparison functors;
  the imported fixed-coefficient derived comparison gives
  `AlgebraicGeometry.ProEtale.derivedComparisonAdjunction` and its counit.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit`, used in the normalization proof plan.

Additional proof-only modules are imported without `public`: ExtensionIntegersDvr,
Etale.Derived.LowerShriek, ComparisonPullbackExact, PointProEtaleSectionsExact,
PointSectionsReconstruction, KFlatResolutionIndependentCoefficients,
PointDerivedHomEvaluation and FiniteConstructibleHom. The connected-constant-H0
node currently has no recorded Lean declaration and hence no module to import.
No import cycle was introduced.

Edge cases checked before and after writing:

- `n = 0` here denotes the first positive exponent, A_1, not the zero quotient.
- The zero object and all shifts are allowed; the hypothesis uses the existing
  intrinsic finite-Tor predicate without a selected Tor interval or model.
- C equal to the coefficient unit gives its coefficient-valued dual, with the
  actual comparison counit still present in the evaluation pairing.
- A two-term complex `[A --varpi--> A]` is allowed, so the statement is not
  restricted to cohomology modules that are projective.
- Naturality includes zero maps, identities and arbitrary localized derived
  morphisms, not just maps of chosen complexes.
- The opposite ordering of the two evaluation factors is explicitly handled by
  the canonical Koszul braiding; no sign convention was silently dropped.
- All finite extensions E are quantified, rather than just E = Q_ell or one
  chosen algebraic-closure subfield. Both the prime condition and ell != p remain.

Searches for an existing statement (all through the authorized search paths):

- `msearch.py`, LeanSearch: `derived internal Hom point sections evaluation
  comparison coefficient modules`. Eight results: smooth sheaf evaluation,
  presheaf sections evaluation, scheme evaluation and `LightCondensed.ihomPoints`;
  none states the finite pro-etale derived comparison with the specified counit.
- `msearch.py`, LeanFinder: `derived internal Hom on proetale algebraically closed
  point evaluation comparison`. Eight results, all scheme/ringed-space evaluation
  naturality; none matches.
- `msearch.py`, Loogle: `CategoryTheory.ihom, CategoryTheory.DerivedCategory`.
  No result; the latter identifier is unknown to the search service.
- `msearch.py`, grep in CategoryTheory:
  `rightDerivedGlobalSections.*[Ii]hom|[Ii]hom.*rightDerivedGlobalSections|point.*[Ii]nternalHom`.
  Zero hits.
- `rg` over upstream WeilConjectures, project `lean/Sheaf`, the upstream names
  index and Mathlib: the item id and the new declaration names have no matching
  existing declaration. Point/internal-Hom concept searches find generic
  PointDerivedHomEvaluation and coefficient trace/Hom APIs; these are reused,
  and do not already state the node's normalized map assertion.

Validation: the prescribed single-file scompile.py compile and deliver2.py dry
run are run for this module. No library build or direct repository write is used.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

