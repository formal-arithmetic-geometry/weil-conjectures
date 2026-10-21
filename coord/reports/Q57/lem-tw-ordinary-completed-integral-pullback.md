1. Files written

- `dag/nodes/sec-purity-real-sheaves/lem-tw-ordinary-completed-integral-pullback.json`: statement, statement dependencies and Lean metadata unchanged; repaired three-step assembly, 2154 characters.
- `dag/nodes/sec-purity-real-sheaves/lem-tw-ordinary-pullback-stratified-models.json`: retain the self-contained statement-only task approved as sound in the return, status unsplit, no Mathlib match. Its statement and logged searches are unchanged.
- `citations.json`: nine verbatim statement quotations, one for every parent step/node citation.

The unlanded new file `lem-tw-ordinary-pullback-quotient-cone-normalization.json` is removed from the delivery, with its complete returned contents retained as `returned-quotient-cone-normalization.json` outside dag/. It was a duplicate, not another available task. The prior full report is retained as `returned-report.md`; `original-report.md`, `original-item.json`, and `searches.jsonl` are preserved. The appendix below also retains the live seven-step proof verbatim as proof material for the new task and the responsibility audit. No existing repository node is deleted or edited besides the item.

2. Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag and ordinary integral/completed pullback notions found no complete matching project declaration. The recorded Sheaf.Paper.OrdinaryCompletedIntegralPullback theorem WeilConjectures.ordinaryCompletedIntegralPullback at the end of that module is still sorry, as are its supporting comparison existence theorems. These are not attachments. No Lean file or Lean record is changed.

3. WANTED

None. The current blueprint, Bhatt–Scholze paper and Stacks sources are present locally.

4. What was wrong

The return is correct. The removed quotient-cone node restated the existing split theorem lem-pur-integral-ambient-operation-models: that statement already gives theta, the strict quotient-tower associativity maps, actual transition compatibility, augmentation normalization including zero in the shifted product, and compatibility with representative changes. Its remaining assertions about arbitrary non-K-flat complexes were unused, and the counit-normalized uniqueness was formal once the computation counit is invertible. The earlier report's attempted distinction was invalid.

This repair starts from the current live item, whose seven steps agree with original-item.json, and changes only proof, proof_deps and split_report. Comparing the returned sandbox with current live found no other changed fields. The target statement is not disputed and is preserved exactly. This is a substantive correction, not an unchanged re-push.

5. Unfinished work

The one retained new node is intentionally statement-only, with proof=[], proof_deps=[], proof_origin=null. Its proof belongs to a later stage-1 worker. The requested repair is otherwise complete, subject to the checks and delivery below.

## Re-split note: why no second non-duplicate node exists

I use the return's explicit alternative: “Spread old steps 2–3 over at least 2 genuinely new nodes, or explain under the note why no second non-duplicate node exists.” This delivery has ONE new node, not two. I am not claiming the numerical minimum was met. The reason for the exception is mathematical coverage by existing nodes, not lack of time or a proposed route change.

Here is the complete candidate inventory from old steps 2–3, with the existing statements open.

- Inverse-image strata: an immersion factors as closed into open. Pulling back the open and using C tensor_A (A/J) = C/JC constructs the pulled locally closed immersion; disjointness and covering follow by inverse images. On a noetherian space an open is quasi-compact, so locally closed is constructible. This is precisely the elementary argument in old step 2 (which was already marked elementary). Naming it as a new unsplit task would violate the brief's ban on elementary new nodes.
- Cover transport: det-pe-topos-functoriality-inverse-image(1) explicitly says that base change sends coverings to coverings. Its application to X_i -> S_i is one instance, not a new theorem. Part (5) already supplies inverse-image composition.
- Equality of structural ring maps for f j_i = i_i f_i: after each finite projection both maps send a constant residue to that residue. The limit universal property gives equality into B_{X_i}. This is a few-line equality from the coefficient definition, not an independent non-elementary argument.
- Restriction of ordinary pullback to a stratum: lem-sfb-ringed-derived-monoidal-comparisons gives c_{f,g}:P_{gf} ≅ P_f P_g, including comparison of 2-isomorphic ringed maps. Apply it to both factorizations of the same composite; lem-sf-immersion-completed-pullback-comparison supplies exact ordinary immersion restriction. A new node asserting this bare comparison would specialize existing statements, not extract new work.
- Restriction to the covering slice: lem-weil-pbc-ringed-derived-slice-localization states j_U^* Lf^* N ≅ L(f_V)^* j_V^* N. This is exactly the restriction used here. Renaming this formula for the pro-etale cover is a duplicate.
- The finite-projective local-model computation: lem-weil-pbc-strict-perfect-ringed-pullback-model already states flatness and K-flatness, the termwise derived comparison, and the pulled splitting maps with the same ranks for bounded complexes with specified finite-free retracts. A model B_U tensor_R L has such a package by tensoring the chosen finite-projective splittings. On each free generator the reassociation sends the basis vector to itself; restricting by its idempotent gives B_V tensor_R L. This last tensor reassociation is elementary once the existing strict-perfect theorem is applied. Creating a second node for it would repeat that theorem, followed by a one-line specialization.

The retained stratified-model node packages the actual geometric strata, covers, coefficient comparisons and identified models into one useful interface, as the return expressly accepted. Separating it into a bare geometry node and a bare model node would leave respectively an elementary fact and an already existing generic theorem. Separating the restriction and model formulas has the same problem. There is no other argument in old steps 2–3 from which to obtain a second comparable independent task without these violations.

Nor is there unassigned work elsewhere to supply an honest second node: old steps 1 and 4 apply the existing characterization in both directions; old steps 5 and 7 and the normalization part of 6 are precisely the ambient-operation theorem now cited; the remaining part of 6 is the existing reconstruction theorem plus elementary coefficient checks. Thus every old argument has an owner, and none is silently summarized away to justify the smaller count.

## Responsibility map for all seven old steps

Old step 1 is parent step 1's forward application of lem-weil-pbc-integral-stratified-perfect-characterization; the noetherian affine-cover convention is checked there. Old steps 2–3 remain the complete statement of lem-tw-ordinary-pullback-stratified-models, with the specific existing tools listed above available to its worker. Old step 4 is the reverse characterization in parent step 1, including actual membership in the detailed category, uniform reduction bounds, compatible origins and intrinsic completeness.

Old step 5 is supplied by the strict-tower isomorphism in lem-pur-integral-ambient-operation-models, whose balanced associativity maps are exactly h_n, using the same c_f and quotient projections. Parent step 2 cites it, lem-weil-pbc-ringed-topoi-derived-pullback, and def-sf-ordinary-integral-pullback-construction exactly as requested. Old step 6's ring checks and canonical comp invertibility remain explicit in parent step 3, using the DVR, finite-quotient and Koszul reconstruction statements. Its normalization is in parent step 2: theta comp has the prescribed quotient augmentation and zero shifted-product coordinate. Old step 7's representative compatibility is expressly part of the ambient theorem; the derived pullback counit identifies its source with the ordinary representative. These give naturality and resolution independence of the specified map, not just isomorphic endpoints.

## Not duplicates

lem-tw-ordinary-pullback-stratified-models vs lem-weil-pbc-integral-stratified-perfect-characterization: the existing characterization has one scheme and no morphism, pulled stratification, covers or ordinary pullback models; it is applied on Y and X separately by the parent.

lem-tw-ordinary-pullback-stratified-models vs lem-weil-pbc-strict-perfect-ringed-pullback-model: the existing generic theorem computes a given bounded packaged complex under a single ringed-topos pullback. It does not assemble base-changed geometric strata, their pro-etale covers, coefficient composition and slice comparisons for an ambient K. It supplies the final termwise computation of the retained task. This is also why that computation cannot become a second new node.

lem-tw-ordinary-pullback-stratified-models vs lem-weil-pbc-ringed-derived-slice-localization: the existing theorem gives the generic derived slice comparison; it does not state stratified local-model transport.

lem-tw-ordinary-pullback-stratified-models vs lem-sfb-ringed-derived-monoidal-comparisons: the existing theorem gives general derived monoidal/composition comparisons; it does not construct geometric stratifications and their covering models.

lem-tw-ordinary-pullback-stratified-models vs lem-sfb-pullback-constant-model-constructible: the latter concerns underived module objects over pulled-back condensed coefficients and finitely presented module models. The retained task concerns ordinary unbounded derived pullback over the actual inverse-limit coefficient sheaves and bounded complexes of finite-projective R-modules, with normalized immersion/slice comparisons.

lem-tw-ordinary-pullback-stratified-models vs lem-tw-ordinary-completed-integral-pullback: the new node assumes specified local models for an ambient K, computes their pullback and never asserts the completion comparison is invertible. The parent still uses the characterization, intrinsic completion and reconstruction to prove that claim.

The duplicate quotient-cone node has been removed, not defended. Whole-DAG concept searches and blueprint_refs searches for stratified perfect, quotient augmentation, pullback model, pullback composition and locally closed were read; the earlier logged searches and returned report are retained. No new node or new mathematical statement was added in this retry, so the searches for the unchanged retained node were reused after reading their results.

## Mathlib searches

The unchanged new node records the actual msearch.py calls in searches.jsonl: LeanFinder on ordinary stratified perfect derived pullback and on extension of scalars/slice localization; Loogle on SheafOfModules.pullback and Comp; LeanSearch on base change of stratified constant perfect complexes; and grep on pullbackComp|pullbackObjFreeIso. Both LeanFinder phrasings and the other services responded. Their returned signatures do not state this derived geometric theorem. I reread the relevant Mathlib Sheaf/PullbackContinuous.lean and Sheaf/PullbackFree.lean code: these are underived module pullback and free-sheaf basis comparisons. No matching Mathlib leaf or one-line specialization of the full retained statement was found. No query was invented or retrospectively altered, and no compiler was run.

## Review by Q57

I read the repair note, the exact returned objections, the live seven-step item, both returned new-node statements, and the actual existing statements named in the return. I read GOAL.md, the three route levels in SETUP.md, the worker brief, stage-1 rules, delivery-errors B–E, the chapter and sk-r-real-linear unit, and the current main-20261015 dual-negation blueprint ancestor. This is the existing ordinary/completed integral route needed by that ancestor; no unit or chapter route changes and no SGA source is used.

For the item and the retained new node I read Bhatt–Scholze Proposition 6.6.11 with both proof directions and the meaning of locally constant perfect values, Lemma 6.5.9(4),(5), and Remark 6.8.15. The paper supplies the stratified-perfect and ordinary coefficient-functor route. I read the Stacks statements and proofs in sites-cohomology.tex at 06YY, 0G7E, 0D6D and 07A4 for derived pullback, K-flat preservation, composition and tensors. The explicit normalization is an agent formulation and is now sourced through the existing ambient-operation statement, not attributed as verbatim paper text.

In parent step 1 I opened the characterization statement and checked its hypotheses on both schemes: prime ell, finite E, the valuation ring and uniformizer, finite-dimensionality, ell invertible, and a finite affine noetherian cover. Local noetherianity plus quasi-compactness supplies the last convention. Condition (ii) is exactly the local-model hypothesis and conclusion of the retained new node. Its bounded finite-projective representatives compute the derived scalar extension, since every term is a summand of a finite free module. The characterization's final sentence explicitly identifies the detailed integral category in this item, and its condition (i) refers to the definition containing intrinsic completeness, uniform reduction bounds and compatible etale-origin witnesses. Thus the cited statements give all the claimed conclusions on M.

For parent step 2 I checked the whole ambient-operation-models statement, not an argument hidden in its proof. Its f is arbitrary with ell invertible on X and Y, as here. Its A is our R and its completed R_W is our B_W. Both use C_X = R lim Res_n(- tensor^L (R/t^n)_X) and the same strict-tower derived-limit functor as reconstruction. It explicitly gives theta, balanced strict-tower comparisons, quotient augmentation normalization including the zero shifted-product coordinate, and compatibility with every quotient transition and change of K-flat representatives. The ordinary-construction node defines the same c_f and chain map, with n+1 instead of n as a harmless indexing shift. The ringed-derived-pullback statement gives the invertible canonical computation counit on flat-term K-flat complexes and its resolution comparisons. These are exactly the three statements cited in repaired step 2, and together they give eta = theta comp, naturality and resolution independence. The claim of extra work in the deleted node was therefore withdrawn in full.

For parent step 3 I read the DVR statement: it explicitly gives a PID, domain, nonzero uniformizer and finite residue field. The finite-quotient lemma applies with its maximal ideal generated by t and gives finiteness of every quotient. A PID is noetherian because each ideal has one generator; a finite residue group is torsion; and multiplication by t^n is injective in the domain, so [R -> R] is the displayed finite-free resolution of R/t^n. These check every adic coefficient hypothesis in the reconstruction statement. That statement specifically makes canonical comp_M invertible for intrinsically complete M; combined with theta it proves invertibility of this eta.

I rechecked the retained task on empty X/strata and zero models, f=id, a locally closed open/closed pair, finite-free models, finite-projective summands, and the complex [R -> t^n R]. Empty pieces are discarded, the zero complex gives zero, coefficient compositions are the identity when f=id, splitting idempotents pull back with the same relations, and the scalar differential remains multiplication by t^n. No flatness of c_f or completeness of the output is assumed by that task. These checks do not use the false unrestricted assertion that inverse image must preserve all limits.

B–E were checked against the actual files: the sole new node is self-contained and statement-only with definitions cited, every parent non-elementary use is a node statement and has a verbatim quotation in citations.json, and no proof claims are extracted from a node's proof. The item statement, coefficient category, canonical map and hypotheses are unchanged. Every parent step is below 2000 characters, the total is below 3000, and all old work is assigned as above. The only deviation from the numerical re-split note is the explicit no-second-nonduplicate exception that this return authorizes, explained rather than hidden.

## Validation and delivery

The inherited two-node delivery was dry-run first as required; it passed mechanical preflight at ca6a9a05a3d, which did not fix the mathematical duplication identified by the return. The repaired one-node version passed the prescribed server preflight, DAG check and split review: OK (not pushed) at 2e736f6293b. This receipt checks the revised proof/dependencies and one-new-node tree; the explicit numerical exception remains for the maintainer’s independent mathematical review. Only the prescribed delivery command runs server-side DAG/review/preflight checks; no such checker, compiler, Lake tool, git command or agent was run locally. All writes are inside the Q57 sandbox.

## Appendix: original seven-step proof (verbatim live text)

### Original step 1

Apply [lem-weil-pbc-integral-stratified-perfect-characterization] to $K$ on $Y$. Its hypotheses are precisely the given coefficient, noetherianity, dimension and invertibility hypotheses. The noetherian convention agrees: quasi-compactness extracts a finite subcover from the noetherian affine neighbourhoods provided by local noetherianity. The last comparison sentence of that lemma applies to the category in this item, not just to a category with similar notation. Obtain a finite constructible locally closed stratification $Y=\coprod_i S_i$ and pro-etale covers of $S_i$ on which $K|_{S_i}$ is the completed scalar extension of a perfect $R$-complex. Choose bounded finite-projective representatives $L^\bullet$ for these local models.

Uses: lem-weil-pbc-integral-stratified-perfect-characterization

### Original step 2

Put $X_i=X\times_Y S_i$ and discard empty strata. These form a finite stratification of $X$ in [def-constructible-stratification]. Indeed an immersion factors into a closed immersion into an open subscheme: inverse image of that open is open, and on affine charts the closed part $\operatorname{Spec}(A/J)$ pulls back to $\operatorname{Spec}(C/JC)$, since $C\otimes_A(A/J)=C/JC$. Its image is the inverse image of the original stratum, so the images remain disjoint and cover $X$. Each is locally closed, hence constructible on the noetherian space $X$. For the latter assertion, every open in a noetherian space is quasi-compact and a locally closed subset is the intersection of an open with a closed subset, which is the constructible convention here. For each trivializing cover $\{U_a\to S_i\}$, the family $\{X_i\times_{S_i}U_a\to X_i\}$ is a pro-etale cover: this is the covering-preserving base-change assertion of [det-pe-topos-functoriality-inverse-image](1).

Uses: def-constructible-stratification, det-pe-topos-functoriality-inverse-image

### Original step 3

Write $j_i:X_i\hookrightarrow X$, $i_i:S_i\hookrightarrow Y$, and $f_i:X_i\to S_i$. The ringed morphisms for $f j_i=i_i f_i$ agree: after projection to $(R/t^n)_{X_i}$ both structural maps send a constant residue to the same residue, and equality into $B_{X_i}$ is equality after all its limit projections. The composition comparison in [lem-sfb-ringed-derived-monoidal-comparisons] therefore gives
$$j_i^*P_fK\simeq P_{f_i}(i_i^*K).$$
Here ordinary immersion pullback is exact and is the restriction functor, by [lem-sf-immersion-completed-pullback-comparison]; this use is of its ordinary exactness assertion, without presupposing completeness of $P_fK$. Restrict this equality to the covers in step 2. By [lem-weil-pbc-ringed-derived-slice-localization], ordinary derived pullback on each cover is the pullback between the localized ringed sites. On a local model it is
$$B_V\otimes_{f_i^{-1}B_{S_i}}f_i^{-1}(B_{S_i}\otimes_R L^\bullet)\cong B_V\otimes_R L^\bullet.$$
This calculation computes derived pullback: every term of the model is a direct summand of a finite free coefficient module, and its complex is bounded. Under the monoidal unit and composition comparisons of the first cited lemma, a free basis vector goes to the same basis vector; applying the corresponding idempotent gives the same assertion for each projective summand. Thus $P_fK$ has the required perfect local models on every $X_i$.

Uses: lem-sfb-ringed-derived-monoidal-comparisons, lem-sf-immersion-completed-pullback-comparison, lem-weil-pbc-ringed-derived-slice-localization

### Original step 4

Apply [lem-weil-pbc-integral-stratified-perfect-characterization] on $X$ to the perfect models just computed. It gives $M=P_fK\in D^b_c(X,R)$ with the definition of this item, including its uniform reduction bound. It also gives membership in [def-weil-pbc-bounded-constructible-complete], hence intrinsic derived $(t)$-completeness in the precise Koszul-unit sense of that category. This last conclusion, rather than an arbitrary lift into a distinguished triangle, is what will establish invertibility of the specified completion map.

Uses: lem-weil-pbc-integral-stratified-perfect-characterization, def-weil-pbc-bounded-constructible-complete

### Original step 5

Choose the flat-term K-flat resolution $Q\to K$ in the statement, and put $F=f_B^*Q$. By [lem-weil-pbc-ringed-topoi-derived-pullback], $F$ represents $M$; by [lem-weil-pbc-ringed-topos-kflat-pullback], $F$ is itself K-flat with flat terms. Let $D_n=(R/t^n)_X$ and $C_n=(R/t^n)_Y$. The finite constant structure map $f^{-1}C_n\cong D_n$ and exact finite module pullback are those of [prop-weil-pbc-proetale-constant-exact]. The exact monoidal inverse image of [lem-weil-pbc-left-exact-site-inverse-image-tensor] preserves the balanced tensor presentations (relative tensor is a cokernel of the two action maps). Consequently there are actual isomorphisms of complexes
$$h_n:F\otimes_{B_X}D_n\xrightarrow{\sim} f_n^*(Q\otimes_{B_Y}C_n).$$
In local balanced section notation they send $(b\otimes q)\otimes a$ to $1\otimes(q\otimes\pi_n(b)a)$. Both sides identify with $f^{-1}Q\otimes_{f^{-1}B_Y}D_n$; the inverse sends $1\otimes(q\otimes a)$ to $(1\otimes q)\otimes a$. These formulas are balanced and respect differentials. Under $D_{n+1}\to D_n$ both paths send a generator to $1\otimes(q\otimes\pi_n(b)\overline a)$, so $h_\bullet$ is an isomorphism of strict towers with their actual quotient transitions. It carries the quotient arrow $F\to F\otimes_{B_X}D_n$ to exactly the quotient arrow in the statement.

Uses: lem-weil-pbc-ringed-topoi-derived-pullback, lem-weil-pbc-ringed-topos-kflat-pullback, prop-weil-pbc-proetale-constant-exact, lem-weil-pbc-left-exact-site-inverse-image-tensor

### Original step 6

The adic hypotheses for [prop-weil-pbc-koszul-reconstruction] hold with $A=R$, $I=(t)$: [lem-weil-l-adic-extension-integers-dvr] makes $R$ a principal ideal domain, hence noetherian, with $t$ nonzero; [lem-weil-valued-dvr-finite-quotients] gives finite quotients. The residue is torsion since it is finite. For every $n\geq1$, $[R\xrightarrow{t^n}R]$ in degrees $[-1,0]$ is a finite free resolution of $R/t^n$, proving perfectness. Thus the intrinsic completeness of $M$ in step 4 implies that its canonical quotient-tower completion unit is an isomorphism, by [prop-weil-pbc-koszul-reconstruction]. Compute this unit using $F$ from step 5. Exact products and the strict Roos model in [lem-pur-integral-operations-well-defined] identify its target with the cone of $1-s$ on $\prod_n(F\otimes_{B_X}D_n)$. The strict tower isomorphism $h_\bullet$ induces the product map in both cone coordinates. Since it carries each quotient map to the one in the statement, it carries the chain map having quotient maps in the unshifted product and zero in the shifted product to that very specified chain map for $\eta_{f,K}$. Its target is $\widehat P_fK$ by [def-pur-integral-derived-operations]. Hence $\eta_{f,K}$ is an isomorphism. This identifies chain maps of strict cones, not merely their projections in a triangulated category.

Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, prop-weil-pbc-koszul-reconstruction, lem-pur-integral-operations-well-defined, def-pur-integral-derived-operations

### Original step 7

For a chain map $v:Q\to Q'$ between flat-term K-flat complexes, the equality
$$(f_n^*(v\otimes1))\,a_{n,Q}=a_{n,Q'}\,f_B^*(v)$$
holds on a generator $b\otimes q$: both expressions are $1\otimes(v(q)\otimes\pi_n(b))$. Taking products and placing zero in the other cone coordinate gives a strictly commuting square of the displayed comparison maps. [lem-weil-pbc-ringed-topoi-derived-pullback] and [lem-pur-integral-operations-well-defined] assert that both representative constructions invert quasi-isomorphisms in this resolving class and give their canonical comparison isomorphisms on the derived category. The square therefore descends after localization, and also commutes with inverses of those quasi-isomorphisms. It proves naturality in $K$ and independence of $Q$ under the canonical comparisons for any two resolutions. All maps of schemes used above were arbitrary; no separatedness or base-field linearity was used.

Uses: lem-weil-pbc-ringed-topoi-derived-pullback, lem-pur-integral-operations-well-defined
