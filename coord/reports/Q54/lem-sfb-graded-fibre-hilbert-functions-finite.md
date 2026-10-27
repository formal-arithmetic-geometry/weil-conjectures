# Stage-1 repair and released re-split

1. Files written:
   - lem-sfb-graded-fibre-hilbert-functions-finite.json: unchanged statement and statement dependencies; short assembly of three independent arguments, status split.
   - lem-sfb-graded-affine-monomial-models.json: statement, unsplit; no Mathlib match.
   - lem-sfb-graded-quotient-generic-ranks.json: statement, unsplit; no Mathlib match.
   - lem-sfb-noetherian-generically-constant-finite-image.json: statement, unsplit; no Mathlib match.
   - report.md and citations.json: signed review and verbatim quotes for every assembly citation.
2. Attachments: none. No matching item declaration was found under lean/WeilConjectures by the item tag, declaration names and Hilbert-function concept. The already landed Sheaf theorem is sorry at line 117, so it is not an attachment.
3. WANTED: none. All sources used below are in the read clone.
4. The previous attempt mistook a stage-2 declaration for finished stage-1 work and attempted a lean-only rebind. The retained retries repaired that binding but overlooked the released stage-1 repair note, treating the old passing stage-1 review as conclusive. The live repair note is dated 2026-10-22 and expressly overrides live-wins under coord/brief-stage1.md §1. It requires at least two independent new nodes and an assembly of at most 3000 characters. This delivery implements that order, retaining Q60's argument and Q47's owning lean record exactly. No statement correction, route change, or Lean edit.
5. Nothing remains unfinished in this stage-1 split. The three new lemmas deliberately have statements only and join the queue for separate workers.

## Current landing-refusal repair — 2026-10-23

The supplied return names head ad9d4c0f5ec and asks for the side completion to be rebased onto the current DAG. I continued the retained repair, including its three new statements, original arguments, citations and actual logged searches. Before editing, the required resumed dry run fetched the current server branch and passed at 7c231a70713; that was a dry run, not a delivery. The current read clone still has the seven-step Q60 proof, the released stage-1 re-split order and none of the three new ids. A field comparison shows that the retained item changes only proof, proof_deps, proof_origin and split_report. Its statement, statement dependencies and all maintainer-owned metadata agree with current. The delivery tool performs the rebase in its own temporary worktree; no git command or repository write was made by this worker.

For this retry I revised assembly step 2: the images of finitely many generators of each M_d span its residue-field tensor product. This proves its dimension is a natural number before defining the entire function as a value in N^N. It supplies the elementary type justification rather than silently using the finite-module hypothesis. I also checked explicitly that C_0=A, finite type of C, finiteness of M over C and finiteness of each M_d all come from step 1. This revised proof and signed review make the retry concrete, beyond a rebase or unchanged push.

I reread every current assembly citation: the affine-model statement supplies actual section generators and stalk fibres; pqf-lem-coherent-ft-locnoeth supplies coherence from exactly quasi-coherence and finite type; the quotient-generic-ranks statement supplies one open for all degrees and explicit scalar comparisons; and the abstract finite-image statement applies to arbitrary set-valued functions, with no continuity assumption. All four citations.json quotes remain verbatim, with one entry for every step/node pair. I also reread all statement dependencies of the four delivery files. No cited statement needs replacement. The entire original seven-step argument remains allocated below, not shortened away.

Source checks repeated in this retry: algebra.tex lemma-graded-module-fg (00K0), lemma-generic-flatness-Noetherian (051R), lemma-finite-projective (00NX), coherent.tex lemma-coherent-Noetherian (01XZ), schemes.tex lemma-spec-sheaves (01HV) and lemma-quasi-coherent-affine (01IB), and more-morphisms.tex lemma-generic-flatness-stratification (0ASY). The latter motivates the Noetherian-induction pattern; it is not claimed to literally state the abstract finite-image lemma. Generic freeness is applied to the whole module and permits infinite free rank; the finite-support retract argument in the retained proof then handles every finite homogeneous summand. Empty schemes, zero modules, nonreduced bases and the jumping family (k[t]/t)[x] satisfy the statements as described in the signed review below.

The existing Mathlib search records were read and retained, not rerun or invented. Each new-node query agrees with searches.jsonl. I read the recorded candidate signatures for homogeneous generators, locally constant module rank and finite image of a globally locally constant map; none gives the corresponding new statement in one specialization. The unchanged item retains its earlier inherited searches. The project Hilbert-function declarations in WeilConjectures/AlgebraicGeometry/Modules/Ample.lean concern Euler characteristics on proper schemes, not this graded-fibre family. The matching Sheaf declaration still ends in sorry, so it is not an attachment. No Lean was written or compiled.

## Landing-refusal repair — 2026-10-22

The latest return is L's promotion/landing refusal, not a mathematical rejection: the earlier completion existed in a side DAG but not the live DAG used by the queue. The retained receipt and initial resumed dry run both name 5e4fe6d7c1b. I compared all four retained node files with the current read-clone DAG. The current item still contains Q60's seven-step proof and review; none of the three new node ids exists there. The item differs only in proof, proof_deps, proof_origin and split_report. Its statement, stmt_deps, sources, blueprint ancestry, chapter/unit and existing Lean metadata agree with current. The released 2026-10-22 stage-1 repair note still requires this redistribution despite that old passing review.

I reread every direct assembly citation and every existing statement dependency of the four files against the current DAG. The external assembly citation pqf-lem-coherent-ft-locnoeth still agrees verbatim with citations.json. The other three citations are the retained new statements, whose quotes also agree verbatim. The current graded-sheaf structure and generation definitions still distinguish arbitrary nonnegative generator degrees from degree-zero generation; the affine-model hypothesis uses the former. The Noetherian, finite-type-algebra, finite-module, localization, projective-module, spectrum, residue-field and module-stalk definitions still supply exactly the notions used by the new statements. No dependency needs replacement and no statement correction is needed.

This retry changes the generic-rank assembly step to exhibit all hypotheses before applying its node: A Noetherian, C_0=A, C finite type, M finite over C, and each M_d finite over A. All come from the affine-model conclusion, including C_0=A from B_0=O_S on that chart. The conclusion is the whole function on V(I) intersect D(b), through the node's explicit quotient/localization fibre isomorphisms. This is an actual revised split and current review, not an unchanged re-push. The original three new statements, logged Mathlib searches, report, citations and complete seven-step argument allocation are retained. deliver.py fetches the current origin/sheaf-dag and overlays only the permitted split fields, preserving the maintainer's current metadata; it is the authorized rebase/delivery operation.

## Review by Q54

This retry addresses the promotion/landing return above. I checked the current source passages for every retained argument: algebra.tex 00K0 (homogeneous monomials), schemes.tex 01HV/01IB (actual sections and stalks), algebra.tex 051R (generic freeness of the entire finite module, without a finite-rank assertion) and 00NX clauses (3) and (8) (finite-free retracts and locally constant fibre rank), and more-morphisms.tex 0ASY (the Noetherian-induction pattern). I also reread the six current supporting theorem statements retained in the report: affine free evaluation, actual germ localization, maximal submodules, finite minimal primes, generic freeness and finite-projective rank. They still give exactly the inputs assigned to the three new nodes. The prime-quotient step needs a single localization for all degrees; the finite-support retraction argument handles an infinite free ambient module. The abstract function lemma assumes generic constancy on every prime closed subset and requires no continuity. The four assembly steps use only the four quoted statements, followed by a finite union. Empty schemes, zero modules, positive generator degrees, nonreduced bases and the jumping family (A/t)[x] remain covered. No long assembly step hides an additional argument.

I read the returned A2/A7/H1/H2 entry in full. The stage-2 rebinding has been undone: the item's complete lean record is identical to live, including existing:false, Q47, the module-owning file and both declarations. No Lean or dependency module is delivered. The return's “No fixes” concerns its superseded lean-only attempt; the newer released stage-1 repair record explicitly orders redistribution of the live proof. I followed that order rather than resubmitting an unchanged node. The previous report and its searches are retained below as historical evidence, including its now-resolved mistaken conflict diagnosis.

For the item and affine-model node I read algebra.tex Tag 00K0, lemma-graded-module-fg, including the homogeneous monomial proof at lines 13873 onward; coherent.tex Tag 01XZ, lemma-coherent-Noetherian at 2225 onward; schemes.tex Tags 01HV/01IB as used by the already read affine evaluation and module-germ nodes. The new affine-model statement requires quasi-coherence in each degree, coherence of degree one, generation of the algebra in degree one with degree zero equal to the structure sheaf, and finite homogeneous local generation in arbitrary degrees. It asserts the finite affine model and the actual finite monomial generating lists, not coherence or finite H. Those are different conclusions from the item. Taking homogeneous components gives the monomials with total degree d-b_j. Refining to affines and using identity-morphism free evaluation supplies section surjectivity; sheaf epimorphisms alone on arbitrary opens would not suffice. The module-germ node supplies localization of the actual sections, and the fibre map is m/u tensor z -> m tensor u^{-1}z, inverse m tensor z -> m/1 tensor z. No separatedness hypothesis or affine-intersection assertion is used.

For the generic-ranks node I read algebra.tex Tag 051R, lemma-generic-flatness-Noetherian at 28458 onward, and Tag 00NX, lemma-finite-projective at 19027 onward, especially direct-summand and fibre-rank clauses. Its hypotheses give, after every prime quotient, a Noetherian domain R, finite-type D and finite D-module N. Tensor/direct-sum compatibility is componentwise with finite supports; the original proof's maps are retained verbatim below. Generic freeness applies to the WHOLE N, not to finitely many selected degrees, and supplies one a. Each localized component is finite and is a graded direct summand of N_a. If N_a has basis T, the finitely many generators of a component use a finite T_d; its inclusion into R_a^{T_d} and the restricted degree projection form a retraction. Thus each component is finite projective. By the existing finite-projective-rank statement its local rank is locally constant, hence constant on Spec of the domain R_a (every nonempty basic open contains its zero prime). A basis at a stalk tensors to a residue-field basis, so the stated fibre dimension equals that rank. This is one function simultaneously in all degrees. The source does not claim finite rank for N_a; neither does the new node. Quotient and localization fibre comparisons are included explicitly in its conclusion, so step 2 does not take them from a definition or from a proof it cannot cite.

For the generic-constant finite-image node I read more-morphisms.tex Tag 0ASY, lemma-generic-flatness-stratification at 15566 onward, including its actual Noetherian-induction proof, and the statements of the existing 00IK maximal-submodule and 00FR minimal-prime nodes. This is an abstract adaptation of that induction, not a claim that 0ASY literally states this set-valued assertion. For each ideal J let P(J) say f(V(J)) is finite. A maximal bad ideal exists by ACC for the finite module A. It is proper; if nonprime, every inverse image of a minimal prime of A/J strictly contains it, and those finitely many closed sets cover V(J). Maximality would make its image finite. Thus a maximal bad ideal I is prime. The hypothesis gives b outside I and one value on V(I) intersect D(b); its complement is V(I+(b)), where I+(b) strictly contains I. Adding that one value to its finite image contradicts badness. This carries the former steps 3 and 6 without assuming any topology or continuity on the target T.

Assembly citation check, with every cited node's complete statement open:
- Step 1 cites graded-affine-monomial-models for the finite cover, finite algebra/module generators, finite modules in each degree and actual stalk-fibre comparison. Each is a literal clause. It separately cites pqf-lem-coherent-ft-locnoeth, whose statement is coherence iff quasi-coherence and finite type on a locally Noetherian scheme. These hypotheses are exactly available.
- Step 2 cites graded-quotient-generic-ranks. A is Noetherian; C is finite type and M finite over C, and every M_d finite over A by step 1. The lemma explicitly gives the same function on the principal open after every prime quotient, with the fibre identification. Lifting a to b outside I uses only the definition of A/I.
- Step 3 cites noetherian-generically-constant-finite-image, whose hypothesis is exactly that each prime closed subset has such a principal open with one value. Apply it to the entire functions as values in T=N^N. This avoids the invalid inference from separately finite values in every degree.
- Step 4 is elementary: finite union over the finite affine cover, with pointwise identification already obtained in step 1. No theorem about gluing flatness or constructibility is invoked.
citations.json copies each whole cited statement verbatim; it contains four step/node entries. The only off-unit theorem still used directly is the same coherence tool already declared by Q60; its declaration is retained in split_report.tool_uses.

The repair is by one level: new nodes have proof=[], proof_deps=[], proof_origin=null, status unsplit, complete independent hypotheses, real sources with labels/tags and no proof sketch inside their statements. Algebraic graded structures in the second node are defined inline by the direct sums and homogeneous multiplication/action rules. The first uses the existing graded-sheaf and arbitrary-degree generation definitions. No new definition is introduced. Every new node inherits the item's chapter/unit and exact blueprint ancestry, with the item prepended to via; ancestor reports None exactly as for the live item. Whole-blueprint searches for graded, monomial, Hilbert function, generic freeness, generic constant, finite image and 0ASY found no equivalent imported node. DAG searches by tags and graded/affine, generic/rank and Noetherian/finite-image concepts found the supporting statements below, not the new conclusions. The Lean source contains no matching finished declaration.

The required msearch.py searches were run and their actual hits read: each new node records two distinct leanfinder phrasings, a leansearch query, loogle and grep. All services answered. GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous (Mathlib/RingTheory/GradedAlgebra/FiniteType.lean:30) only supplies homogeneous ring generators; it does not give the sheaf chart or fibre comparison. Module.isLocallyConstant_rankAtStalk (Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean:224) concerns one already finitely presented flat module, not one localization controlling infinitely many graded pieces. IsLocallyConstant.range_finite (Mathlib/Topology/LocallyConstant/Basic.lean:154) assumes global local constancy; our function can jump on a proper closed subset. Their source signatures were read. No hit is an exact match or one-line specialization; there are zero Mathlib leaves. Previous searches for the unchanged item are retained without pretending they were rerun.

Small cases: empty scheme permits empty affine cover and H empty; zero module and empty e-list give zero functions; e_j with b_j>d contributes no monomial. If B_1=0 then positive algebra degrees are zero, and generators in positive degrees remain allowed. Over A=k[t], C=A[x], M=(A/t)[x], the function is constant one at (t) and zero off V(t): a=t makes N_a=0 over the domain, while quotient I=(t) gives rank one in every degree. Hence the generic statement does not wrongly assert global constancy or finite total rank. Nonreduced bases such as k[epsilon]/epsilon^2 are handled by prime quotients within the induction. For the abstract node, T may be empty only when the spectrum is empty; on the zero ring V(J) is empty and its image is finite. Over a product of two fields, the component values may differ and the induction still gives a finite image. No field characteristic or reducedness condition is added.

I checked delivery-errors B--E: none of the new nodes restates a whole item clause (affine structural model, generic ranks for each prime quotient, and a general arbitrary-set induction criterion are distinct arguments); none is two lines from the item's cited statements. The generic lemma combines generic freeness, finite-support projective retractions, local rank constancy and explicit scalar comparisons. The abstract induction needs ACC and finite minimal primes. The affine lemma must pass from local sheaf generators to actual affine sections and fibres. Every argument formerly carried by steps 1--6 is assigned to one of these nodes and retained verbatim below for its next worker. Former step 7 is the elementary final union. The revised assembly is 1655 characters, no step near 2000. This repairs every numbered fault while obeying the released re-split; no gate or launcher was modified.

## Not duplicates

lem-sfb-graded-affine-monomial-models vs lem-sbc-affine-section-associated-stalk: the existing statement concerns “Unequal affine module sections are detected at an associated stalk” (Let L be a locally Noetherian scheme [def-weil-pbc-scheme-conventions, def-weil-pbc-noetherian-ring], N a quasi-coherent module [pqf-def-coherent], and V an affine open such that N(V) is finite over O_L(V). For…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sbc-affine-module-germ-localization: the existing statement concerns “Quasi-coherent affine module germs are localization maps” (Let L be a scheme [def-weil-pbc-scheme-conventions], N a quasi-coherent O_L-module [pqf-def-coherent], V an affine open, and y a point of V. Put R=O_L(V), p=hV.primeIdealOf(y), and regard N_y [def-weil-pbc-modu…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sbc-affine-restriction-source-depth: the existing statement concerns “Affine localization comparison for the injective restriction source” (Let $L$ be a locally Noetherian scheme [def-weil-pbc-scheme-conventions, def-weil-pbc-noetherian-ring], $U$ an open subscheme, $N$ a quasi-coherent module [pqf-def-coherent], and $V$ an affine open. Write $R=\m…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-affine-double-dual-stalk: the existing statement concerns “Stalk comparison for the actual affine double dual” (theorem affine_double_dual_stalk (A : CommRingCat.{u}) [IsNoetherianRing A] (M : ModuleCat.{u} A) [Module.Finite A M] (x : Spec A) : ∃ hfinite : Module.Finite ((Spec A).presheaf.stalk x) (TopCat.Presheaf.stalk …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-trf-affine-chart-stalk-differentials: the existing statement concerns “Affine chart comparison for stalk maps and relative differentials” (Let $f:X\to S$ be a morphism of schemes [def-pc-scheme] locally of finite presentation [def-sbc-locally-finite-presentation], $x\in X$, and $s=f(x)$. There exist affine open neighbourhoods $W=\operatorname{Spec…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-q1-exterior-sheaf-affine-unit-bijective: the existing statement concerns “The exterior sheafification unit is bijective on affine quasi-coherent sections” (Let $X$ be a scheme [def-pc-scheme], $F$ a quasi-coherent $\mathcal O_X$-module [pqf-def-coherent], $U$ an affine open of $X$ [def-weil-affine-spectrum], and $n\geq0$. Let $P_n(W)=\bigwedge^n_{\mathcal O_X(W)}F…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-koszul-hom-coordinates: the existing statement concerns “Homology of the affine Koszul Hom model” (Let $Y$ be a scheme [def-pc-scheme], $U$ an affine open, $A=\Gamma(Y,U)$, $n\in\mathbf N$, $f:\mathrm{Fin}(n)\to A$ and $q\in\mathbf Z$. Let $T$ be associated sheafification followed by transport from $\operato…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-free-sheaf-dual-transpose: the existing statement concerns “Canonical finite free sheaf duality transposes matrix components” (Let X be a scheme, I,J finite types, and phi:O_X^(J) -> O_X^(I) a sheaf morphism. For i in I and j in J the (j,i) component of homObjFreeUnitIso(I)^-1 followed by precomposition with phi followed by homObjFreeU…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-p4-self-tor-affine-chart-sections: the existing statement concerns “Normalized sections of the open pushforward of an associated affine module” (Let $Y$ be a scheme [def-pc-scheme], $U$ an affine open [def-weil-affine-spectrum], $A=\Gamma(Y,U)$, and $M$ an $A$-module [def-weil-sheaf-of-modules-category]. Let $L=\widetilde M$ on $\operatorname{Spec}A$ [l…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-finite-retract-sheaves-affine-trivialization: the existing statement concerns “Simultaneous affine trivialization of finitely many finite free sheaf retracts” (Let X be a scheme [def-pc-scheme], U an open of X, s a finite set of integers, and M_n sheaves of O_U-modules [def-weil-sheaf-of-modules-category]. For each n in s assume maps i_n: M_n -> O_U^{m_n} and p_n: O_U…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-perfect-module-model: the existing statement concerns “Actual K-projective module models on affine opens” (Let $X$ be a scheme [def-pc-scheme], $U$ an affine open and $R=\Gamma(U,\mathcal O_X)$. Define $F_U:\mathrm{Mod}_R\to\mathrm{Mod}(\mathcal O_U)$ by tilde on $\operatorname{Spec}(R)$ [lem-weil-pbc-affine-tilde-g…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-koszul-hom-coefficient-complex-square: the existing statement concerns “Affine Koszul Hom coefficient complex square” (Let Y be a scheme, U an affine open, A=Γ(Y,U), I any ideal of A, n a natural number and f:Fin n → A any sequence. Set T=tilde followed by chart transport, TC its termwise complex functor, E=TC of the integer ex…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-finite-free-resolution-sheafification: the existing statement concerns “Sheafification of an explicit finite free resolution on an affine chart” (Let X be a scheme, U an open, and e : U.toScheme ≅ Spec A [def-weil-affine-spectrum]. Let M be an A-module, and let an explicit augmented exact resolution of M by finite free A-modules be given by ranks n, augm…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs def-pc-affine-base-change-tilde-coordinates: the existing statement concerns “Explicit affine base-change module and target coordinates” (Let A to D be a map of commutative rings, M an unbounded A-module complex, K a derived object on Spec A, e:Q(tilde M) isomorphic to K, and assume the canonical pullback counit on tilde M is invertible. Define t…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-mixed-affine-sections-underived-chart-model: the existing statement concerns “Ordinary affine chart extension and sections comparison with its unit equation” (Let $g:T\to S$ be a morphism between affine schemes [def-pc-scheme]. Put $F_S=\widetilde{(-)}\circ(S.toSpec\Gamma)^*$, where the second operation is exact restriction along the canonical spectrum chart [lem-wei…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-koszul-hom-coefficient-homology-square: the existing statement concerns “Homology transport of the affine Koszul coefficient square” (For any affine chart U of a scheme Y [def-pc-scheme], ideal I of A=Γ(Y,U), and sequence f:Fin n → A, the finite free Hom coefficient complex square [lem-sc-affine-koszul-hom-coefficient-complex-square] induces …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-stalk-scalar-extension-coordinates: the existing statement concerns “Exact affine stalk homology in scalar-extension coordinates” (Let A be a commutative ring, C a complex of A-modules, p a prime, and i an integer. Let D be the structure-sheaf stalk of Spec(A) at p, kappa:A to D its canonical map, F extension of scalars along kappa, N=tild…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-koszul-finite-free-resolution: the existing statement concerns “Sheafification of an augmented affine Koszul complex” (Let $i:Z\to Y$ be a closed immersion [def-weil-closed-immersion] of schemes [def-pc-scheme], $U$ an affine open of $Y$, $A=\Gamma(Y,U)$ and $I=i.\mathrm{ker}.\mathrm{ideal}(U)$ [def-sbc-closed-immersion-ideal-s…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-pullback-chart-tensor-flat-stalks: the existing statement concerns “Tensor flatness and relative stalk flatness on one pulled-back affine chart” (Let $A,T$ be commutative rings, $X,Y$ schemes [def-pc-scheme], $f:X\to\operatorname{Spec} A$, and $M$ a quasi-coherent $\mathcal O_X$-module [pqf-def-coherent]. Let $U$ be one affine open of $X$, with no coveri…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-tilde-kflat: the existing statement concerns “Associated sheaf of a K-flat complex on an affine scheme is K-flat” (Let $A$ be a commutative ring and $X=\operatorname{Spec}(A)$ [def-pc-scheme]. Let $K^\bullet$ be a cochain complex of $A$-modules that is K-flat, i.e. for every acyclic complex $F^\bullet$ of $A$-modules the to…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-s3-koszul-regular-affine-refinement: the existing statement concerns “A common regular affine refinement around a point of the immersion” (Let i:Z→Y be a closed immersion, U and Uprime affine opens of Y, and z in Z with i(z) in both opens. Suppose the ideal i.ker(U) is generated by a finite Koszul-regular sequence. There is an affine U0 containing…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-free-complex-module-lift: the existing statement concerns “Affine lifting of a free complex with its supplied unit coefficient” (Let R be a commutative ring, S=Spec R [def-weil-affine-spectrum], P a cochain complex [def-pc-derived-category] of O_S-modules [def-weil-sheaf-of-modules-category], and n:Z→N. Supply identifications e_j:P^j≅O_S…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-k4-affine-hom-comparison-right: the existing statement concerns “Covariant naturality of the normalized affine Hom comparison” (Let Y be a scheme, U an affine open, A=Gamma(Y,U), T the associated-sheaf functor transported along isoSpec, and c the comparison uniquely normalized on global generators [lem-sc-k4-affine-hom-generator-extensi…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-isomorphic-source-normalized-models: the existing statement concerns “Normalized affine pullback models from an isomorphic source chart” (Let $A,T$ be schemes [def-pc-scheme], let $A$ be affine and let $s:T\to A$ be an isomorphism. Let $M,N$ be quasi-coherent structure-sheaf modules on $A$ [pqf-def-coherent]. Put $P=\Gamma(T,s^*M)$ and $Q=\Gamma(…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-koszul-coefficient-hom-coordinates: the existing statement concerns “Underived affine Koszul Hom coefficient square” (Let i:Z -> Y be a closed immersion of schemes [def-pc-scheme, def-weil-closed-immersion], U an affine open, A=Gamma(Y,U), I=ker(i)(U) [def-sbc-closed-immersion-ideal-sheaf], n,m natural numbers, and f:Fin n -> …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-e3-affine-model-stalk-presentation: the existing statement concerns “Natural affine model presentation over the original local ring” (Let $Y$ be a scheme [def-pc-scheme], $x\in Y$, and $U\subseteq Y$ an affine open containing $x$. Put $A=\Gamma(U,\mathcal O_Y)$ and $S=\mathcal O_{Y,x}$ [def-pc-module-stalk-functor], with $A\to S$ the germ map…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-s2-affine-model-stalk-transport-linear: the existing statement concerns “Coordinate scalar compatibility of explicit affine stalk transport” (Let Y be a scheme [def-pc-scheme], x a point, and U an affine open containing x. Put A=Gamma(Y,U) and q=isoSpec(x). For an O_Y-module F [def-weil-sheaf-of-modules-category], an A-module M, and a model isomorphi…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-perfect-flat-model-replacement: the existing statement concerns “Affine perfect replacement with a quasi-isomorphism” (Let $Y$ be an affine scheme [def-pc-scheme], with derived localizations for its module category and each localized open site [def-pc-derived-category]. Let $D$ be a cochain complex of $\mathcal O_Y$-modules [de…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-k4-affine-hom-comparison-left: the existing statement concerns “Contravariant naturality of the normalized affine Hom comparison” (Let Y be a scheme, U an affine open, A=Gamma(Y,U), T the associated-sheaf functor transported along isoSpec, and c the comparison uniquely normalized on global generators [lem-sc-k4-affine-hom-generator-extensi…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-tensor-pullback-homology-comparison: the existing statement concerns “Affine tensor pullback comparison of homology” (Let S be an affine scheme [def-pc-scheme], C a cochain complex of quasi-coherent O_S-modules [def-pc-cochain-complex-modules] [pqf-def-coherent], A=Gamma(S,top), B any commutative A-algebra, a an integer, and P…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-lem-pc-affine-tilde-global-sections-stalk-coordinates: the existing statement concerns “Global-sections and stalk coordinates for a morphism from an affine tilde module” (Let A be a commutative ring, p a prime of A, i an integer, L an object of the derived quasi-coherent category of Spec(A) [lem-pc-affine-derived-cohomology-presentation], and V an A-module. Let d:tilde(V) to H^i…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-ordinary-tensor-stalk-coordinates: the existing statement concerns “Ordinary tensor target coordinates before the derived stalk presentation” (Let R,A,R',A' be commutative rings with the algebra structures and compatible maps of a cartesian spectrum square as in [def-pc-affine-base-change-tilde-coordinates]. Let M be any complex of A-modules, i an int…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-k3-affine-hom-comparison-maps: the existing statement concerns “Natural forward affine Hom comparison, invertible in rank one” (Let Y be a scheme [def-pc-scheme], U an affine open, A=Gamma(Y,U), and T the associated-sheaf functor transported by isoSpec [lem-weil-pbc-spec-module-tilde-sections]. There exists a family c(M,N):T(Hom_A(M,N))…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-pc-single-retract-sheaf-affine-trivialization: the existing statement concerns “Affine trivialization of one finite free sheaf retract” (Let X be a scheme [def-pc-scheme], U an open of X, and M a sheaf of O_U-modules [def-weil-sheaf-of-modules-category]. Suppose M is a retract of O_U^m for some natural number m, with section i and retraction p s…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-tilde-stalk-tensor-comparison: the existing statement concerns “Natural tensor comparison for associated-sheaf stalks” (Let $A$ be a commutative ring, let $X=\operatorname{Spec}(A)$ [def-pc-scheme], and let $x\in X$. Put $B=\mathcal O_{X,x}$ and let $\rho:A\to B$ be the canonical germ homomorphism. Write $S(M)=\widetilde M_x$ fo…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-sheaf-resolution-from-ring-model: the existing statement concerns “Sheafifying an actual finite-free affine ring resolution” (Let U be an affine open of a scheme T [def-pc-scheme], and C a cochain complex of quasi-coherent O_U-modules [def-pc-derived-category]. Write A=Γ(U,O_U). Let d be a natural number and P a cochain complex of A-m…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-k4-affine-hom-generator-extension: the existing statement concerns “Unique affine Hom comparison extending global generators” (Let Y be a scheme [def-pc-scheme], U an affine open, A=Gamma(Y,U), and T its associated-sheaf functor transported along isoSpec [lem-weil-pbc-spec-module-tilde-sections]. Identify T(A) with the structure sheaf …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-dimension-affine-open-cover: the existing statement concerns “The dimension of a scheme is the supremum of the dimensions of the rings of an affine open cover” (Let $X$ be a nonempty scheme [def-pc-scheme] and let $(U_i)_{i\in I}$ be a family of open subschemes of $X$ with $X=\bigcup_{i\in I}U_i$, each $U_i$ isomorphic to $\operatorname{Spec}A_i$ for a commutative ring…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-scalar-localized-tensor-square: the existing statement concerns “Affine algebraic tensor comparison after scalar extension to the fourth stalk” (Let R,A,R',A' be commutative rings and let the compatible maps phi_g':A to A' and phi_f':R' to A' form the cartesian spectrum square of [def-pc-affine-base-change-tilde-coordinates]. Let M be an A-K-flat comple…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-sections-complex-counit: the existing statement concerns “Affine quasi-coherent complex reconstructed from ordinary sections” (Let Y be an affine scheme [def-pc-scheme], A = Gamma(Y,O), and D an integer cochain complex of O_Y-modules [def-pc-cochain-complex-modules] with quasi-coherent terms. Apply ordinary sections termwise to obtain …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-flat-module-tilde: the existing statement concerns “The associated sheaf of a flat module is tensor-flat” (Let $A$ be a commutative ring and $M$ an $A$-module. Suppose $M$ is flat (tensoring $A$-modules with $M$ preserves exact sequences). Let $\widetilde M$ be the associated sheaf on $\operatorname{Spec}(A)$ [lem-w…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-base-change-ordinary-stalk-comparison: the existing statement concerns “Localization of the ordinary affine tensor comparison” (Let R,A,R',A' be commutative rings, with R-algebra structures on A and R', and an algebra map from A tensor_R R' to A'. Let phi_g' and phi_f' be its restrictions and assume the corresponding spectrum square is …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-finite-free-coefficient-comparisons: the existing statement concerns “Degreewise finite-free affine Hom comparisons with arbitrary coefficients” (Let $Y$ be a scheme [def-pc-scheme], $U$ an affine open, $A=\Gamma(Y,U)$, and $K_\bullet$ a chain complex of $A$-modules in nonnegative degrees [def-weil-pbc-module-chain-complex-homology] whose terms are finit…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-localized-tensor-stalk-square: the existing statement concerns “Localized affine derived tensor comparison in germ-normalized chain coordinates” (Let R,A,R',A' be commutative rings with the algebra structures and compatible maps of a cartesian spectrum square as in [def-pc-affine-base-change-tilde-coordinates]. Let M be an A-K-flat complex, m a BaseDeriv…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-g3-affine-koszul-signed-dual-coefficient-square: the existing statement concerns “Affine koszul signed dual coefficient square” (Let Y be a scheme [def-pc-scheme], U an affine open, A=Γ(Y,U), I an ideal of A, n a natural number and f:Fin n→A. Let T be associated sheafification transported from Spec A to U and TC its termwise functor on i…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-derived-cohomology-presentation: the existing statement concerns “Canonical module localization and exact stalk presentations of affine cohomology” (For a commutative ring A, an integer i and a derived object L with quasi-coherent cohomology on Spec A [def-pc-derived-category], define T_i(L) as the actual global sections of H^i(L) [lem-weil-pbc-spec-module-…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-tilde-preserves-finite-limits: the existing statement concerns “Finite-limit preservation by affine associated sheafification” (For every commutative ring A, the associated sheaf functor from A-modules to modules on Spec(A) [def-pc-scheme, def-weil-sheaf-of-modules-category] preserves all finite limits. There are no nonzero-ring or fini…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-universal-tensor-exact: the existing statement concerns “Square-zero affine base-change tests detect module tensor exactness” (Let S be an affine scheme [def-pc-scheme], C a cochain complex of quasi-coherent O_S-modules [def-pc-cochain-complex-modules] [pqf-def-coherent], and a an integer. Put A = Gamma(S,O_S) and let P be the complex …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-localizing-presheaf-sheafification: the existing statement concerns “Affine sections of a localizing presheaf survive sheafification” (Let $T$ be a scheme [def-pc-scheme] and $P$ a presheaf of $\mathcal O_T$-modules [def-weil-sheaf-of-modules-category]. Assume that for every affine open $W\subseteq T$ and every $a\in\Gamma(T,W)$, the restricti…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-opcycles-flat-from-sections: the existing statement concerns “Transfer flat global-sections opcycles to affine sheaf opcycles” (Let S be an affine scheme [def-pc-scheme], C a cochain complex of O_S-modules [def-pc-cochain-complex-modules], and a an integer. Assume C^(a-1) and C^a are quasi-coherent [pqf-def-coherent]. Let P be its termw…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-basis-dual-matrix: the existing statement concerns “Affine sheafification preserves transposed dual-basis components” (Let Y be a scheme, U an affine open, A=Gamma(Y,U), and T the associated sheaf functor followed by restriction along U.isoSpec. Let M,N be A-modules with finite bases bM:I and bN:J, f:N -> M, i:I, j:J. Write eM,…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-v2-exterior-power-localization: the existing statement concerns “Exterior powers preserve module localization, characterized on pure wedges” (Let R and B be commutative rings, B an R-algebra which is a localization at a multiplicative submonoid S of R [def-weil-pbc-module-localization]. Let M be an R-module and N a B-module. Suppose f : M -> N is R-l…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-coherent-affine-free-resolution: the existing statement concerns “Finite free resolution of a coherent sheaf on a Noetherian affine neighbourhood” (Let $X$ be a Noetherian scheme [def-weil-pbc-quasi-compact-scheme] [pqf-def-locnoeth], let $\mathcal F$ be a coherent $\mathcal O_X$-module [pqf-def-coherent], and let $x\in X$. Then there are an affine open ne…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-k3-affine-hom-comparison-finite-free: the existing statement concerns “Finite-basis inverse for a natural Hom comparison” (Let Y be a scheme [def-pc-scheme], U an affine open, A=Gamma(Y,U), and T any additive functor from A-modules to module sheaves on U. Suppose c(M,N):T(Hom_A(M,N)) -> internalHom(T(M),T(N)) [def-pur-sheaf-hom] is…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-projective-sections-sheafification: the existing statement concerns “Sheafification of a finite-projective affine section comparison” (Let $Y$ be an affine scheme [def-pc-scheme] and put $A=\Gamma(Y,\mathcal O_Y)$. Let $D$ be a cochain complex of $\mathcal O_Y$-modules [def-pc-cochain-complex-modules] with quasi-coherent terms. Let $P$ be a co…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-localizing-presheaf-basis-sheaf: the existing statement concerns “A localizing module presheaf satisfies the affine-basis sheaf condition” (Let T be a scheme [def-pc-scheme] and P a presheaf of O_T-modules [def-weil-sheaf-of-modules-category]. Suppose for every affine open W and every a in Gamma(T,W) the restriction P(W) -> P(D(a)), with scalars re…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-localization-sheafification: the existing statement concerns “Sheafification preserves affine values of localizing module presheaves” (Let T be a scheme [def-pc-scheme] and P a presheaf of O_T-modules [def-weil-sheaf-of-modules-category]. Assume that, for every affine open U of T and a ∈ Γ(T,U), the restriction P(U) → P(D(a)), considered as a …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-perfect-sections-projective-model: the existing statement concerns “Bounded finite-projective model of ordinary affine sections” (Let $Y$ be an affine scheme [def-pc-scheme], with the derived categories of module sheaves and localized open sites [def-pc-derived-category]. Put $A=\Gamma(Y,\mathcal O_Y)$. Choose a derived category of $A$-mo…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-k4-affine-hom-comparison-rankone: the existing statement concerns “Rank-one invertibility of the normalized affine Hom comparison” (Let Y be a scheme, U an affine open, A=Gamma(Y,U), T the associated-sheaf functor transported along isoSpec, and c the comparison uniquely normalized on global generators [lem-sc-k4-affine-hom-generator-extensi…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-intrinsic-flat-module-stalk-tensor-presentation: the existing statement concerns “Affine quasi-coherent stalks are tensor products of sections with the stalk ring” (Let Y be a scheme [def-pc-scheme], G a quasi-coherent O_Y-module [pqf-def-coherent], V an affine open of Y, and x a point of V. Put A=O_Y(V), M=G(V), and B=O_Y,x. Give M the section-module action restricted alo…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-finite-free-dual-naturality: the existing statement concerns “Explicit finite basis affine dual comparisons commute with precomposition” (Let Y be a scheme [def-pc-scheme], U an affine open, A=Γ(Y,U), and T the associated sheaf functor followed by transport along U.isoSpec. Let M,N be A-modules with specified finite bases bM indexed by I and bN i…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-localizing-principal-cover-gluing: the existing statement concerns “Unique gluing for a localizing module presheaf on a principal affine cover” (Let $T$ be a scheme [def-pc-scheme], $P$ a presheaf of $\mathcal O_T$-modules [def-weil-sheaf-of-modules-category], and $W$ an affine open. Assume for every $a\in\Gamma(T,W)$ the restriction $P(W)\to P(D(a))$, …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-strictly-perfect-finite-free-refinement: the existing statement concerns “Finite free refinement of a strictly perfect local representative” (Let $X$ be a scheme [def-pc-scheme], $E\in D(\mathcal O_X)$ [def-pc-derived-category], $U\subseteq X$ open, and $P$ a strictly perfect complex on $U$ [def-pc-perfect-complex] with $E|_U\cong Q(P)$. For every $x…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-pullback-chart-tensor-sections: the existing statement concerns “Tensor sections of one inverse-image affine chart” (Let $A,T$ be commutative rings, $X,Y$ schemes [def-pc-scheme], $f:X\to\operatorname{Spec}A$, $M$ a quasi-coherent module [pqf-def-coherent], and $U$ an affine open of $X$. Let $q:A\to T$, $p:Y\to\operatorname{S…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-universally-exact-opcycles-flat: the existing statement concerns “Flat degree-zero opcycles from universal degree-minus-one vanishing on an affine scheme” (Let S be an affine scheme [def-pc-scheme] and C a cochain complex of O_S-modules [def-pc-cochain-complex-modules]. Assume every C^n is quasi-coherent and flat over the identity S -> S [def-pc-morphism-conventio…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-base-change-tilde-stalk-comparison: the existing statement concerns “Stalk localization of explicit affine tensor coordinates” (Let R,A,R',A' be commutative rings with R-algebra structures on A,R' and a structure map A tensor_R R' to A'. Let phi_g':A to A' and phi_f':R' to A' be its restrictions and assume their spectrum square is carte…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-base-change-tilde-global-comparison: the existing statement concerns “Global mate square for explicit affine tensor coordinates” (Let R,A,R',A' be commutative rings with R-algebra structures on A,R' and a structure map A tensor_R R' to A'. Let phi_g':A to A' and phi_f':R' to A' be its restrictions and assume their spectrum square is carte…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-tensor-pullback-stalk-coordinates: the existing statement concerns “Canonical ordinary pullback cohomology coordinates at a stalk” (Let A and A' be commutative rings, phi:A to A' a ring map, and M any cochain complex of A-modules. Define the additive equivalence affineTensorPullbackHomologyStalkIso from the localization of H^i(A' tensor_A M…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pc-affine-tensor-pullback-complex-comparison: the existing statement concerns “Affine tensor pullback comparison of complexes” (Let S be an affine scheme [def-pc-scheme], C a cochain complex of quasi-coherent O_S-modules [def-pc-cochain-complex-modules] [pqf-def-coherent], A=Gamma(S,top), and B any commutative A-algebra. Assume the asso…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sfb-graded-fibre-hilbert-functions-finite: the new statement gives affine algebra/module presentations, simultaneous monomial section generators and stalk-fibre isomorphisms; the item asserts coherence and finite whole fibre functions.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-regular-stalk-scalar: the existing statement concerns “Scalar endomorphisms act on the affine unit germ by their germs” (Let X be a scheme [def-pc-scheme], x in an affine open U, A = Gamma(X,U), R = O_{X,x}, and H, b and mu_a as in [def-sc-affine-free-basis-germs]. For every a in A, H(mu_a)(b) = germ_U,x(a) b.…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-picard-residue-homology-comparison-source-residue: the existing statement concerns “picard_residue_homology_source_residue_comparison” (Under the complete signature below, the explicit degree-one affine residue cycles modulo boundaries compute the derived residue fibre of any object represented by the strictly perfect complex; no geometric dire…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-chart-scalar-transport: the existing statement concerns “Affine chart and slice scalar transport” (Let X be a scheme [def-pc-scheme], U an affine open, A=Gamma(X,U), and M any sheaf of modules on Spec A. Let f be an endomorphism of M acting as multiplication by a in A on sections of every open. After restric…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-affine-perfect-sections-counit: the existing statement concerns “Natural section reconstruction counit on affine perfect complexes” (For a scheme W and affine open U, terminal sections followed by the actual affinePerfectSheafification [lem-pc-affine-perfect-module-model], termwise on complexes, admits a natural transformation to the identit…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-picard-residue-source-model-homology: the existing statement concerns “picard_residue_source_model_homology” (theorem picard_residue_source_model_homology [∀ Y : Scheme.{v}, HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))] [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1} (Shea…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-regular-stalk-comparison-bijective: the existing statement concerns “The regular affine unit germ generates its ambient stalk freely” (Let X be a scheme [def-pc-scheme], x in an affine open U, and let H, b and c : O_{X,x} -> H(Gamma(X,U)) be the explicit maps of [def-sc-affine-free-basis-germs]. Then c, sending r to r b, is bijective.…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-free-sheaf-stalk-realization: the existing statement concerns “Natural finite-coordinate stalk comparison for affine sheafification” (Let X be a scheme [def-pc-scheme], x in an affine open U, A = Gamma(X,U), and R = O_{X,x} [def-pc-module-stalk-functor]. Let Phi = affinePerfectSheafification X U hU, the existing tilde/restriction/slice-equiva…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-free-stalk-comparison-bijective: the existing statement concerns “Bijectivity of finite coordinate combinations of affine basis germs” (Let X be a scheme [def-pc-scheme], x in an affine open U and let H and c_n be the explicit maps of [def-sc-affine-free-basis-germs]. For every natural number n the linear map c_n : ULift(Fin(n) -> O_{X,x}) -> H…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-principal-model-comparison: the existing statement concerns “Exact associated-sheaf comparison on a principal affine neighbourhood” (Let X be a scheme [def-pc-scheme], K a derived module-sheaf object [def-pc-derived-category], s in an affine open U, and M any complex of A=Gamma(X,U)-modules. Suppose the associated-sheaf complex [lem-pc-affin…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-free-residue-sections-derived-model: the existing statement concerns “Derived residue model from an affine free section complex” (Let W be a scheme, w a point, and E an object of its derived category, with fixed derived localizations on all schemes and localized open module sites [def-pc-scheme, def-pc-derived-category]. Let U be an affin…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-picard-ordinary-raw-coordinates: the existing statement concerns “Raw degree-zero and degree-one scalar coordinates and residue naturality” (Let $W$ be a scheme, $w\in U$ an affine open, $m\in\mathbb N$, and $d\in\Gamma(W,U)^m$. Let $K$ be a strictly perfect cochain complex on the localized module site over $U$ [def-pc-perfect-complex], and let $e_0…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs def-sc-affine-free-basis-germs: the existing statement concerns “Explicit affine basis germs and their linear combination map” (Let X be a scheme [def-pc-scheme], U an affine open with affine chart hU, x in U, A = Gamma(X,U), and R = O_{X,x} [def-pc-module-stalk-functor]. Write Phi = affinePerfectSheafification [lem-pc-affine-perfect-mo…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-integral-function-field-affine-fraction: the existing statement concerns “Function field of an integral scheme is the fraction field of an affine open” (Let $X$ be an integral scheme [def-pc-integral-scheme] and $\eta$ its generic point [def-sc-generic-point], i.e. the unique point with $\overline{\{\eta\}}=X$ [lem-sc-scheme-sober]. Let $U\subseteq X$ be a none…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-free-basis-germ-map: the existing statement concerns “Matrix action on the explicit finite free basis germs” (Let X be a scheme [def-pc-scheme], x in an affine open U, A = Gamma(X,U), R = O_{X,x}, and H and b_p^(n) as in [def-sc-affine-free-basis-germs]. For natural numbers n and m and any A-linear f : ULift(Fin(n) -> …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-picard-derived-fibre-residue-bridge-core: the existing statement concerns “Fixed-model residue naturality core” (For fixed affine strictly-perfect source and target complexes representing the derived direct images in the setup of new-picard-derived-fibre-residue-bridge, choose residue-to-derived-fibre and residue-to-struc…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-picard-derived-fibre-residue-bridge: the existing statement concerns “Common affine residue model bridge for derived fibre naturality” (In the geometric setup of new-picard-derived-fibre-naturality, choose a common affine neighbourhood, strictly perfect source and target residue models, their residue-to-derived-fibre and residue-to-structure-sh…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-picard-derived-fibre-residue-model-data: the existing statement concerns “Simultaneous affine strictly-perfect residue model data” (For the geometric setup of new-picard-derived-fibre-residue-bridge, choose one affine neighbourhood of the marked point and strictly-perfect source and target complexes representing the localized derived direct…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-tilde-scalar-section-action: the existing statement concerns “Associated sheaf scalar action on all sections” (For a commutative ring R, an R-module M, a in R, and an endomorphism f acting as a times the identity on M, tilde(f) acts as a times the identity on sections over every open of Spec R. The associated-sheaf func…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-picard-residue-quotient-model-homology: the existing statement concerns “picard_residue_quotient_model_homology” (theorem picard_residue_quotient_model_homology [∀ Y : Scheme.{v}, HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))] [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1} (Sh…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-scalar-section-action: the existing statement concerns “Affine scalar endomorphism action on sections over its chart” (Let $X$ be a scheme [def-pc-scheme], $U$ an affine open, and $A=\Gamma(X,U)$. Write $\Phi$ for affinePerfectSheafification [lem-pc-affine-perfect-module-model], and $P$ for ordinary direct image from the slice …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-affine-residue-model-naturality: the existing statement concerns “Naturality of all represented affine residue arrows” (Let E be a derived object on W, represented over an affine open U containing w by a strictly perfect K and a specified isomorphism m: restriction(E) ~= Q(K). Let p=ker(evaluation). There exists one additive com…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-affine-perfect-residue-model-naturality: the existing statement concerns “Natural derived residue model on the full perfect subcategory” (For W,w and an affine open U containing w, restrict to the full subcategory of IsStrictlyPerfect complexes. The functor taking homology after extending terminal sections along evaluation is naturally isomorphic…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs new-affine-residue-evaluation-homology-naturality: the existing statement concerns “Natural residue homology comparison with evaluation scalars” (Let W,U,w be an affine open neighborhood of w and let p=ker(evaluation at w). For every localized module complex K there is an additive isomorphism from affineResidueCycleHomology to homology of its section com…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-free-terminal-sections-reconstruction: the existing statement concerns “Finite free slice complex reconstructed from terminal sections” (Let W be a scheme and U an affine open [def-pc-scheme]. Let K be an integer cochain complex of module sheaves on the localized open site of U [def-pc-cochain-complex-modules]. For r: Z -> N suppose K^j is isomo…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-spec-tilde-free-module: the existing statement concerns “On Spec R the free module of rank n is the sheaf associated to R^n (Stacks 01HV(1)-(2), 01I7)” (Let $R$ be a commutative ring, $X=\operatorname{Spec}R$ [def-weil-affine-spectrum], $n\ge0$, and let $\mathcal O_X^{\oplus n}$ be the free $\mathcal O_X$-module of rank $n$ [def-weil-sheaf-of-modules-category] …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-global-formal-comparison: the existing statement concerns “Affine formal equivalence with quotient-system and section-limit natural comparisons” (Let X be an affine Noetherian scheme, J ideal sheaf data, and Coh(X,J) the coherent formal category [def-weil-pbc-coherent-formal-module]. Put A=Gamma(X,top), I=J(top), S=AdicCompletion I A [def-weil-pbc-adic-c…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-module-pullback-affine-sections-bijective: the existing statement concerns “Bijectivity of the affine pure-tensor sections map” (Let $f:X\to Y$ be a morphism of schemes [def-pc-scheme], $V\subseteq Y$ and $U\subseteq X$ affine opens with $U\subseteq f^{-1}V$, $A=\mathcal O_Y(V)$ and $B=\mathcal O_X(U)$ with its $A$-algebra structure indu…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-map-annihilation-sheafification: the existing statement concerns “Transfer a uniform annihilator bound through affine sheafification” (Let X be affine Noetherian, J ideal sheaf data, A=Γ(X,⊤), I=J(⊤), and L=tilde followed by pullback along X≅Spec A. For arbitrary A-modules T,P, a linear map ψ:T→P, an X-module G and an isomorphism ε:L(P)≅G, if …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-coherent-formal-modules-affine-reconstruction: the existing statement concerns “Affine formal modules: Reconstruction” (Let A, I, B, X, J and the fixed canonical quotient functor Q be as in the statement dependencies. Let L be any functor from coherent formal J-modules to finite B-modules and p(F) a family of cones to the A-modu…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-spec-domain-stalks-function-field: the existing statement concerns “Stalks and function field of the spectrum of a domain” (Let $R$ be a commutative ring and $X=\operatorname{Spec}R$ [def-weil-affine-spectrum]. (1) For every prime $\mathfrak p\subset R$ the stalk $\mathcal O_{X,\mathfrak p}$, with the map $R=\Gamma(X,\mathcal O_X)\t…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-module-pullback-affine-sections: the existing statement concerns “Sections of the pullback of a quasi-coherent module over an affine open” (Let $f:X\to Y$ be a morphism of schemes [def-pc-scheme], $\mathcal G$ a quasi-coherent $\mathcal O_Y$-module [pqf-def-coherent], [def-weil-sheaf-of-modules-category], and $f^*\mathcal G$ its pullback [def-pc-mo…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs stage3-affine-pushout-ring-affine-sections: the existing statement concerns “Affine sections preserve the structure-algebra ring pushout” (Let $f:U\to X$ be affine, $A=f_*\mathcal O_U$, $r_0:f^{-1}\mathcal O_X\to\mathcal O_U$ the structure map, and $t_0=f^{-1}\rho$ for $\rho:\mathcal O_X\to A$. Suppose $b:\mathcal O_U\to B$ and $t:f^{-1}A\to B$ fo…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-quasi-coherent-iso-on-affine-cover: the existing statement concerns “A map of quasi-coherent modules bijective on an affine open cover is an isomorphism” (Let $Y$ be a scheme [def-pc-scheme], $\varphi:\mathcal F\to\mathcal G$ a morphism of $\mathcal O_Y$-modules [def-weil-sheaf-of-modules-category] between quasi-coherent $\mathcal O_Y$-modules [pqf-def-coherent],…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs stage3-affine-pushout-ring-section-delta: the existing statement concerns “Second leg on sections from the inverse-image unit” (Let f:U → X be a morphism of schemes. Put A=f_*O_U, ρ:O_X → A its structure map, IA=f⁻¹A, r₀:f⁻¹O_X → O_U its adjoint structure map, and t₀=f⁻¹ρ. Let B be a commutative-ring sheaf on U, b:O_U → B and t:IA → B m…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-intersection-quotients-stalk: the existing statement concerns “Localization of affine quotient systems with a prescribed kernel filtration” (Let $X$ be a scheme [def-pc-scheme], $I$ a quasi-coherent ideal sheaf [def-sbc-ideal-sheaf-powers], $U$ an affine open, and $S:\mathbf N^{\mathrm{op}}\to\operatorname{Mod}(\mathcal O_X)$ [def-weil-sheaf-of-modu…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-tilde-principal-localization-transport: the existing statement concerns “TildePrincipalLocalizationTransport” (Let $R$ be a commutative ring, $N$ an $R$-module and $e:X\cong\operatorname{Spec}R$ an isomorphism of schemes. Let $G=e^*(\widetilde N)$, using restriction along $e$ [lem-weil-pbc-spec-module-tilde-sections]. T…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-quasi-coherent-module-cokernel-image: the existing statement concerns “Cokernel and image of a morphism of quasi-coherent modules: quasi-coherent, computed on affine opens” (Let $X$ be a scheme [def-pc-scheme] and $\varphi:\mathcal F\to\mathcal G$ a morphism of $\mathcal O_X$-modules [def-weil-sheaf-of-modules-category] between quasi-coherent $\mathcal O_X$-modules [pqf-def-coheren…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-coherent-tilde-presentation: the existing statement concerns “Associated-module presentation of a coherent sheaf on an affine scheme” (Let X be affine Noetherian and H a coherent module [def-weil-pbc-coherent-formal-module]. There exists a module P over A=Γ(X,⊤) and an isomorphism from tilde(P) [lem-weil-pbc-spec-module-tilde-sections] pulled …); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-module-basic-open-localization: the existing statement concerns “Affine basic-open sections of a quasi-coherent module satisfy the two localization conditions” (Let $X$ be a scheme [def-pc-scheme], $F$ a quasi-coherent $\mathcal O_X$-module [pqf-def-coherent], $U$ an affine open [def-weil-affine-spectrum], and $g\in\Gamma(X,U)$. (1) For every $s\in\Gamma(F,D(g))$ there…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-spec-module-tilde-sections: the existing statement concerns “The quasi-coherent sheaf of a module on Spec and its sections over principal opens” (Let $R$ be a commutative ring and $N$ an $R$-module. There is a sheaf of $\mathcal O_{\operatorname{Spec}R}$-modules $\widetilde N$ on $\operatorname{Spec}R$ [def-weil-sheaf-of-modules-category] with $R$-linear…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-spec-map-residue-field-naturality: the existing statement concerns “Spec of a ring map on points and on residue fields” (Let $\psi:R\to R'$ be a homomorphism of commutative rings and $\operatorname{Spec}\psi:\operatorname{Spec}R'\to\operatorname{Spec}R$ the induced morphism of schemes [def-weil-affine-spectrum]. Let $\mathfrak p'…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-core: the existing statement concerns “Normalized sectionwise fixed-chart comparisons” (Under the hypotheses of lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed, there is an additive whole-chart comparison a such that on each principal open independently there exists a bijective sectio…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs stage3-affine-pushout-ring-section-map-tmul: the existing statement concerns “Pure-tensor formula for the section tensor map” (Let f:U → X be a morphism of schemes. Put A=f_*O_U, ρ:O_X → A its structure map, IA=f⁻¹A, r₀:f⁻¹O_X → O_U its adjoint structure map, and t₀=f⁻¹ρ. Let B be a commutative-ring sheaf on U, b:O_U → B and t:IA → B m…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-quasicoherent-epi-affine-cover: the existing statement concerns “Surjectivity on an affine cover implies a quasi-coherent-target epimorphism” (Let $X$ be a scheme [def-pc-scheme], $M,N$ sheaves of $\mathcal O_X$-modules [def-weil-sheaf-of-modules-category], with $N$ quasi-coherent [pqf-def-coherent], and $\varphi:M\to N$ a morphism. Let $(U_i)_{i\in I…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-completion-affine-sections-coordinates: the existing statement concerns “Affine coordinates for coherent completion quotient sections” (Let X be a Noetherian scheme, I a quasi-coherent ideal sheaf and P a coherent module [def-weil-pbc-coherent-formal-module]. For an affine open U [def-weil-affine-spectrum], put A=O_X(U), J=I(U) and C=the J-adic…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-spec-tilde-stalk-localization: the existing statement concerns “Stalks of tilde modules are localizations” (Let $R$ be a commutative ring, $X=\operatorname{Spec}R$ [def-weil-affine-spectrum], $\mathfrak p\subset R$ a prime ideal with point $x\in X$, and $S=R\setminus\mathfrak p$. Let $S\subseteq R$ be a multiplicativ…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-generators: the existing statement concerns “Whole-chart sections generate principal-open sections” (Under the hypotheses of lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed, restrictions of sections of F on the whole fixed affine chart span its sections on each principal open, over the section rin…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-spec-residue-field-identification: the existing statement concerns “Residue fields of Spec R and the canonical morphism Spec kappa(p) -> Spec R” (Let $R$ be a commutative ring, $\operatorname{Spec}R$ its spectrum [def-weil-affine-spectrum] and $\mathfrak p\in\operatorname{Spec}R$. Let $\kappa_{\operatorname{Spec}R}(\mathfrak p)$ be the residue field of t…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs stage3-affine-pushout-ring-section-products: the existing statement concerns “Finite product generation of affine ring-sheaf pushout sections” (Let f:U → X be a morphism of schemes. Put A=f_*O_U, ρ:O_X → A its structure map, IA=f⁻¹A, r₀:f⁻¹O_X → O_U its adjoint structure map, and t₀=f⁻¹ρ. Let B be a commutative-ring sheaf on U, b:O_U → B and t:IA → B m…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs stage3-affine-pushout-ring-section-comm: the existing statement concerns “Commutativity of the ring-sheaf pushout section square” (Let f:U → X be a morphism of schemes. Put A=f_*O_U, ρ:O_X → A its structure map, IA=f⁻¹A, r₀:f⁻¹O_X → O_U its adjoint structure map, and t₀=f⁻¹ρ. Let B be a commutative-ring sheaf on U, b:O_U → B and t:IA → B m…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-spec-map-stalk-localization: the existing statement concerns “The stalk maps of Spec of a ring map are the induced maps of localizations” (Let $\psi:R\to R'$ be a homomorphism of commutative rings and $\operatorname{Spec}\psi:\operatorname{Spec}R'\to\operatorname{Spec}R$ the induced morphism of schemes [def-weil-affine-spectrum]. Let $Q\subset R'$…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-tilde-gamma-adjunction: the existing statement concerns “On Spec R, M ↦ M~ is left adjoint to global sections, fully faithful, and an equivalence onto quasi-coherent modules; it preserves colimits” (Let $R$ be a commutative ring, $X=\operatorname{Spec}R$ [def-weil-affine-spectrum], and for an $R$-module $M$ let $\widetilde M$ be the $\mathcal O_X$-module of [lem-weil-pbc-spec-module-tilde-sections], with $…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-spec-map-global-sections: the existing statement concerns “Spec of a ring map induces that ring map on global sections” (Let $\psi:C\to B$ be a homomorphism of commutative rings and $\operatorname{Spec}\psi:\operatorname{Spec}B\to\operatorname{Spec}C$ the induced morphism of schemes [def-weil-affine-spectrum]. Let $\varepsilon_B:…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-open-section-vanishing-prime: the existing statement concerns “Sections over an affine open: vanishing at a point iff membership in its prime; basic opens are affine with ring the localization” (Let $X$ be a scheme [def-pc-scheme], $U\subseteq X$ an affine open, $R=\mathcal O_X(U)$, and for $x\in U$ let $\mathfrak p_x\subset R$ be the prime ideal of $x$ given by $U\cong\operatorname{Spec}R$ [lem-weil-p…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-open-stalk-localization: the existing statement concerns “Stalk of a scheme at a point of an affine open: the canonical open immersion and the localization” (Let $X$ be a scheme [def-pc-scheme], $U\subseteq X$ an affine open, $R=\mathcal O_X(U)$, and $\iota_U:\operatorname{Spec}R\to X$ the canonical open immersion with image $U$ [lem-weil-pbc-affine-open-spec-points…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-weil-pbc-affine-section-linear-map-extension: the existing statement concerns “Extending an affine linear section map from a quasi-coherent source” (Let $X$ be a scheme [def-pc-scheme], $P,Q$ sheaves of $\mathcal O_X$-modules [def-weil-sheaf-of-modules-category], and $V\subseteq X$ an affine open [def-weil-affine-spectrum]. Assume $P$ is quasi-coherent [pqf…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs stage3-affine-pushout-ring-section-map-injective: the existing statement concerns “Injectivity of the canonical affine tensor section map” (Let f:U → X be a morphism of schemes. Put A=f_*O_U, ρ:O_X → A its structure map, IA=f⁻¹A, r₀:f⁻¹O_X → O_U its adjoint structure map, and t₀=f⁻¹ρ. Let B be a commutative-ring sheaf on U, b:O_U → B and t:IA → B m…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs stage3-affine-pushout-ring-section-map: the existing statement concerns “Canonical tensor section map for a ring-sheaf pushout” (Let f:U → X be a morphism of schemes. Put A=f_*O_U, ρ:O_X → A its structure map, IA=f⁻¹A, r₀:f⁻¹O_X → O_U its adjoint structure map, and t₀=f⁻¹ρ. Let B be a commutative-ring sheaf on U, b:O_U → B and t:IA → B m…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-pur-coordinate-subspace-generic-stalk: the existing statement concerns “Ambient fibre stalk at the generic point of a coordinate subspace” (Let S be a scheme [def-pc-scheme], U an affine open of S, R=Γ(S,U), and s a prime of R. Let z be a point of A^a_S [def-sbc-affine-space] over the image of s, whose image in its scheme-theoretic fibre is generic…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-affine-monomial-models vs lem-sc-affine-cap-section-open-dictionary: the existing statement concerns “Affine dictionary for an invertible module and its section” (Let R be a commutative ring, X=Spec(R), and M an invertible O_X-module (that is, an O_X-module which is locally free of rank 1) [def-sc-invertible-module]. Put N=Gamma(X,M). Then the canonical counit identifies…); it does not assert a finite affine cover with simultaneous monomial generators for a graded sheaf algebra/module and its actual section-fibre models.

lem-sfb-graded-quotient-generic-ranks vs lem-sbc-finite-flat-affine-basis: the existing statement concerns “A finite flat section algebra has a finite basis on an affine neighbourhood of each target point.” (Let $f:X\to Y$ be a finite flat morphism [def-weil-finite-integral-morphism, def-weil-flat-morphism] of schemes [def-weil-pbc-scheme-conventions], with $Y$ locally Noetherian [def-weil-pbc-noetherian-ring]. For…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sbc-finite-type-algebra-generic-flatness: the existing statement concerns “Finite type algebras over arbitrary domains are generically flat” (Let R and B be commutative rings with R an integral domain, and let φ : R → B be a finite type ring map [def-weil-pbc-finite-type-algebra]. There is a nonzero a ∈ R such that, for every B-algebra T that is a lo…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-trf-regular-local-pic-zero: the existing statement concerns “Picard group of a regular-local localization vanishes” (Let $(A,\mathfrak m)$ be a regular local ring [def-weil-regular-scheme], let $f\in A$, and let $A_f$ be the localization of $A$ at $f$ [def-weil-ring-localization-away]. Let $P$ be a finitely generated projecti…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-flat-model-finite-free-shortening: the existing statement concerns “Local finite-free shortening of a pseudo-coherent bounded flat model” (Let U⊆T be open in a scheme [def-pc-scheme], t∈U and d≥0. Let C,Q be complexes of O_U-modules [def-pc-derived-category], with C supported in [0,d] and termwise flat over U, Q supported in degrees ≤d and termwis…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-affine-residue-epi-splitting: the existing statement concerns “Affine residue surjectivity splits a map onto a finite-presentation flat module” (Let $S$ be an affine scheme [def-pc-scheme], let $M,N$ be quasi-coherent $\mathcal O_S$-modules [def-weil-sheaf-of-modules-category, pqf-def-coherent], and let $f:M\to N$ be a module morphism. Assume that $N$ i…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-split-top-differential-cancellation: the existing statement concerns “Cancellation of one split top differential” (Let $S$ be a scheme [def-pc-scheme] and let $B$ be an integer-indexed cochain complex of $\mathcal O_S$-modules [def-pc-cochain-complex-modules] supported in $[0,m+1]$ for $m\in\mathbf N$. Suppose its terms are…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-finite-retract-sheaves-affine-trivialization: the existing statement concerns “Simultaneous affine trivialization of finitely many finite free sheaf retracts” (Let X be a scheme [def-pc-scheme], U an open of X, s a finite set of integers, and M_n sheaves of O_U-modules [def-weil-sheaf-of-modules-category]. For each n in s assume maps i_n: M_n -> O_U^{m_n} and p_n: O_U…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-flat-model-finite-free-shortening-construction: the existing statement concerns “Structural local finite-free construction” (Under the hypotheses of lem-pc-flat-model-finite-free-shortening there exist V ≤ U, P, and a quasi-isomorphism eP : P ⟶ (V → U)^*C, with t ∈ V, P supported in [0,d], and every P term finite free.…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-principal-open-finite-projective-tilde: the existing statement concerns “Finite projective principal localizations give a finite locally free associated sheaf on an open” (Let A be a commutative ring and U an open of Spec A [def-pc-scheme]. Let M be an A-module. Suppose that for every f in A with D(f) contained in U, M_f is a finite projective A_f-module. Then the restriction to …); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-flat-model-finite-free-structural-data: the existing statement concerns “Structural local finite-free data” (Under the hypotheses of lem-pc-flat-model-finite-free-shortening there exist V ≤ U and P over V with t ∈ V, P supported in [0,d], and every P term finite free.…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-finite-projective-module-colimit-descent: the existing statement concerns “Descent of one finite projective module over a directed ring colimit” (Let $I$ be a nonempty directed preorder and $F:I\to\mathrm{CommRing}$ a diagram with colimit $A$ [def-weil-pbc-category-colimit]. For every finite projective $A$-module $X$ [def-weil-pbc-projective-module], the…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-flat-model-finite-free-shortening-comparison: the existing statement concerns “Pullback homology comparison for the local replacement” (Given the hypotheses, structural output V ≤ U and P, and a quasi-isomorphism eP : P ⟶ (V → U)^*C, for every g and q the pullback homology of P is nonempty isomorphic to that of C pulled back to U.…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs new-pc-single-retract-sheaf-affine-trivialization: the existing statement concerns “Affine trivialization of one finite free sheaf retract” (Let X be a scheme [def-pc-scheme], U an open of X, and M a sheaf of O_U-modules [def-weil-sheaf-of-modules-category]. Suppose M is a retract of O_U^m for some natural number m, with section i and retraction p s…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-flat-model-finite-free-quasi-iso: the existing statement concerns “Quasi-isomorphism for local finite-free model” (Under the hypotheses of lem-pc-flat-model-finite-free-shortening and a point t ∈ U, there exist V ≤ U and a complex P supported in [0,d] with finite-free terms, with quasi-isomorphisms eQ : (V → U)^*Q ⟶ P and e…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-flat-model-finite-free-truncation-zero: the existing statement concerns “Local finite freeness of the canonical truncation in degree zero” (Let T be a scheme, U an open subscheme, d a natural number, C a flat complex strictly supported in [0,d], Q a complex of finite-free modules strictly bounded above by d, and e : Q → C a quasi-isomorphism. For e…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-strictly-perfect-finite-free-refinement: the existing statement concerns “Finite free refinement of a strictly perfect local representative” (Let $X$ be a scheme [def-pc-scheme], $E\in D(\mathcal O_X)$ [def-pc-derived-category], $U\subseteq X$ open, and $P$ a strictly perfect complex on $U$ [def-pc-perfect-complex] with $E|_U\cong Q(P)$. For every $x…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-projective-dimension-locus-open: the existing statement concerns “Openness of a fixed projective-dimension bound” (Let R be a commutative Noetherian ring [def-weil-pbc-noetherian-ring], M a finite R-module [def-weil-finitely-generated-module], and n a natural number. The set of primes p of R such that Ext^i_{R_p}(M_p,N) van…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-coherent-free-stalks-locally-free: the existing statement concerns “Coherent sheaves with free stalks are locally free” (Let $X$ be a locally Noetherian [pqf-def-locnoeth] scheme [def-pc-scheme] and let $\mathcal F$ be a coherent [pqf-def-coherent] $\mathcal O_X$-module. If every stalk $\mathcal F_x$ is a finite free $\mathcal O_…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pc-split-top-differential-cancellation-properties: the existing statement concerns “Flat quasi-coherent finite-presentation sheaves are closed under retracts” (Let $S$ be a scheme [def-pc-scheme] and $M,N$ be $\mathcal O_S$-modules [def-weil-sheaf-of-modules-category]. Suppose there are maps $i:M\to N$ and $r:N\to M$ with $r\circ i=\mathrm{id}_M$. If $N$ is flat over …); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-universal-h0-split-differential: the existing statement concerns “Universal rank-one kernels split the first differential” (Let R be a commutative ring and P a cochain complex of R-modules (modules P^i with differentials d^i: P^i -> P^(i+1) and d^(i+1) d^i = 0). Suppose P^(-1) = 0 and P^0 and P^1 are finite projective (finitely gene…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-connective-universal-h0-zero-differential: the existing statement concerns “Cancelling the degree-zero complement in a connective universal rank-one complex” (Let R be a commutative ring and P a bounded cochain complex of finite projective R-modules [def-pc-perfect-ring-complex] whose terms in negative degrees are zero. Assume H0 of its termwise scalar extension to e…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs new-residue-kernel-unit-minor-base-change-free: the existing statement concerns “Finite projective modules become free after localization at a prime.” (For a commutative ring R, finite projective R-modules X and Y, and a prime ideal 𝔭, the scalar extensions of X and Y to Localization.AtPrime 𝔭 are free modules over that localization.…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-residue-bottom-differential: the existing statement concerns “A single bottom differential is split injective from residue exactness” (Let R be a commutative ring and P a cochain complex of R-modules indexed by the integers. Let a be an integer. Suppose P^(a-1) is zero, and P^a and P^(a+1) are finite projective R-modules [def-pc-perfect-ring-c…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs new-residue-kernel-unit-minor-kernel: the existing statement concerns “Diagonal matrix normal form for a residue rank-one kernel” (Let R be a commutative ring, X and Y finite projective R-modules, f:X→Y linear, and p a prime. Put A=R_p and κ=A/m. Suppose ker(f⊗κ) is linearly isomorphic to κ. There exist A-modules U,C, an A-linear map g:A→C…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs new-residue-kernel-unit-minor: the existing statement concerns “Residue rank-one kernel gives a one-column residual normal form” (Let R be a commutative ring, X and Y finite projective R-modules, f:X->Y an R-linear map, and p a prime. Set A=R_p and kappa=A/m_A. Assume the kernel of f tensor_R kappa is isomorphic to kappa. Then there exist…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-principal-cokernel-projective-descent: the existing statement concerns “Injectivity and projective cokernel descend from a principal cover” (Let R be a commutative ring, M a finitely generated R-module and N a finitely presented R-module. Let f : M -> N be R-linear. Suppose that for each prime ideal p of R there exists s outside p such that the map …); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs new-universal-h0-split-factorization: the existing statement concerns “Universal H0 splitting factorization data” (Let R be a commutative ring and P a cochain complex of R-modules with P^(-1)=0 and P^0,P^1 finite projective. Suppose that for every commutative R-algebra B, H^0(P tensor_R B) is isomorphic to B. Then there are…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-residue-connective-projective-opcycles: the existing statement concerns “Finite projectivity of zeroth opcycles from negative residue exactness” (Let R be a commutative ring and P a bounded cochain complex of finite projective R-modules [def-pc-perfect-ring-complex]. Suppose for every prime ideal p of R that termwise extension of scalars to its residue f…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-bounded-free-stalk-model-spread: the existing statement concerns “Spreading a given bounded free stalk model” (Let X be a scheme [def-pc-scheme], E an object of D(O_X) [def-pc-derived-category] with a strictly perfect representative on a neighbourhood of x [def-pc-perfect-complex], and G a sheaf complex with Q(G) isomor…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs new-universal-h0-cokernel-local-free: the existing statement concerns “Universal rank-one H0 gives a locally free first cokernel” (Let R be a commutative ring and P a cochain complex of R-modules. Suppose P^(-1)=0 and P^0 and P^1 are finitely generated projective R-modules. Suppose that for every commutative R-algebra B, the degree-zero ho…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs new-residue-kernel-unit-minor-pivot: the existing statement concerns “Invertible leading pivot for a finite free map with residue kernel dimension one” (Let R and A be commutative rings with an R-algebra structure on the local ring A. Let f : X → Y be an R-linear map. Suppose A ⊗_R X and A ⊗_R Y are finite free and the kernel of κ(A) ⊗_R f is isomorphic to κ(A)…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs new-residue-kernel-unit-minor-matrix-core: the existing statement concerns “Matrix unit-minor normalization over a local ring assuming localized modules are free.” (Given finite free scalar extensions over a local ring and a map whose residue has one-dimensional kernel, the map is equivalent by source and target linear equivalences to (u,a) ↦ (u,g(a)) with a free complemen…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-zariski-pair-rank-one-propagation: the existing statement concerns “A finite flat algebra is rank one when it is rank one modulo a Zariski-pair ideal” (Let $A$ be a commutative ring and $I\subseteq A$ an ideal contained in the Jacobson radical of $A$ (the intersection of all maximal ideals of $A$). Let $A\to B$ be a homomorphism of commutative rings such that …); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-finitely-presented-flat-module-projective: the existing statement concerns “A finitely presented flat module is finite projective” (Let $A$ be a commutative ring and $M$ an $A$-module which is finitely presented (there is an exact sequence $A^{\oplus m}\to A^{\oplus n}\to M\to0$ for some $m,n\ge0$; in particular $M$ is a finitely generated …); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-finite-projective-rank-locally-constant: the existing statement concerns “The rank of a finite projective module is locally constant on Spec” (Let $A$ be a commutative ring and $M$ a finite projective $A$-module (e.g. a direct summand of a finite free $A$-module). Then for every prime $\mathfrak p\subset A$ the localization $M_{\mathfrak p}$ is a fini…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-finite-projective-descends-flat-local: the existing statement concerns “Finite projective modules descend along flat local homomorphisms” (Let $(R,\mathfrak m_R)$ and $(S,\mathfrak m_S)$ be local rings and $\varphi:R\to S$ a local homomorphism ($\varphi(\mathfrak m_R)\subseteq\mathfrak m_S$) which is flat [def-weil-pbc-flat-ring-map]. Let $M$ be a…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-finite-projective-prime-local-free: the existing statement concerns “A finite projective module is free after localizing away from each prime” (Let $A$ be a commutative ring and $M$ a finite projective $A$-module, i.e. $M$ is finitely generated [def-weil-finitely-generated-module] and projective [def-weil-pbc-projective-module]. For every prime ideal $…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-finite-projective-finitely-presented: the existing statement concerns “A finite projective module is finitely presented” (Let $A$ be a ring and $M$ an $A$-module which is finitely generated [def-weil-finitely-generated-module] and projective [def-weil-pbc-projective-module]. Then $M$ is finitely presented: there is an exact sequen…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-finite-projective-standard-free-cover: the existing statement concerns “A direct summand of a finite free module is finite locally free (standard cover)” (Let $A$ be a commutative ring and $M$ an $A$-module which is a direct summand of a finite free $A$-module (equivalently, $M$ is finite projective). Then there are finitely many elements $f_1,\dots,f_r\in A$ gen…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-principal-contraction-spreading: the existing statement concerns “Spreading local contraction data with free complements” (Let R be a commutative ring, p a prime, and X,Y,Z finite free R-modules [def-weil-pbc-free-module]. Let a:X→Y and b:Y→Z satisfy b∘a=0. Set L=R_p [def-weil-pbc-localization-at-prime]; scalar extensions are [def-…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs stage3-b4-bounded-finite-free-resolution: the existing statement concerns “Bounded finite free resolution construction” (Let R be a commutative Noetherian local ring [def-weil-pbc-noetherian-ring], M a finite R-module [def-weil-finitely-generated-module], and d a natural number. If M has a projective resolution of length at most …); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-zariski-pair-flat-integral-isomorphism: the existing statement concerns “Flat integral finitely presented algebra which is an isomorphism modulo a radical ideal is an isomorphism” (Let $A$ be a commutative ring and $I\subseteq A$ an ideal contained in the Jacobson radical of $A$ (a Zariski pair). Let $A\to B$ be a ring map which is flat ($B$ is a flat $A$-module [def-weil-pbc-flat-ring-ma…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-weil-pbc-minimal-finite-free-resolution-local: the existing statement concerns “Minimal finite free resolutions over a Noetherian local ring” (Let $(R,\mathfrak m)$ be a Noetherian local ring [def-weil-pbc-noetherian-ring] with maximal ideal $\mathfrak m$, let $M$ be a finitely generated $R$-module [def-weil-finitely-generated-module] and let $d\ge0$ …); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-pur-noetherian-algebra-module-generic-freeness: the existing statement concerns “Noetherian generic freeness for finite algebra-module pairs” (Let $R$ be a commutative Noetherian integral domain [def-weil-pbc-noetherian-ring], let $B$ be a commutative $R$-algebra of finite type, meaning $B\cong R[x_1,\ldots,x_n]/J$ for some finite $n\geq0$ and an idea…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-trf-finite-tor-amplitude-perfect: the existing statement concerns “Finite Tor amplitude and perfectness over the finite coefficient ring” (Let $A=A_{E,n}=\mathcal O_E/\varpi_E^n$ be the finite coefficient ring, so that $A$ is a local Artinian ring with maximal ideal $(\varpi_E)$, and let $C$ be a bounded complex of $A$-modules whose cohomology mod…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-affine-standard-cover-finite-presentation-flat: the existing statement concerns “A finite standard-open free cover gives finite presentation and flatness” (Let $R$ be a commutative ring and $N$ an $R$-module. If there are finitely many elements $f_1,\dots,f_r\in R$ generating the unit ideal such that each localization $N_{f_i}$ [def-weil-pbc-module-localization-aw…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-affine-standard-cover-finite-projective: the existing statement concerns “A finite standard-open free cover makes a module finite projective” (Let $R$ be a commutative ring and $N$ an $R$-module. If there are finitely many elements $f_1,\dots,f_r\in R$ generating the unit ideal such that each localization $N_{f_i}$ [def-weil-pbc-module-localization-aw…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-affine-finite-projective-prime-membership: the existing statement concerns “Prime membership in a finite projective module is detected at the prime localization” (Let $R$ be a commutative ring, $N$ a finite projective $R$-module [def-weil-pbc-projective-module], $s\in N$, and $\mathfrak p\subset R$ a prime ideal. Put $S=R\setminus\mathfrak p$ and $N_{\mathfrak p}=S^{-1}N…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-affine-standard-cover-finite-free-local-fp-flat: the existing statement concerns “A finite free module is finitely presented and flat” (Let $A$ be a commutative ring and $P$ an $A$-module that is free [def-weil-pbc-free-module] with a finite basis. Then $P$ is finitely presented [def-sc-finitely-presented-module] and flat as an $A$-module [def-…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-graded-quotient-generic-ranks vs lem-sc-free-prime-membership: the existing statement concerns “Prime membership for a finite free module after localization” (Let $R$ be a commutative ring, $F=R^{n}$ a finite free $R$-module, $s=(s_1,\dots,s_n)\in F$, and $\mathfrak p\subset R$ a prime ideal. Put $S=R\setminus\mathfrak p$ and $F_{\mathfrak p}=S^{-1}F$ [def-weil-pbc-m…); it does not assert one generic localization after every prime quotient, controlling all graded component ranks and their fibre comparisons simultaneously.

lem-sfb-noetherian-generically-constant-finite-image vs lem-sfb-local-integral-perfect-model-cohomology: the existing statement concerns “Cohomology of a local integral perfect scalar model” (Let $\ell$ be prime and $E/\mathbf Q_\ell$ a finite extension, with valuation ring $R=\mathcal O_E$ and uniformizer $\pi$ [def-weil-l-adic-coefficient-extension]. Let $X$ and $S$ be schemes [def-pc-scheme] and …); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs def-sfb-affine-locally-constructible-proetale-modules: the existing statement concerns “Affine-local constructibility of pro-etale modules over discrete Noetherian rings” (Let $X$ be a scheme [def-pc-scheme] and $R$ a discrete commutative Noetherian ring [def-weil-pbc-noetherian-ring]. On the small pro-etale site of $X$ [def-weil-pbc-proetale-site], use the constant ring sheaf $\…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-sfb-graded-fibre-hilbert-functions-finite: the new statement is an arbitrary-set-valued function criterion with generic-constancy hypotheses, with no graded sheaf or coherence conclusion.

lem-sfb-noetherian-generically-constant-finite-image vs lem-sfb-proetale-fp-local-models-comparison: the existing statement concerns “Intrinsic finite local models and fixed coefficient local models” (Let X be a scheme and R a commutative Noetherian ring. For the intrinsic module category and finitely presented local models of [def-sfb-proetale-fp-local-models], form the equivalence E obtained by restricting…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-a1-local-spectrum-open-classification: the existing statement concerns “Open subsets of a one-dimensional Noetherian local spectrum” (Let $(A,\mathfrak m)$ be a Noetherian local commutative ring [def-weil-pbc-noetherian-ring] whose Krull dimension is at most one [def-weil-pbc-krull-dimension-ring], and let $S=\operatorname{Spec}(A)$ be its af…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-weil-pbc-krull-intersection-localization: the existing statement concerns “Intersection of the I-adic filtration of a finite module vanishes near V(I)” (Let $R$ be a Noetherian ring [def-weil-pbc-noetherian-ring], $I\subseteq R$ an ideal, $M$ a finitely generated $R$-module [def-weil-finitely-generated-module] and $N=\bigcap_{n\ge0}I^nM$. Then for every prime i…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-weil-pbc-popescu-reduce-to-field: the existing statement concerns “Popescu's theorem reduces to a field as base” (Assume that for every field $k$ and every Noetherian ring $\Lambda$ [def-weil-pbc-noetherian-ring] with a regular ring map $k\to\Lambda$ [def-weil-pbc-g-ring], $\Lambda$ is a filtered colimit of smooth $k$-alge…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs stage3-b4-bounded-finite-free-resolution: the existing statement concerns “Bounded finite free resolution construction” (Let R be a commutative Noetherian local ring [def-weil-pbc-noetherian-ring], M a finite R-module [def-weil-finitely-generated-module], and d a natural number. If M has a projective resolution of length at most …); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-weil-pbc-reduced-noetherian-total-ring-fractions: the existing statement concerns “The total ring of fractions of a reduced Noetherian ring is a finite product of fields” (Let $R$ be a reduced Noetherian ring [def-weil-pbc-noetherian-ring] (no nonzero nilpotent elements), let $\mathfrak q_1,\dots,\mathfrak q_t$ be its minimal prime ideals, pairwise distinct (finitely many, [lem-w…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-weil-pbc-noetherian-submodule-finite: the existing statement concerns “Submodules of a finite module over a Noetherian ring are finite” (Let $A$ be a Noetherian ring [def-weil-pbc-noetherian-ring] and $M$ a finitely generated $A$-module [def-weil-finitely-generated-module]. Then every $A$-submodule $N\subseteq M$ is a finitely generated $A$-modu…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-weil-pbc-finite-modules-noetherian-abelian: the existing statement concerns “Finite modules over a Noetherian ring form an abelian category” (Let $R$ be a Noetherian ring [def-weil-pbc-noetherian-ring] and $\mathrm{Mod}^{fg}_R$ the category of finitely generated $R$-modules [def-weil-finitely-generated-module] and $R$-linear maps (with the pointwise …); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-weil-pbc-noetherian-finite-module-acc: the existing statement concerns “Ascending chain and maximal condition for submodules of a finite module over a Noetherian ring” (Let $A$ be a Noetherian ring [def-weil-pbc-noetherian-ring] and $M$ a finitely generated $A$-module [def-weil-finitely-generated-module]. Then (1) every increasing sequence $N_1\subseteq N_2\subseteq\dots$ of $…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-weil-pbc-noetherian-finitely-many-minimal-primes: the existing statement concerns “A Noetherian ring has finitely many minimal primes” (Let $R$ be a Noetherian ring [def-weil-pbc-noetherian-ring]. Then $R$ has only finitely many minimal prime ideals (prime ideals $\mathfrak q\subset R$ containing no strictly smaller prime ideal); equivalently $…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.

lem-sfb-noetherian-generically-constant-finite-image vs lem-sc-finite-minimal-primes-over-ideal: the existing statement concerns “Finitely many minimal primes over an ideal in a Noetherian ring” (Let $R$ be a Noetherian commutative ring [def-weil-pbc-noetherian-ring] and let $I \subseteq R$ be an ideal. The set of prime ideals of $R$ that are minimal among those containing $I$ is finite.…); it does not assert finite image of an arbitrary set-valued function from generic constancy on each prime closed subset.


## Validation

Current retry: the required initial dry run passed on 2026-10-23 at 7c231a70713. After the explicit finite-dimension revision, a fresh final dry run is required before push. The earlier validation history below is retained.

The initial resumed dry run exited 1, nothing pushed: unchanged node, old 5867-character proof, no new nodes. This was repaired by honoring the released repair order. A preliminary server review_split now passes. Full dry run and delivery results are recorded below when they finish.


## Complete retained arguments and allocation

The new nodes are statement-only. Their intended arguments are retained here verbatim from the live split, including the parts now elementary in the assembly.

### Former step 1

Work locally where $\mathcal B_1$ has finite generators $x_1,\ldots,x_r$ and $L$ has homogeneous generators $e_1,\ldots,e_t$ of degrees $b_1,\ldots,b_t$. For each $d$, $L_d$ is generated as a sheaf by the finite list $x_1^{\alpha_1}\cdots x_r^{\alpha_r}e_j$ with $\sum\alpha_i=d-b_j\geq0$: take the degree-$d$ component of a local expression in the $e_j$, and expand its homogeneous coefficients using the degree-one generators. There are finitely many such monomials for each fixed $d$. Hence $L_d$ is of finite type and, by its assumed quasi-coherence and the locally Noetherian hypothesis, is coherent. This works also when the generating lists are empty or some $b_j>d$.

Uses: pqf-def-coherent, pqf-lem-coherent-ft-locnoeth.

### Former step 2

Refine the neighbourhoods of step 1 to affine opens $U=\operatorname{Spec}A$ with $A$ Noetherian, and choose finitely many covering $S$ by quasi-compactness. On one such $U$ put $C=\bigoplus_d\mathcal B_d(U)$ and $M=\bigoplus_d L_d(U)$, with multiplication and action induced by the sheaf operations. Apply affine free evaluation to the identity morphism of $U$: a finite list of sections generating a quasi-coherent sheaf gives a surjection on sections. Applied degree by degree to the monomials in the $x_i$, and to the monomials times $e_j$, this shows that $C$ is generated as an $A$-algebra by $x_1,\ldots,x_r$, that $M$ is generated over $C$ by $e_1,\ldots,e_t$, and that every $M_d=L_d(U)$ is finite over $A$. The germ-localization statement identifies the function in the question on $U$ with $d\mapsto\dim_{\kappa(\mathfrak p)}(M_d\otimes_A\kappa(\mathfrak p))$. Indeed its stalk is $(M_d)_{\mathfrak p}$, and $(M_d)_{\mathfrak p}\otimes_{A_{\mathfrak p}}\kappa(\mathfrak p)=M_d\otimes_A\kappa(\mathfrak p)$ by the fraction formula $m/u\otimes z\mapsto m\otimes u^{-1}z$.

Uses: pqf-def-locnoeth, def-weil-pbc-quasi-compact-scheme, lem-weil-pbc-affine-pushforward-free-evaluation, lem-sbc-affine-module-germ-localization.

### Former step 3

Fix the affine data $A,C,M$ from step 2. For an ideal $I\subseteq A$, let $P(I)$ assert that only finitely many functions $d\mapsto\dim_{\kappa(\mathfrak p)}(M_d\otimes_A\kappa(\mathfrak p))$ occur at primes $\mathfrak p\supseteq I$. If some $P(I)$ fails, choose a maximal such ideal $I$ using the maximal-submodule assertion for the finite $A$-module $A$. Thus $P(J)$ holds for every $J\supsetneq I$, and $I\ne A$ since $V(A)$ is empty. The quotient $A/I$ is Noetherian: every ideal is the image of an ideal of $A$ and the images of finite generators generate it. It has finitely many minimal primes. If $I$ is not prime, the inverse images $\mathfrak q_1,\ldots,\mathfrak q_v$ of these primes all strictly contain $I$, and their closed sets cover $V(I)$, by the irreducible-component formulation of that same result. The finite union of their finite sets of functions proves $P(I)$, a contradiction. Therefore a maximal counterexample $I$ is prime.

Uses: lem-weil-pbc-noetherian-finite-module-acc, lem-weil-pbc-noetherian-finitely-many-minimal-primes.

### Former step 4

For this prime $I$ put $R=A/I$, $D=C\otimes_A R$ and $N=M\otimes_A R=\bigoplus_d(M_d\otimes_A R)$. The tensor/direct-sum identity sends $(m_d)_d\otimes r$ to $(m_d\otimes r)_d$ and its inverse adds the finitely many components. The images of the fixed generators show that $D$ is a finite type $R$-algebra and $N$ a finite $D$-module. The ring $R$ is a Noetherian domain. Generic freeness therefore gives a single $0\ne a\in R$ such that the whole module $N_a$ is free over $R_a$, with no assertion that this free module has finite rank. Localization in the degree-zero element $a$ preserves the grading, so every $(N_d)_a$ is an $R_a$-linear direct summand of $N_a$.

Uses: lem-pur-noetherian-algebra-module-generic-freeness.

### Former step 5

Each $(N_d)_a$ is finite over $R_a$, since the images of the finite generators of $M_d$ still generate it. It is in fact a direct summand of a finite free module: under a chosen basis $N_a\cong\bigoplus_{\lambda\in T}R_a$, the images of finitely many generators of $(N_d)_a$ have support in a finite subset $T_d\subset T$. Its inclusion factors through $R_a^{T_d}$, and the degree-$d$ projection restricted to this finite free module is a retraction. Thus $(N_d)_a$ is finite projective in the direct-summand sense. Apply the finite-projective rank statement: its stalks are finite free and their ranks are locally constant on $\operatorname{Spec}R_a$. Their residue-field dimensions equal those ranks, since a basis of the free stalk tensors to a basis over its residue field. As $R_a$ is a domain, every nonempty basic open contains its zero prime; consequently the locally constant rank at any prime equals the rank at the zero prime. For every $d$, the fibre dimension is therefore constant on all of $\operatorname{Spec}R_a$. There is one whole function $h_\eta$ on this open, not merely finitely many possible values separately in each degree.

Uses: def-weil-pbc-projective-module, lem-weil-pbc-finite-projective-rank-locally-constant.

### Former step 6

Choose a lift $\widetilde a\in A$ of $a$. The complement in $V(I)$ of $\operatorname{Spec}R_a$ is $V(I+(\widetilde a))$, and $I+(\widetilde a)\supsetneq I$ because $a\ne0$. By maximality of the counterexample, only finitely many functions occur on this complement. At a prime $\mathfrak p\supseteq I$, quotienting by $I$ does not change its residue field or the fibres: $(M_d\otimes_A R)\otimes_R\kappa(\mathfrak p)\cong M_d\otimes_A\kappa(\mathfrak p)$ via $(m\otimes\bar b)\otimes z\mapsto m\otimes bz$, with inverse $m\otimes z\mapsto(m\otimes1)\otimes z$; on the open, localizing at $a$ has the same property because $a$ becomes invertible in the residue field. Hence adjoining $h_\eta$ to the finite set from the complement proves $P(I)$, a contradiction. No counterexample exists, so $P(0)$ holds for the original affine chart.

Uses: .

### Former step 7

For each of the finitely many affine charts of step 2 take the finite set of functions just obtained, and let $H$ be their union. Every point belongs to one chart, and its function there is the function in the question by the stalk comparison in step 2. Thus $H\subseteq\mathbf N^{\mathbf N}$ is finite and contains every $h_s$. Each value is a natural number because each $M_d$ is finite over its coordinate ring. If $S$ is empty, take the empty cover and $H=\varnothing$; coherence of the pieces is then vacuous.

Uses: .


## Historical retained report (superseded diagnosis)

# Stage-1 repair: superseded assignment

1. Files written: the sandbox item JSON restores Q47's live `lean` record, including
   `existing: false`, its module-owning `file`, original statement, author and date;
   restores the live `lean_audit` metadata; and is semantically identical to the
   current live item. `citations.json` records all 11 step/node citations verbatim.
   No new nodes or Mathlib leaves. No stage-1 mathematical change is proposed.
2. Attachments: none. The existing Sheaf theorem ends in `sorry`; it is a stage-2
   statement, not a finished proof. A search of lean/WeilConjectures for the item
   tag and graded-fibre-Hilbert declaration names found no attachment.
3. WANTED: none.
4. The returned attempt used the stage-2 lane's report and rebound Q47's existing
   module through a stage-1 delivery. The current live node already has Q60's
   reviewed stage-1 split and Q47's reviewed stage-2 statement. Both reviews pass.
   The mathematical fields in the retained sandbox already match the live node.
5. There is no remaining stage-1 split to deliver. The standing brief says live
   split-and-reviewed nodes win and must not be split again. The historical
   report below is retained for its searches and inspections, not resubmitted as
   a current stage-2 claim. No source, module, launcher or repository was edited.

## Review by Q54

I compared every JSON field in the retained item with the current live node.
The only differences were the unauthorized lean rebind and omitted lean_audit.
I restored both from live, preserving the complete proof, citations, recorded
Mathlib searches, blueprint references, source information and both reviews.
This addresses A2/A7 and H1/H2 without taking ownership of Q47's module. The
maintainer's return explicitly says the split was superseded and requests no
mathematical fixes; I do not manufacture a new split or claim Q60's work.

I nevertheless read all seven existing proof steps, every statement they cite,
and Stacks 0ASY (more-morphisms.tex, lemma-generic-flatness-stratification),
00K0 (algebra.tex, lemma-graded-module-fg), 051R (algebra.tex,
lemma-generic-flatness-Noetherian), 00NX (algebra.tex, lemma-finite-projective),
01XZ (coherent.tex, lemma-coherent-Noetherian) and 01HV/01IB (schemes.tex).
There are no new nodes needing a separate source or new Mathlib searches.

Step 1 uses pqf-def-coherent and pqf-lem-coherent-ft-locnoeth: finite monomials
in degree-one algebra generators times arbitrary-degree module generators give
finite type in each degree, and the cited equivalence supplies coherence under
the assumed quasi-coherence and local Noetherianity. Step 2 uses pqf-def-locnoeth
and def-weil-pbc-quasi-compact-scheme to choose finitely many suitable affine
charts; affine-pushforward-free-evaluation applies to the identity affine map
and each quasi-coherent piece to turn the finite sheaf generating list into a
surjection on sections. affine-module-germ-localization states the actual
localization of those sections at the relevant prime, which gives the fibres
used in the affine reduction. The fraction maps are written in the step.

Step 3 uses the maximal-element clause of noetherian-finite-module-acc for the
finite module A and noetherian-finitely-many-minimal-primes for A/I. Both
hypotheses hold; a non-prime I is strictly contained in every minimal prime
over it, so maximality controls each member of the finite closed cover. Step 4
uses noetherian-algebra-module-generic-freeness exactly with the Noetherian
domain A/I, finite-type algebra D, and finite D-module N. It gives one nonzero
element freeing the whole module; no finite rank of that whole module is used.

Step 5 uses projective-module's direct-summand characterization and
finite-projective-rank-locally-constant. The explicit finite-support retraction
makes each homogeneous piece a summand of a finite free module, so the rank
statement applies. A locally constant rank on the spectrum of a domain is
constant because every nonempty basic open contains the zero prime. The one
localization from step 4 works for every degree. Steps 6 and 7 cite no nodes:
the quotient/localization fibre maps are written with inverse formulas; the
strictly larger ideal falls under the maximal-counterexample hypothesis; the
last step takes the finite union over the chosen affine cover. Each cited
statement was read directly, and citations.json uses its entire statement as
a verbatim quote, not a paraphrase or a claim extracted from its proof.

Small cases checked: empty scheme gives the empty cover and empty H; L=0 and
empty generator lists give the zero function; generators above d contribute no
monomials; B1=0 makes the positive algebra degrees zero. Nonreduced bases are
allowed because the prime-counterexample quotient is used only within the
induction. For (k[t]/t)[x] over k[t], the zero and constant-one fibre functions
both occur, as permitted by finite H. No separatedness or flatness hypothesis
is introduced. No step exceeds 2000 characters (maximum 1149); no hidden long
step or new lemma was introduced. B--E were checked against these existing
steps; the repair changes no mathematical statement or dependency.

Validation: the initial required dry run exited 1 because this section was
missing. After repairing the report and restoring live ownership, the second
required dry run completed and exited 1 with PREFLIGHT FAILED, nothing pushed:

1. the item's node file is unchanged;
2. re-split: proof is 5867 characters and must be at most 3000;
3. re-split: at least one new node is required (none added).

The unchanged item is intentional: Q60's reviewed split is already live and
must win under the standing brief. The latter two gates demand another split
of that reviewed work, while the maintainer's return explicitly says this was
a superseded S1 delivery, contains no mathematical fixes, and should have been
skipped by the dispatcher. I cannot satisfy these gates without changing an
already reviewed split solely to manufacture stage-1 content. The dispatcher
or maintainer must clear/reconcile this obsolete assignment and re-split gate.
The tool was not patched or bypassed, and no push was attempted. Both dry-run
processes exited; none is left running. Outcome: BLOCKED by conflicting
stage-1 preflight requirements on a superseded assignment.

## Repair retry verification — 2026-10-22

This retry reread the maintainer's complete return and the stage-1 standing
brief, then compared the retained sandbox item with the current shared live
item field by field. There are no differing JSON fields. In particular, Q47's
`lean.existing: false`, `lean.file`, declaration list, author and date remain
intact. Q60's stage-1 `reviewed.result: pass` and Q47's stage-2
`reviewed_lean.result: pass`, both dated 2026-10-22, are preserved. The return's
A2/A7/H1/H2 ownership and lane faults therefore have already been removed;
there is no remaining item delta to merge. No node or Lean file was edited in
this retry.

I repeated the attachment check in the authorized read clone: the item tag,
`graded_fibre_hilbert_functions_finite` and `gradedFibreHilbertFunction` have no
hits under `lean/WeilConjectures`. The recorded declaration is under
`lean/Sheaf/AlgebraicGeometry/GradedFibreHilbertFunctionsFinite.lean:105`; its
proof at line 117 is `sorry`. Thus neither a finished proof nor an ATTACH
answer is justified. The prior mathematical review and search records above
are retained as prior work, not claimed as fresh searches in this retry.

The required first dry run of this retry was run exactly as prescribed:
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q54 lem-sfb-graded-fibre-hilbert-functions-finite --no-push`.
It completed with exit code 1 and `PREFLIGHT FAILED, nothing pushed`:

1. the item's node file is unchanged;
2. the re-split gate counts 5867 proof characters and requires at most 3000;
3. that gate requires at least one new node; this delivery adds zero.

The return explicitly calls the earlier delivery superseded, says "No fixes",
and asks that stage 1 skip items whose stage-2 binding has already landed with
a reviewed pass. The standing stage-1 brief also says live split-and-reviewed
nodes win and must never be split. Producing a new split solely to pass these
three gates would conflict with those instructions. This is a superseded-item
routing/preflight conflict, not an unresolved mathematical split or a reason
to overwrite Q47's binding. The dispatcher or maintainer must reconcile the
assignment and re-split gate. No push was attempted; the only dry-run process
exited, and no delivery invocation remains active. No launcher or repository
file was edited, and no compiler or build was run.

## Historical report from the returned attempt (retained, superseded)

## Worker report

Exact existing declaration: `AlgebraicGeometry.graded_fibre_hilbert_functions_finite`
in `Sheaf.AlgebraicGeometry.GradedFibreHilbertFunctionsFinite`, live source
`lean/Sheaf/AlgebraicGeometry/GradedFibreHilbertFunctionsFinite.lean:105`.
The helper `AlgebraicGeometry.gradedFibreHilbertFunction` is defined at line 52.
Both the shared source and `scompile.py --source` on the server contain the same
statement. No duplicate module is written, as required by brief-stage2 §1.
Only the item's `lean` record changes; the statement and dependencies are unchanged.

Assignment overlap: `coord/ledger.md:24888` records the stage-2 merge of
`deliver/Q47/lem-sfb-graded-fibre-hilbert-functions-finite` at 05:06 UTC today.
`coord/deliveries.log:49490` records landing 20261022T050637-Q47-2958025-102,
commit 3dae427af7. Its existing `reviewed_lean` is a pass. There is no repair note
for this item. This report does not claim to have written or proved that module.

Hypothesis and clause correspondence, read against the complete signatures and
source docstrings:

- `S : Scheme.{u}` and `[IsNoetherian S]` say precisely quasi-compact and
  locally Noetherian: Mathlib's class extends `IsLocallyNoetherian` and
  `CompactSpace`. No separatedness, nonemptiness or reducedness is assumed.
- `B L : ℕ → S.Modules` gives all nonnegative homogeneous pieces.
  `A : GradedSheafAlgebra B` is the recorded restriction-compatible commutative,
  unital, bilinear multiplication. `M : GradedSheafModule A L` is its
  associative unital homogeneous action. These are the existing dependency
  structures, not private copies.
- `hB : ∀ d, SheafOfModules.IsQuasicoherent.{u} (B d)` expresses
  quasi-coherence of the graded algebra via its pieces. A direct sum of
  quasi-coherent modules is quasi-coherent, and its summands are quasi-coherent.
- `hzero : IsIso A.unit` identifies degree zero with the structure sheaf via
  the given structural unit.
- `hone : RingedSpace.IsCoherent S.toRingedSpace (B 1)` is exactly coherent
  degree one, using the Stacks finite-type and finite-type-kernels definition.
- `hgen : A.IsGeneratedInDegreeOne` is the existing sheaf-local span condition
  for products of degree one and degree n. Together with `hzero`, it means
  generation by degree one.
- `hL : ∀ d, SheafOfModules.IsQuasicoherent.{u} (L d)` gives the assumed
  quasi-coherent module pieces.
- `hM : M.IsLocallyFinitelyGenerated` chooses, near each point, a finite family
  of degrees `Fin t → ℕ` and homogeneous sections in those degrees. Its local
  span criterion allows every nonnegative generator degree, arbitrary shifts,
  and `t = 0`; it does not impose surjectivity on sections of every open.
- The first conclusion `∀ d, RingedSpace.IsCoherent S.toRingedSpace (L d)`
  asserts coherence in every degree, including zero.
- `gradedFibreHilbertFunction L s d` is `Module.finrank (S.residueField s)` of
  `κ(s) ⊗[S.presheaf.stalk s] ((RingedSpace.moduleStalkFunctor
  S.toRingedSpace s).obj (L d))`, with the algebra induced by `(S.residue s)`.
  These are the actual stalk and quotient residue field. The tensor commutor
  identifies this extension-of-scalars order with the node's displayed order.
  Coherence implies finite-dimensional fibres, so `finrank` is the ordinary
  natural-number dimension, not its infinite-dimensional default.
- `∃ H : Set (ℕ → ℕ), H.Finite ∧ (∀ s, gradedFibreHilbertFunction L s ∈ H)`
  gives one finite set of whole functions, simultaneously in every degree.
- `IsEmpty S → H = ∅` expressly permits the empty scheme and chooses its
  empty set of functions.

Dependency declarations inspected in their complete source:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, with no separation axiom.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`:
  `GradedSheafAlgebra` and `GradedSheafModule` (bilinearity, restriction,
  associativity, commutativity and units).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`, the dependency's recorded
  quasi-coherent finite-type conjunction. The coherent clause itself uses the
  same node's full Stacks notion supplied by
  `WeilConjectures.AlgebraicGeometry.Coherent`, `RingedSpace.IsCoherent`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.residue`, `Scheme.Hom.residueFieldMap`.
- `Sheaf.AlgebraicGeometry.GradedSheafGeneration`:
  `GradedSheafAlgebra.IsGeneratedInDegreeOne`,
  `GradedSheafModule.IsLocallyFinitelyGenerated`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`, taking the actual additive stalk with its
  stalk-ring module action.

Source read: Stacks `more-morphisms.tex`, label
`lemma-generic-flatness-stratification` (0ASY), statement and proof, and
`algebra.tex`, `lemma-graded-module-fg` (00K0), statement and monomial proof.
The existing module's docstring spells out all seven DAG proof steps, including
simultaneous generic freeness and the finite-support retract argument; its only
postponed theorem is the named main theorem. The helper definition has real data.

Edge cases checked: empty scheme (all pointwise conditions vacuous, H empty);
zero module and empty homogeneous generator family (zero function); degree-zero
pieces; generators above the tested degree (no monomials from those generators);
B_1 zero; positive shifts of B; nonreduced bases; arbitrary characteristic.
Over Spec k[t], the module (k[t]/t)[x] gives different functions at t=0 and
away from t=0, which the finite-set conclusion permits. No flatness hypothesis
or degree-zero generator restriction has been added.

Searches actually run for Q54 with the prescribed msearch.py:

- leanfinder: "A finite graded module over a standard graded algebra on a
  Noetherian scheme has finitely many fibre Hilbert functions". Eight hits on
  Rees algebras, graded finite type and associated primes; no exact Mathlib match.
- loogle: "Module.finrank, Set.Finite". Nine span/affine-span dimension results;
  none is this graded-sheaf theorem.
- grep: "hilbertFunction|HilbertFunction|graded_fibre_hilbert". Zero wrapper hits.
- leansearch: "Only finitely many whole fibre Hilbert functions occur for a
  finite graded sheaf module over a Noetherian scheme". Eight hits on finite
  scheme fibres and module generators, not the requested theorem.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item ID and declaration names found the
  exact existing Sheaf declaration. The upstream `Scheme.Hom.hilbertFunction`
  computes Euler characteristics of tensor powers, which is a different notion.

No new node, dependency module, statement correction or disputed statement.
An existing attachment has no new file requiring compilation; the prescribed
server source reader confirmed the current published declaration. Delivery
validation: `deliver2.py --no-push` passed the server preflight and both
sandbox/library attachment checks, printing `OK (dry run): commit 72ff3a251a6
passes the preflight and compiles; nothing pushed`. No Lean module is added.

## Second reading by Q54

No second worker was started: the dispatcher brief expressly forbids starting
other agents and assigns independent review to the maintainer. The clause-by-clause
reading above is the worker's own inspection, not a claimed independent review.

## Rebase validation

The initial resumed dry run exited successfully at 5e4fe6d7c1b before the above repair edits. All four citation quotes were checked against the current statement text. The final dry run and push are performed after these edits; the tool output is the authoritative result. No Lean, compiler, repository file or launcher file was written.
