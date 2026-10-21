# Worker report

1. Files written:
   - dag/nodes/sec-six-functors-basics/det-def-sfb-filtered-two-colimit-model.json: existing definition, unchanged statement; four assembly steps, 2109 characters in their text.
   - dag/nodes/sec-six-functors-basics/lem-sfb-coherent-hom-transition-laws.json: statement, unsplit; no exact Mathlib match. Extracts the endpoint cocycle/naturality calculation and the product/identity cancellation.
   - dag/nodes/sec-six-functors-basics/lem-sfb-directed-hom-quotient-composition.json: statement, unsplit; no exact Mathlib match. Extracts upper-bound independence, descent in both variables and all category laws in an abstract partial Hom system.
   - dag/nodes/sec-six-functors-basics/lem-sfb-coherent-cocone-evaluation-invariant.json: statement, unsplit; no exact Mathlib match. Extracts the two endpoint compatibility identities, transition invariance and stagewise identity/product formulas.
   - citations.json: verbatim excerpts for each of the five node citations in the four assembly steps.
   - report.md; research/ retains the original item and proof, complete search outputs and the small-case orientation check. searches.jsonl was written only by msearch.py.
2. Attachments: none. A search of lean/WeilConjectures for the exact blueprint tag and the notions found no declaration there giving this concrete normalized model. Its FilteredTwoColimit.lean records cocone data and finite-stage conditions, not the model construction. The complete existing Sheaf.CategoryTheory.FilteredTwoColimitModel file was read; it is left untouched. The explicit human decision of 2026-10-21 requests this stage-1 re-split of an already stated/reviewed node. The extracted abstract quotient lemma is not exactly its concrete category declaration.
3. WANTED: none.
4. What was wrong: the old proof concentrated seven arguments in the item, preventing independent work. No mathematical statement error was found. The original statement, statement dependencies, original Mathlib search records, import/blueprint metadata, and Lean records are preserved. This delivery changes the proof decomposition only; it does not infer that its old review approves the new split.
5. Unfinished: the three new nodes intentionally have proof=[], proof_deps=[], proof_origin=null and status=unsplit. They are separate stage-1 work items, as the human requested. No Lean file was written and no compiler, Lake or build command was run.

## Source and route

I read GOAL.md, the stage-1 brief and stage document, SETUP.md's three-level rule, the worker role, the open-stage notice, the chapter and unit records, and delivery-errors.md B–E. The current source is main-20261015, sec-six-functors-basics/sk-def-sfb-filtered-two-colimit: both the model statement and its proof were read in full. The unit's second proof paragraph explicitly prescribes pair objects, common-stage Hom colimits and comparison; this decomposition stays inside that route. The item is not the unit's key statement, so no unit realization record is edited.

All three new lemmas are agent-formulated intermediate statements extracted from the model proof. Their source fields identify the exact paragraph and calculation, rather than claiming an unrelated Stacks theorem. For the set-colimit portion I read literature/stacks-project/categories.tex, Section Tag 04AX (section-directed-colimits), especially the coproduct quotient and eventual equality formula after Definition 002V. The universal property is Definition 002F, already represented by def-weil-pbc-category-colimit. No SGA source is used.

## Searches and Mathlib verdicts

The sandbox was initially empty of node files and had no searches.jsonl; no prior attempt was discarded. Before creating nodes I searched the whole DAG by Hom-transition/composition/evaluation names, statement concepts and category-colimit titles, and ran tools/blueprint_refs.py ancestor and searches for homTransition, coherent, quotient and conjugation (also literal narrower phrases). The coherent and quotient results are retained in research/. I opened the relevant neighboring statements, including the strict filtered-category colimit results, the categorical quotient result, normalization, and the comparison characterization; none states an extracted lemma.

For each proposed id, msearch.py actually ran leanfinder, loogle, grep and leansearch. Every service answered successfully; all twelve query records remain in searches.jsonl, and the nodes record the exact queries and complete returned hits. LeanFinder and LeanSearch used distinct phrasings. The item already has the extensive earlier searches, which are retained rather than rerun with the same question.

For the transition lemma the closest results were Pseudofunctor.mapComp'_naturality_1/_2 and mapId' naturality, plus DirectedSystem.mk. I read Mathlib/CategoryTheory/Bicategory/Functor/Cat.lean. They give naturality or package already proved transition laws, not the endpoint cocycle calculation for the explicitly given T and tau. This is not a one-line specialization of a complete matching declaration.

For quotient composition the hits included Ind, DirectLimit.instMul/instMonoid and CategoryTheory.Quotient.comp. I inspected the Ind category documentation, Mathlib/CategoryTheory/Quotient.lean and Limits/Types/ColimitType.lean and ColimitTypeFiltered.lean. Ind is a presheaf subcategory, DirectLimit's operation is total on one type per stage, and Quotient.comp begins with a category on representatives. Here representatives carry varying stages and only a common-stage partial Hom product is given. Proving independence of that stage is precisely the missing intermediate argument. The general filtered-set equality result is reused from the existing Mathlib leaf.

For evaluation the pseudofunctor compositor hits and Cocone.w/CoconeMorphism.w give ordinary naturality, not the theta/tau endpoint cancellation in the statement. The new statement supplies that cancellation for raw cocone data, without requiring a pre-existing Hom functor or a comparison functor. It also states its same-stage product and unit equations, so the parent uses the statement rather than its future proof.

## Not duplicates

lem-sfb-coherent-hom-transition-laws vs det-def-sfb-filtered-two-colimit-model: the new lemma is a calculation on raw T/tau data, requires no directedness or vertex, and constructs no colimit category or comparison functor; the model is their later assembly. This extraction is explicitly required by the human re-split.
lem-sfb-directed-hom-quotient-composition vs det-def-sfb-filtered-two-colimit-model: the new lemma assumes abstract partial Hom products and their transition laws, and proves quotient descent/category laws; it does not prove those laws from coherence or construct a cocone comparison. It is only the middle argument of the model.
lem-sfb-coherent-cocone-evaluation-invariant vs det-def-sfb-filtered-two-colimit-model: the new lemma gives stagewise endpoint identities and invariant evaluation without directedness, quotient Hom sets, category structure or a comparison functor; the parent descends it to its category.
lem-sfb-directed-hom-quotient-composition vs lem-weil-pbc-filtered-colimit-categories: the existing result assumes a strict functorial system of categories and quotients both object and arrow sets; the new lemma fixes the label objects and allows only partially defined stage Hom products. Turning these data into the existing result and identifying its arrow fiber with the prescribed quotient would require another construction/comparison, not a one-line specialization.
lem-sfb-directed-hom-quotient-composition vs lem-weil-pbc-filtered-colimit-category-structure: the same distinction applies: the existing theorem's objects are a strict object colimit, whereas new O retains all label objects and supplies representative/common-stage formulas.
lem-sfb-directed-hom-quotient-composition vs lem-coef-category-quotient-relations: the existing result assumes a category before taking its quotient; here no composition on the differently staged representatives is given, so the upper-bound argument must precede category laws.
lem-sfb-coherent-cocone-evaluation-invariant vs lem-weil-pbc-coherent-cocone-normalization: normalization changes transitions by beta and compares finite-stage conditions; this lemma holds for a fixed cocone and evaluates its transitions, with no replacement/normalization assertion.
lem-sfb-coherent-hom-transition-laws vs det-def-sfb-filtered-two-colimit-characterization: characterization assumes the model already exists and identifies equivalence conditions; it does not prove transition coherence, and citing it would be circular.
lem-sfb-coherent-cocone-evaluation-invariant vs det-def-sfb-filtered-two-colimit-characterization: the characterization assumes the already constructed comparison functor and cannot supply its well-definedness.

No new lemma is assigned a Stacks tag claiming it is the tagged theorem. The existing two Tag 04AX/002F leaves are reused. No new duplicate of either set-colimit leaf is created.

## Review by ND

I checked the source statement against the item clause by clause: I is a preorder, not necessarily antisymmetric; the normalization equations and orientation of tau/theta match; objects are pairs, not an object colimit; each Hom index is the set of common upper stages; products are h after g; the comparison has theta on the target and inverse theta on the source. There is no added faithfulness or full-surjectivity hypothesis. No target statement or definition was changed.

Step 1 cites lem-sfb-coherent-hom-transition-laws. Its statement explicitly supplies both transition identity and composition laws, and also the product/identity equations needed in step 3. I checked the pentagon identity at both endpoints: A_(a;n,p) T_np(A_(a;k,n)) = A_(a;k,p) tau_(knp,T_ik x), and the inverse equation at the source. Naturality of tau_knp cancels the middle expression. The common-stage index is a set; a bound of two common stages remains above i and j. Thinness supplies parallel-arrow equalization. Thus the small and filtered hypotheses in the next step are actually verified, even for a non-antisymmetric preorder.

Step 2 cites the statements of def-weil-pbc-category-colimit and lem-weil-pbc-filtered-colimit-sets-elementwise, both opened in full. The former states the precise universal factorization property; the elementary quotient argument proves existence here, rather than treating a definition as an existence theorem. The latter states representative surjectivity and eventual equality for a small filtered category, exactly the properties used. The index was verified in step 1, and a common universe or ULift prevents a hidden universe restriction. This is the same explicit quotient/ULift universal-property argument of the old proof; it is short enough to remain elementary assembly.

Step 3 cites lem-sfb-directed-hom-quotient-composition. Its statement covers arbitrary differing representative stages, independence under changing the upper stage, compatibility in each quotient input, associativity and both units. I checked every hypothesis in the substitution: labels are all pairs (i,x), r is the index, H_k is the stage Hom set, mu_k is the category product, and e_(a,k) is the identity of T_ik x. Step 1 supplies transport functoriality and product/unit preservation. Normalization T_ii=Id identifies the chosen unit at r(a) with the item's [i,id_x]. The new lemma assumes stage associativity and units but does not assume that representatives form a category: this avoids concealing the upper-bound argument in an input hypothesis.

Step 4 cites lem-sfb-coherent-cocone-evaluation-invariant. Its statement explicitly contains P_n(t_kn g)=P_k(g), the endpoint theta identities, and stagewise product/identity equations. I checked its compatibility hypothesis is precisely the item's compatibility equation and uses the actual natural isomorphisms from the cocone definition, with no assertion taken from that definition beyond its data. Inverting the source endpoint equation and substituting the target one gives cancellation of Phi_n(tau) with its inverse, followed by naturality of theta_kn. Hence quotient elimination legitimately gives the Hom map. The category law from step 3 computes a pair at one common stage; the lemma's same-stage product equation then proves the functor law. This uses the cited statement, not a hidden construction in its proof.

I tested the new assertions on the terminal index/category (all formulas reduce to ordinary composition and the vertex functor), empty O (the abstract quotient lemma yields the empty category), empty off-diagonal H (no nonexistent representative is required), and repeated stages/equivalent indices in a preorder (no antisymmetry is used). The presence of labels in the model supplies actual indices whenever an argument needs them. For a noncommutative orientation check, research/check_small_cases.py uses S3 on four stages with nontrivial inner transition functors: T_ij=conj(b_ij), tau_ijk=b_ik (b_jk b_ij)^(-1), and theta_ij=b_ij^(-1). All 11454 checks of transition identity/composition, transported products and evaluation invariance/product equations passed. This finite check is evidence for the order of factors, not a proof replacing the displayed calculation.

Against delivery-errors B–E: all new objects and hypotheses are introduced in their statements; no proof is written inside a new node; searches are real and retained; no new node is a bare definition/theorem citation or a restatement of the whole item. None depends on the model node or its characterization, so the extraction is acyclic. I checked each citation against its statement and copied literal substrings into citations.json. All three stages of the original proof are represented below. Each assembly step is below 2000 characters and the entire text is below 3000; the non-elementary coherence, quotient descent and evaluation calculations now have three independently claimable nodes. No correction to the mathematical source was needed. The first dry run required an explicit notion citation in the transition lemma; I opened def-nagata-category and added its category definition as a statement dependency. Its statement supplies exactly the Hom, identity and composition notion used, and no mathematical hypothesis changed.

## Coverage of the old proof

| Old step | New location |
|---|---|
| 1: filtered common-stage index; endpoint cocycle and naturality for t | Index argument remains assembly step 1; all transition equations are in lem-sfb-coherent-hom-transition-laws. |
| 2: actual quotient colimit, lifted cocone universal property and common-stage equality | Assembly step 2, with the two existing Mathlib leaves; quotient elimination and uniqueness remain explicit. |
| 3: transition products and identities | Last two equations of lem-sfb-coherent-hom-transition-laws. |
| 4: compAt_transition, independence of upper stage and descent in both variables | Explicit conclusions of lem-sfb-directed-hom-quotient-composition. |
| 5: common-stage associativity and normalized two-sided units | Last paragraph of lem-sfb-directed-hom-quotient-composition; normalization substitution in assembly step 3. |
| 6: endpoint theta compatibility, cancellation and naturality, quotient descent | Explicit endpoint/intermediate identities in lem-sfb-coherent-cocone-evaluation-invariant; quotient elimination in assembly step 4. |
| 7: vertex object assignment, identity and composition equations | Last equations of lem-sfb-coherent-cocone-evaluation-invariant; object assignment and common-stage application in assembly step 4. |

The old proof is reproduced verbatim below to preserve every calculation and the earlier formalization notes. The new nodes are deliberately statement-only: their assigned future workers must supply these arguments, not merely cite this report as a proof.

### Original step 1

For fixed $a=(i,x)$ and $b=(j,y)$ write $J_{ab}=\{k\in I:i\le k,\ j\le k\}$. This is a set, is nonempty by directedness, and any two of its elements have an upper bound still in $J_{ab}$. Its category has at most one arrow between any two objects, so parallel arrows are already equal. Thus it is a small filtered category. For $k\le n\le p$, put $A_{a;k,n}=\tau_{ikn,x}$ and $A_{b;k,n}=\tau_{jkn,y}$. The cocycle axiom says
$$A_{b;n,p}T_{np}(A_{b;k,n})=A_{b;k,p}\tau_{knp,T_{jk}y},$$
with the analogous identity for $a$. Consequently
$$t_{np}(t_{kn}(g))=A_{b;k,p}\tau_{knp,T_{jk}y}\,T_{np}T_{kn}(g)\,\tau_{knp,T_{ik}x}^{-1}A_{a;k,p}^{-1}=A_{b;k,p}T_{kp}(g)A_{a;k,p}^{-1}=t_{kp}(g),$$
where the middle equality is naturality of $\tau_{knp}$. Normalization gives $t_{kk}(g)=g$. Hence the displayed Hom sets and transition maps form a diagram of sets indexed by $J_{ab}$.

### Original step 2

For fixed objects use Mathlib Functor.ColimitType for the Hom diagram, the quotient of the sigma type by the generating transition relation. Functor.ιColimitType_map proves compatibility of the classes. For any cocone on the ULift-valued diagram, descend the map (k,g) ↦ ι_k(ULift.up g) by Quot.lift; cocone naturality respects the generating relation. Factorization is definitional and uniqueness follows by quotient induction. This proves homCocone_isColimit and realizes [def-weil-pbc-category-colimit]. With the filteredness of the common-stage preorder from step 1, Functor.ιColimitType_eq_iff_of_isFiltered gives the common-stage equality criterion directly on this quotient, realizing [lem-weil-pbc-filtered-colimit-sets-elementwise] without a further ULift comparison.

### Original step 3

For three fixed objects $a=(i,x)$, $b=(j,y)$, $c=(l,z)$ and a stage $m$ above all three indices, write $g_m:T_{im}x\to T_{jm}y$ and $h_m:T_{jm}y\to T_{lm}z$. For $m\le p$, direct cancellation of the middle isomorphisms gives
$$t^{ac}_{mp}(h_mg_m)=\tau_{lmp,z}T_{mp}(h_mg_m)\tau_{imp,x}^{-1}=\bigl(\tau_{lmp,z}T_{mp}(h_m)\tau_{jmp,y}^{-1}\bigr)\bigl(\tau_{jmp,y}T_{mp}(g_m)\tau_{imp,x}^{-1}\bigr)=t^{bc}_{mp}(h_m)t^{ab}_{mp}(g_m).$$
Here the superscripts specify the pair of objects determining $t$. Likewise $t^{aa}_{mp}(\mathrm{id}_{T_{im}x})=\mathrm{id}_{T_{ip}x}$, because a functor preserves identities and conjugating an identity by an isomorphism gives an identity.

### Original step 4

The helper compAt_transition moves a product to a later stage using steps 1 and 3 and homClass_transition. For two upper bounds m and n choose p above both. Moving each product to p proves compRepresentative_eq_compAt. To descend composition by Quot.liftOn₂ it suffices to respect the generating transition relation separately in each input. Choose a stage above the other input and the later representative; homTransition_comp identifies the two transported inputs there. This proves compRepresentative_rel_right and compRepresentative_rel_left without needing the full eventual-equality criterion.

### Original step 5

For three composable classes choose one stage above their three representative stages. By step 4 both bracketings of their composite are represented there by the two bracketings of the same three morphisms in that stage category, and are equal by its associativity. For $a=(i,x)$, normalization $T_{ii}=\mathrm{Id}$ makes $[i,\mathrm{id}_x]$ a morphism $a\to a$; at every later stage $m$ it is represented by $\tau_{iim,x}T_{im}(\mathrm{id}_x)\tau_{iim,x}^{-1}=\mathrm{id}_{T_{im}x}$. Thus left and right composition with it reduce to the identity laws at a common stage. The pair objects, Hom sets, composition, and identities now define an ordinary category.

### Original step 6

For a representative $g\in H_k$ the map $P_k(g)=\theta_{jk,y}\Phi_k(g)\theta_{ik,x}^{-1}$ has source $\Phi_i(x)$ and target $\Phi_j(y)$ by [det-def-sfb-filtered-two-colimit-cocone]. For $k\le n$, cocone compatibility, applied to $i\le k\le n$ and $j\le k\le n$, gives
$$\theta_{in,x}^{-1}=\Phi_n(\tau_{ikn,x})\theta_{kn,T_{ik}x}^{-1}\theta_{ik,x}^{-1},\qquad
\theta_{jn,y}=\theta_{jk,y}\theta_{kn,T_{jk}y}\Phi_n(\tau_{jkn,y})^{-1}.$$
Substitute these and $t_{kn}(g)=\tau_{jkn,y}T_{kn}(g)\tau_{ikn,x}^{-1}$. The two pairs of inverse $\Phi_n(\tau)$ factors cancel, and naturality of the cocone isomorphism $\theta_{kn}:\Phi_nT_{kn}\Rightarrow\Phi_k$ gives
$$P_n(t_{kn}(g))=\theta_{jk,y}\theta_{kn,T_{jk}y}\Phi_nT_{kn}(g)\theta_{kn,T_{ik}x}^{-1}\theta_{ik,x}^{-1}=\theta_{jk,y}\Phi_k(g)\theta_{ik,x}^{-1}=P_k(g).$$
The private helper mapHomRepresentative_transition proves this calculation directly from cocone compatibility and naturality. Thus the formula respects each generating transition relation, and Quot.liftOn descends it to all classes without using the full eventual-equality criterion.

### Original step 7

Set $\Phi(i,x)=\Phi_i(x)$ on objects. Normalization and functoriality of $\Phi_i$ give $\Phi([i,\mathrm{id}_x])=\theta_{ii,x}\Phi_i(\mathrm{id}_x)\theta_{ii,x}^{-1}=\mathrm{id}_{\Phi_i(x)}$. For a composable pair use step 4 to represent both morphisms at one stage $m$, say $g_m:T_{im}x\to T_{jm}y$ and $h_m:T_{jm}y\to T_{lm}z$. Step 6 allows their images to be computed at $m$, and
$$\Phi([m,h_m])\Phi([m,g_m])=\theta_{lm,z}\Phi_m(h_m)\theta_{jm,y}^{-1}\theta_{jm,y}\Phi_m(g_m)\theta_{im,x}^{-1}=\theta_{lm,z}\Phi_m(h_mg_m)\theta_{im,x}^{-1}=\Phi([m,h_mg_m]).$$
This proves that the comparison assignment is a functor.

