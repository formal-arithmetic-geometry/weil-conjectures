# Stage-1 delivery: lem-sfb-qcqs-finite-complex-heart-filtered-closure

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-finite-complex-heart-filtered-closure.json: corrected Noetherian statement and four-step assembly proof; no Mathlib match.
- citations.json: seven verbatim supporting extracts, one for every step/node pair.
- searches.jsonl: actual search-command results, retained without editing. write_split.py is a sandbox working file.

Zero new nodes and zero Mathlib leaves. The NN nodes lem-sfb-noetherian-scalar-constructible-heart, lem-sfb-noetherian-scalar-constructible-fp2, and lem-sfb-fp2-ind-realization were already in the shared DAG and are reused unchanged. The sandbox initially contained only dispatcher brief markers, with no previous split or report.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, finite-complex-heart terminology, and ind-constructible terminology. CompactConstructible.lean defines IsIndConstructibleHeart as a hypothesis, not a proof of this assertion. The continuousMapRingObj/padicIntegersRingObj/padicAlgClRingObj declarations in CompactConstructibleEllAdic.lean concern stronger geometric assumptions and do not state the present full coefficient/no-cohomological-bound theorem. No exact finished project declaration was found.

## WANTED

No new document is required for this assembly. The existing FP2 dependency retains its own WANTED qualification: a printed formulation including arbitrary finite nonregular A and Yoneda Ext1 in exactly its generality. HRS Lemma 5.3 is the derived-constructible/perfect statement, not a verbatim source for that finite-nonregular case. This delivery relies on the named statement-only node rather than silently treating it as proved.

## Statement correction and source error

STATEMENT-DISPUTED: the original assertion for arbitrary qcqs X is false, already for Lambda=Q_ell. The repaired statement adds that X is Noetherian. All six coefficient cases, all-continuous Omega coefficients, arbitrary diagram arrows, ambient extensions and the original indexing universe remain explicit. No absolute cohomological-dimension hypothesis is introduced. The imported title still says qcqs because title is a maintainer-owned field.

Here is the counterexample, including the obstruction for the actual finite-complex class rather than just for constructibles. Let S=beta(N), let k be an algebraically closed field, and let X=Spec(C_lc(S,k)), with k discrete. This absolutely flat ring has spectrum S and local rings k. Since S is extremally disconnected, X is affine w-contractible. Put R=C(S,Q_ell), and let f be the continuous extension of n |-> ell^n. It vanishes on the boundary S minus N. Multiplication by f on R is injective: a function annihilated by f vanishes on dense N and hence everywhere. Multiplication by f on Lambda_X has nonzero sheaf kernel Z: after restriction to the nonempty boundary, f is zero. The boundary is a pro-etale object, being the inverse limit of its clopen neighbourhoods. This is HRS Example 4.2, transported to the profinite scheme via Proposition 4.3. In particular Gamma(X,Z)=0 does not imply Z=0.

Write F:D(R)->D(X,Lambda) for the fully faithful realization of HRS Lemma 4.1, left adjoint to exact, colimit-preserving Gamma, and put F_0(M)=H^0F(M[0]). Constructible subsets of the Stone space S are clopen, so every scalar-model constructible module on X is lisse. By HRS 4.1(2), a finite complex of such modules is F(P) for a perfect R-complex P. Concretely each term corresponds to a finite projective R-module (Gamma is exact and conservative on the realization image), and the maps correspond under full faithfulness.

HRS Theorem 6.12 makes R semihereditary. Thus it is coherent and its finitely presented modules have projective dimension at most one. Perfect P has finitely presented cohomology. F on modules has amplitude [-1,0]: use a length-one finite-projective resolution for finitely presented modules, then express arbitrary modules as filtered colimits. The exactness of filtered colimits gives the same amplitude for arbitrary modules. The two-row hyperhomology calculation consequently gives the natural exact sequence

0 -> F_0(H^0P) -> H^0F(P) -> H^(-1)F(H^1P[0]) -> 0.

The first map is the counit F_0(Gamma N)->N for N=H^0F(P), since Gamma F(P)=P and Gamma is exact. Therefore that counit is monic for every finite-stage N_K. It remains monic for every object of I_X: Gamma and F_0 preserve filtered colimits and filtered colimits of monomorphisms in the module category are monomorphisms.

Now let B=im(f:Lambda_X->Lambda_X). Exactness of Gamma gives Gamma B=fR, which is isomorphic to R. Under this isomorphism its counit F_0(Gamma B)->B is precisely Lambda_X->B induced by multiplication f. Its kernel is the nonzero Z. Hence B is not in I_X. However Z=H^0([Lambda_X --f--> Lambda_X] in degrees 0,1) lies in I_X, as does Lambda_X. The cokernel of Z->Lambda_X is B, so cokernel closure fails. Also Q=coker f is the H^0 of the two-term finite complex in degrees -1,0; Lambda_X and Q belong to I_X, whereas ker(Lambda_X->Q)=B does not. Thus kernel closure fails as well.

My source analysis reached this same obstruction before I read the already-landed NN sibling report. Its amplitude/counit argument confirms the stronger finite-complex-class test; an invisible kernel by itself would be insufficient. The sibling lem-sfb-finite-complex-heart-filtered-approximation has already received the same Noetherian correction. Its three reusable lemmas avoid creating duplicates here. That affine sibling assumes a local cohomological bound, whereas the present repair is qcqs Noetherian and requires no such bound; neither statement is a replacement for the original general qcqs claim.

## Consequence for the parent

The parent lem-sfb-closed-torsion-rigidity-serre-transfer, step 2, applies this item to a merely qcqs T. After this correction it must supply Noetherianity or replace that argument. In particular the arbitrary-qcqs rigidity claim has not been proved by this delivery. I cannot edit that other item, the blueprint unit or Challenge targets. This report explicitly flags the affected application for maintainer repair. The source refinement paragraph (2) asserts derived direct-sum preservation; it does not prove the false heart-presentation lemma extracted by earlier agents. The unit route is retained for the corrected domain.

## Review by NY

I read the latest refinement and cocycle proofs and the sk-prop-ind-heart proof, the chapter/unit records, and the entire B–E checklist. For the source error I read HRS Lemma 4.1, Example 4.2, Proposition 4.3, Lemma 5.3, Theorem 6.2, Remark 6.4, Theorem 6.12, and Section 8. The derived Ind-completion results of Section 8 do not imply ordinary-heart kernel/cokernel closure for this I_X. No prohibited SGA source is used.

Step 1 cites exactly three opened statements. The small sieve-site theorem supplies Grothendieckness for Z-module sheaves, so it is applied with Z, not with the varying coefficient ring. The sheaf tensor node gives the closed symmetric monoidal structure; its sheafification formula gives additivity. The internal-module theorem then applies to Lambda_X and supplies Grothendieckness of the actual ambient category. These three off-unit inputs are declared generic tool uses.

Step 2 uses the existing scalar-constructible-heart node. Its statement includes essential smallness, zero and ambient kernel/cokernel/extension closure, precisely for Noetherian X and the same six rings, including integral torsion scalar models and all-continuous Omega. It is not a theorem just about field coefficients, nor does it add characteristic, dimension, invertibility or completeness assumptions. I read its HRS source clauses; finite nonregular A uses the discrete branch rather than an invalid t-admissibility assertion.

Step 3 is elementary from the kernel/cokernel clauses just cited. I wrote cycles and boundaries explicitly, including B=coker(ker d^{-1}->K^{-1}), before taking coker(B->ker d^0). The reverse inclusion uses C[0]. This identifies classes of heart objects and arbitrary module-map diagrams; it never assumes morphisms lift to complexes. No elementary fact was made into a node.

Step 4 uses the complete statements of scalar-constructible-fp2 and fp2-ind-realization, both already landed. The former supplies bijective Hom and Yoneda Ext1 comparisons for arbitrary ambient filtered diagrams, including injectivity. The latter assumes exactly Grothendieckness, essential smallness, finite weak Serre closure, and those comparisons, all supplied by steps 1–2 and the first cited statement. It concludes arbitrary ambient extensions, not just extensions equipped with a finite-stage lift. This is a general categorical input with separate hypotheses, not a relabelled clause of the present geometric item. Its same-universe conclusion is explicit. No derived-versus-Yoneda Ext identification is silently required: both inputs use Yoneda Ext1.

I checked zero complexes, C[0], complexes with three relevant degrees, the empty scheme, zero coefficient rings, integral torsion models, finite nonregular A, infinite coproducts and arbitrary diagram arrows. No step exceeds 2000 characters; the entire proof is 2184 characters. All substantive facts used in the assembly have cited statements, and all seven citation extracts were checked as literal substrings. Existing JSON fields outside the split-owned set are retained. Statement/definition notions and stmt_deps include the new Noetherian condition.

## Searches and duplicates

I searched the entire DAG and current blueprint with blueprint_refs.py for finite complexes, finite-complex hearts, coherent objects, subobjects, scalar models, isomorphism classes and continuity. The live repository contained the three NN lemmas before I created any new node, so the proposed new continuity/smallness nodes were discarded. There are no new nodes and hence no same-tag new/existing pairs needing justification. The closest affine sibling has an additional affineness and local-bound hypothesis; its proof inputs are reused directly.

All Mathlib searches used msearch.py and are retained as logged. The item preserves its imported search records and adds this worker's actual searches. The semantic searches, Loogle patterns and grep queries returned only abstract Ind-category results, Serre-class definitions, ordinary sheaf finite presentations, scalar-module smallness, or condensed AB axioms. I inspected the relevant Mathlib files: CategoryTheory/ObjectProperty/Extensions.lean, CategoryTheory/Abelian/SerreClass/Basic.lean, and Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean. None identifies this geometric realization image or proves the entire assertion by specialization. No search that failed or was not run is represented as evidence of absence.

## Unfinished work

There is no unfinished split for the corrected statement and no new node to deliver. The upstream use under only qcqs hypotheses remains invalid and is expressly reported above. No Lean was written or compiled, and no git command or repository write was performed. The required delivery tool performs server validation and constructs its own worktree.
