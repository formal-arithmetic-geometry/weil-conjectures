# Repair of lem-sfb-polynomial-test-universally-open

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-test-universally-open.json`: statement unchanged, split into a two-step assembly (1023 characters).
- `dag/nodes/sec-six-functors-basics/lem-sfb-tensor-principal-polynomial-model.json`: statement; unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-principal-affine-test-universally-open.json`: statement; unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quote for every use of each assembly step (the complete polynomial-model statement is quoted to include its finite-data and image assertions).

## Attachments

None. The upstream source search by blueprint tag and polynomial/openness concepts found no completed exact project declaration. `lean/Sheaf/AlgebraicGeometry/PolynomialTestUniversallyOpen.lean:70` states the item and its proof is `sorry`.

## WANTED

None for this repair: the required Stacks sources are local.

## What required repair

The return requires spreading the 4242-character argument across at least two genuinely independent, comparable statement-only tasks, with an assembly of at most 3000 characters. No statement dispute was found. The sandbox initially held only dispatcher markers, with no nodes, report or search log; the current repository item was copied as the returned working text. The first dry run exited for missing report/review. The two children preserve different arguments, not the polynomial-test hypothesis or the whole conclusion as a single restatement.

The polynomial model carries old steps 2,3,4 (2181 characters in the returned text): finite tensor coefficients; evaluation; ring pushout by an explicit universal map; cartesian spectra; pullback of principal opens; exact image identity. The affine criterion carries old steps 1,5,6 (2061 characters): tensor affine pullback; principal-open basis; unions; affine cover of an arbitrary base; open-immersion pullback; identification of iterated fibre products; local image gluing. The assembly alone uses the original hypothesis to infer openness of the polynomial image and takes its continuous inverse image.

## Not duplicates

lem-sfb-tensor-principal-polynomial-model vs lem-sfb-polynomial-test-universally-open: no openness assumption or universal-openness conclusion; it constructs a finite polynomial/cartesian model for a single arbitrary tensor element and states its exact image identity.
lem-sfb-tensor-principal-polynomial-model vs lem-sfb-finite-dominant-normal-base-universally-open: the latter assumes finite dominance over an integral locally Noetherian normal base and asserts openness; it gives no polynomial model or image identity.
lem-sfb-principal-affine-test-universally-open vs lem-sfb-polynomial-test-universally-open: the criterion assumes principal-open image tests for every arbitrary A-algebra, with no polynomial assumption; its work is the separate basis and affine-cover localization argument.
lem-sfb-principal-affine-test-universally-open vs lem-sfb-finite-dominant-normal-base-universally-open: the criterion has arbitrary rings and an explicit affine principal-open hypothesis, with no dominance, normality, integrality or finiteness assumption.
lem-sfb-tensor-principal-polynomial-model vs lem-sfb-principal-affine-test-universally-open: the first constructs a finite specialization model and image equality without assuming openness; the second glues openness from arbitrary affine principal-open tests without constructing any polynomial model.
lem-sfb-tensor-principal-polynomial-model vs lem-weil-pbc-tensor-map-polynomial-presentation: the existing theorem transports a supplied finite presentation, assumes finitely many generators/relations, and says nothing about modeling an arbitrary tensor element, cartesian evaluation squares or image equality.

DAG searches by 0F31, polynomial/pushout, principal-open/base-change and universal-openness wording, and whole-blueprint searches for polynomial, universally open, 0F31, principal open, polynomial specialization, affine base changes, finite polynomial and principal-open found no equal or stronger statement. The only existing 0F31 users are the item and its finite-dominant parent; both pairs are distinguished above.

lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-qcqs-finite-affine-open-cover: the existing lemma gives a finite affine cover only for a quasi-compact scheme; the new criterion proves openness after every scheme base change from tensor principal-open image tests and needs no quasi-compactness.
lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-affine-opens-basis: the existing lemma supplies affine neighbourhoods, without any assertion about images or universal openness; the new criterion assembles tensor principal-open tests and affine restriction identifications into universal openness.
lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-etale-finite-affine-restriction-detection: the existing statement is finite affine etale restriction detection for equality of sheaf sections over a qcqs base, not openness of arbitrary tensor pullbacks.
lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings: the existing statement gives cofinal finite affine coverings under qcqs hypotheses; the new criterion proves universal openness and handles arbitrary infinite covers without those hypotheses.
lem-sfb-principal-affine-test-universally-open vs lem-sbc-affine-preparation-restriction: the existing statement restricts supplied universal-homeomorphism preparations to obtain flat locally finitely presented maps; the new criterion assumes neither preparations nor flatness and concludes universal openness from principal-open image tests.
lem-sfb-principal-affine-test-universally-open vs lem-pc-closed-imm-base-change: the existing statement treats closed immersions and their pulled-back ideal sheaves; the new criterion treats arbitrary affine morphisms with open images of principal opens after arbitrary affine base changes.
lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-closed-immersion-base-change: the existing statement asserts stability of closed immersions, not the criterion for universal openness or the arbitrary-base localization of open images.
lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-immersion-base-change-lft: the existing statement asserts immersion base-change stability and local finite type; the new criterion requires no immersion or finite-type hypothesis and proves universal openness from tensor principal-open tests.
lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-open-immersion-base-change: the existing statement supplies stability of open immersions, a tool in the future proof; it does not prove openness for a general affine morphism whose tensor principal-open images are open.
lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-base-change-image: the existing statement supplies an arbitrary-subset image identity in a supplied cartesian square, but not a principal-open criterion or its basis and affine-cover assembly into universal openness.
lem-sfb-principal-affine-test-universally-open vs lem-weil-pbc-etale-covering-base-change: the existing statement preserves etale jointly surjective families under base change; it does not give openness or the tensor principal-open testing criterion.

lem-sfb-principal-affine-test-universally-open vs lem-sfb-coefficient-heart-curve-generic-neighborhood: the existing node constructs generic neighborhoods for a finite locally closed stratification of a Noetherian scheme and describes their immersion pullbacks; it neither assumes tensor principal-open image tests nor proves universal openness of an arbitrary affine morphism after arbitrary scheme base changes. Their shared 01JY reference is only the open-immersion base-change ingredient.

lem-sfb-principal-affine-test-universally-open vs lem-sf-hom-comparison-affine-inputs: the existing node gives finite affine covers and restriction of finite-coefficient constructible complexes and flat models on a finite-type scheme over an algebraic closure of a finite field; it makes no assertion about images of tensor principal opens or universal openness for arbitrary rings and arbitrary scheme base changes. Their common 01IT tag supplies affine neighborhoods only.

## Review by Q125

I read Stacks more-morphisms.tex Tag 0F31, lemma-test-universally-open, especially lines 21742--21784, for the item and both children. For the polynomial model I checked the displayed polynomial square and image equality against the tensor expansion at 21760--21762 and cartesian comparison at 21773--21784. For the affine criterion I checked the affine localization at 21742--21752 and basis reduction at 21757--21759; I also read schemes.tex Tags 01IT and 01JY (lemma-basis-affine-opens and lemma-base-change-immersion), and the arbitrary-subset equality in the proof of morphisms.tex Tag 01S1 (lemma-base-change-surjective). No SGA source is used. The chapter/unit records and inherited blueprint place were read; this remains the same local prerequisite of the alteration route, and neither record changes. The ancestor tool again returns None, matching the inherited null ancestor.

After the first content dry run, I opened all eleven additional same-tag node statements listed by the duplicate gate and added the individual distinctions above; none states the new criterion. Assembly step 1 cites the new polynomial-model statement for its finite n and image equality; that statement explicitly provides the maps, cartesian property and equality, so no use depends on a hidden proof. It cites the existing principal-open-basis statement only for D(h) being open, which its clause (i) says verbatim. Openness of the polynomial spectrum map is exactly the item's hypothesis at the n supplied by the model; continuity of Spec(e) is part of being a scheme morphism. Step 2 cites the new affine criterion whose hypothesis is exactly the conclusion of step 1 for all B,g. Its conclusion includes every scheme and base morphism in the unchanged item. All these statements were opened and read before citations.json was written.

I also read each former dependency statement: the module tensor definition supplies finite pure-tensor generation, polynomial definition supplies evaluation and uniqueness, algebra tensor universal property supplies w(b tensor c)=v(b)u(c), affine fibre-product theorem supplies the precise projections, basic-open pullback supplies the preimage formula, and base-change-image supplies equality for arbitrary subsets. The affine-open basis, open-immersion base-change, open-immersion definition and fibre-product universal property provide exactly the old arbitrary-base argument. They are future splitting material for the children; the children intentionally have no proof or proof dependencies.

For small cases, a zero tensor may use n=0 and h=0, with empty principal opens and empty images; zero rings give empty spectra and preserve the stated identities. No assertion requires e to be flat, finitely presented, surjective or injective. Compatibility u(phi_n(t_i))=v(e(t_i)) forces u(t_i)=v(b_i), so the universal pushout map has the required restriction on variables even when A to C is not injective. The affine criterion includes empty T and any infinite affine cover; q(O) is the union of its intersections with the cover, without assuming quasi-compactness or affine intersections. These checks preserve all hypotheses of the source.

I ran three search kinds plus LeanSearch for each child and tried a second semantic/name phrasing. LeanSearch was rate-limited and is recorded unavailable. I read the relevant Mathlib candidates PolynomialLaw.exists_lift (Basic.lean:452), MvPolynomial.instIsPushout (TensorProduct/MvPolynomial.lean:178), and universal-openness locality (UniversallyOpen.lean:92--103). They are only ingredients, not one-line specializations of the full child statements. No search is recorded as executed unless its query occurs in searches.jsonl. No new proof step is longer than 2000 characters; each child is statement-only. No repository, launcher or Lean file was written, and no compiler was invoked.

## Preserved argument and handoff for the new workers

The following six returned steps are retained verbatim. Steps 2--4 belong to `lem-sfb-tensor-principal-polynomial-model`; steps 1,5,6 belong to `lem-sfb-principal-affine-test-universally-open`. Their dependency lists are included so that the split has lost no argument or previously identified tool. These are handoff material in the report, not proofs placed inside the statement-only children.

### Original step 1

Fix any commutative $A$-algebra $B$, without a finite-generation assumption, and put $D=B\otimes_A C$. The affine fibre-product theorem identifies $\operatorname{Spec}(D)$ with $\operatorname{Spec}(C)\times_{\operatorname{Spec}(A)}\operatorname{Spec}(B)$, with projection $q_B:\operatorname{Spec}(D)\to\operatorname{Spec}(B)$ induced by $b\mapsto b\otimes1$ (interchanging the two factors in that theorem). The principal opens $D_D(g)$, $g\in D$, form a basis. It therefore suffices to prove that $q_B(D_D(g))$ is open for every $g\in D$.

Uses: lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-spec-localization-away-basic-open

### Original step 2

Fix $g\in D$. Since pure tensors generate the tensor product as an $A$-module, write $g=\sum_{i=1}^n b_i\otimes c_i$ with $n\geq0$; scalar coefficients in a linear combination are absorbed into the $b_i$. Put $R=A[t_1,\ldots,t_n]$, $S=C[t_1,\ldots,t_n]$ and $h=\sum_i c_i t_i\in S$. Polynomial evaluation gives $e:R\to B$ with $e(a)=a_B$ and $e(t_i)=b_i$, and $k:S\to D$ with $k(c)=1\otimes c$ and $k(t_i)=b_i\otimes1$. The tensor multiplication rule gives $k(h)=\sum_i(b_i\otimes1)(1\otimes c_i)=g$. The maps $R\to S\to D$ and $R\xrightarrow{e}B\to D$ agree on coefficients and variables, hence agree. At $n=0$ these are the coefficient maps and $h=g=0$.

Uses: def-weil-pbc-module-tensor-product, def-weil-pbc-mv-polynomial-ring, lem-weil-pbc-algebra-tensor-pushout-universal-property

### Original step 3

The commuting ring square of step 2 is a pushout. Indeed, for a commutative ring $E$, suppose $u:S\to E$ and $v:B\to E$ agree on $R$. Their restrictions $u|_C$ and $v$ agree on $A$, so the tensor-product universal property gives the unique map $w:D\to E$ satisfying $w(b\otimes c)=v(b)u(c)$. It has $w\circ(B\to D)=v$. Also $wk=u$: this holds on every $c\in C$, and on $t_i$ it is $wk(t_i)=v(b_i)=u(t_i)$ by compatibility on $R$; polynomial uniqueness finishes the equality. Conversely any map with these two restrictions has this formula on pure tensors and is unique. Thus the affine fibre-product theorem and uniqueness of the fibre product identify the square with top arrow $\alpha=\operatorname{Spec}(k):\operatorname{Spec}(D)\to\operatorname{Spec}(S)$, bottom arrow $\beta=\operatorname{Spec}(e):\operatorname{Spec}(B)\to\operatorname{Spec}(R)$, and vertical arrows $q_B$ and $f_n=\operatorname{Spec}(\varphi_n)$ as cartesian.

Uses: lem-weil-pbc-algebra-tensor-pushout-universal-property, def-weil-pbc-mv-polynomial-ring, lem-weil-pbc-fibre-product-affine-spectra, def-pc-fibre-product, def-weil-affine-spectrum

### Original step 4

By hypothesis $f_n$ is open, so $U=f_n(D_S(h))$ is open in $\operatorname{Spec}(R)$; $D_S(h)$ is open by the principal-open basis theorem. Pullback of a basic open gives $\alpha^{-1}(D_S(h))=D_D(k(h))=D_D(g)$. Apply the base-change image identity to the cartesian square of step 3 and the subset $D_S(h)$ of $\operatorname{Spec}(S)$. It gives $q_B(D_D(g))=\beta^{-1}(f_n(D_S(h)))=\beta^{-1}(U)$. The last set is open because $\beta$ is a scheme morphism, hence continuous. This uses the image identity for arbitrary subsets, without any flatness or finite-presentation condition on $e:R\to B$.

Uses: lem-weil-pbc-spec-localization-away-basic-open, lem-weil-pbc-basic-open-pullback, lem-weil-pbc-base-change-image

### Original step 5

Every open $O\subseteq\operatorname{Spec}(D)$ is the union of the principal opens contained in it. Its image under $q_B$ is the union of their images, each open by step 4, and hence is open. Thus the base change to $\operatorname{Spec}(B)$ is open for every commutative $A$-algebra $B$.

Uses: lem-weil-pbc-spec-localization-away-basic-open

### Original step 6

Now let $T\to\operatorname{Spec}(A)$ be any scheme morphism and put $P=\operatorname{Spec}(C)\times_{\operatorname{Spec}(A)}T$, with projection $q:P\to T$. Cover $T$ by affine open subschemes $W_j\cong\operatorname{Spec}(B_j)$, using the affine-open basis theorem. Each induced morphism $W_j\to\operatorname{Spec}(A)$ corresponds to a ring map $A\to B_j$. Set $P_j=P\times_T W_j$. Base change of the open immersion $W_j\hookrightarrow T$ makes $P_j\to P$ an open immersion; the base-change image identity (applied to the whole of $W_j$) identifies its image with $q^{-1}(W_j)$. Thus it identifies $P_j$ with that open subscheme. The universal property of fibre products identifies $P_j$ with $\operatorname{Spec}(C)\times_{\operatorname{Spec}(A)}W_j$: a map into either object is exactly a pair of maps into $\operatorname{Spec}(C)$ and $W_j$ agreeing over $\operatorname{Spec}(A)$. Its projection $q_j:P_j\to W_j$ is open by step 5. For any open $O\subseteq P$, the set $q(O)\cap W_j=q_j(O\cap q^{-1}(W_j))$ is therefore open in $W_j$ and hence in $T$. Taking the union over $j$ proves that $q(O)$ is open. This proves universal openness for arbitrary $T$, including the empty scheme, with no quasi-compactness or separation assumption.

Uses: lem-weil-pbc-affine-opens-basis, def-weil-affine-spectrum, lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-base-change-image, def-weil-open-immersion, def-pc-fibre-product

## Unfinished work

The two new nodes are deliberately unsplit, ready for separate workers. Required server checks and delivery follow this self-review.

The server preflight also requested standalone wording in assembly step 1: its reference to the hypothesis now explicitly says that every polynomial spectrum map is assumed open. This is only a wording correction; the quantified hypothesis and applications are unchanged.

## Repair of the landing return at head 1fb5d7ad0e3

The reader-approved delivery was returned because its side-project completion had not been promoted to the live queue DAG. I have retained the two statement-only children, all their actual searches, the two-step assembly, citations, and the verbatim six-step handoff above. I compared the retained item with the current shared DAG and rebuilt its JSON from that current node, overlaying only the retained proof, proof dependencies, actual additional search entries, and split report. The current statement, statement dependencies, source, blueprint ancestry, Lean metadata, import fields, and existing review history are preserved. The released stage-1 repair note still explicitly requires this re-split and at least two new nodes, so the older passing review does not supersede it. The authorized delivery tool will create the delivery commit on its freshly fetched current server base.

I re-read the current statements of every existing citation: def-weil-affine-spectrum supplies both contravariant Spec morphisms and their correspondence with ring maps; def-weil-pbc-mv-polynomial-ring supplies evaluation; def-pc-scheme supplies schemes and affine opens; def-pc-fibre-product supplies existence, projections and the universal property; def-weil-pbc-module-tensor-product supplies the underlying module tensor product; def-weil-open-immersion supplies identification with the open subscheme; lem-weil-pbc-spec-localization-away-basic-open supplies exactly clause (i) used in assembly step 1. All remain unmerged Mathlib leaves and their statements support the retained uses. I re-read both children's complete statements as well: the model provides the image equality for every B,g without an openness assumption; the criterion assumes exactly the principal-open image openness established by step 1 and gives the arbitrary-scheme base-change conclusion used in step 2. The three citations.json quotes remain verbatim substrings of these current or delivered statements. There is no new hypothesis to discharge and no changed mathematical citation requiring a different proof.

The first repair dry run terminated without pushing and identified one newly present same-tag node, lem-sfb-coefficient-heart-curve-generic-neighborhood. I opened and read its full statement and proof: it concerns generic points of finitely many components in a Noetherian stratified scheme, keeping the stratum scheme structures. It is not the arbitrary-affine principal-open testing criterion. I added its required individual comparison in Not duplicates. This is a content repair of the stale duplicate audit as well as a rebase, not an unchanged re-push. The source remains Stacks 0F31, which I reread in full at more-morphisms.tex lines 21725--21788. The edge cases and argument allocation checked above are unaffected. The exact project theorem in PolynomialTestUniversallyOpen.lean still ends in sorry, so there is no attachment. No Lean, repository, or launcher file has been written and no compiler has been run.

## Continued landing repair for returned head 596256b6702

The resumed dry run passed at 59e99e86be5. After the interrupted push session disappeared, I checked that no deliver.py invocation remained active. The next authorized delivery invocation completed with an exact-content result: the server branch was already at 596256b670 with this retained content, so it correctly declined an unchanged push. This is the head of the currently supplied landing return; the earlier repair section addressed its predecessor.

I compared the sandbox item against the current shared DAG: the statement, statement dependencies, source, blueprint metadata and maintained fields agree; the intended differences are the short assembly, its three proof dependencies, the retained searches and split report. Both children remain absent from the current DAG. I reread the released repair note, which still requires two statement-only tasks and preserves the statement. I reread all current statement dependencies of the item and children, and all three assembly citations. The existing principal-open lemma remains an unmerged Mathlib leaf whose clause (i) explicitly says every D(a) is open. The polynomial model supplies both the finite n and the exact image equality, without any assumption on the evaluation map. The affine criterion requires all A-algebras and all their tensor elements; step 1 establishes precisely those quantifiers. I adjusted step 2 to state that match explicitly, including the tensor multiplication and the map b to b tensor 1. No changed cited statement requires changing the mathematical route. All citation quotes remain verbatim.

I also reread the entire proof of Stacks Tag 0F31 at more-morphisms.tex lines 21725--21788 and the chapter and unit records. The finite sum, evaluation square and image identity agree with the model; principal opens and affine localization agree with the criterion. The project source search still yields no exact completed declaration in WeilConjectures; the Sheaf theorem still ends in sorry. The zero element, n=0, zero rings, empty scheme and unrestricted affine-cover checks above still apply. This continuation changes the assembly wording and records validation of the currently returned head; it does not discard or repeat any logged search or preserved argument. The final delivery command will build on its freshly fetched current server base.


## Current landing-return repair, 2026-10-23

The required initial dry run completed without pushing and found one additional same-tag node, lem-sf-hom-comparison-affine-inputs (01IT). I read its whole current statement: it supplies affine covers and restrictions of constructible complexes and flat models over a finite-field datum. It does not state the principal-open image criterion for arbitrary commutative rings. The new pair is now individually distinguished under Not duplicates.

I compared all three retained node files to the current shared DAG. Both children are still absent; the item still has the former six-step proof. The released stage-1 repair note continues to require at least two comparable new tasks and a short assembly, preserving the statement. I refreshed the item from the current live JSON, retaining only Q125's proof, proof dependencies, actual searches and split report. Thus the statement, statement dependencies, source, maintained Lean records, review history, creation metadata and blueprint ancestry remain those of the current live node. This is a live-base delivery by the authorized tool, with an updated duplicate audit and a concrete clarification of the assembly, rather than an unchanged re-push.

I reread Stacks more-morphisms.tex, Tag 0F31, lemma-test-universally-open, including the finite tensor expansion, polynomial evaluation square, image equality and affine localization. I reopened every current existing statement dependency of the item and children and the principal-open basis lemma. None changes the mathematical applications. I also reread both complete child statements and all retained searches.jsonl entries and saved search results; the statement and search questions have not changed, so no query is repeated or invented. The project-tag search in WeilConjectures still gives no completed exact declaration; the Sheaf declaration at PolynomialTestUniversallyOpen.lean:70 still has a sorry proof.

Assembly step 1 now explicitly defines D, j, q_B and D_D(g), avoiding notation supplied only implicitly by the cited child. The polynomial-model statement supplies a finite n and exactly the displayed image identity for every B,g. Clause (i) of the existing principal-open lemma supplies openness of D_S(h). The item's hypothesis applies at that n, and continuity takes its open image back to Spec B. Assembly step 2 applies the criterion with precisely these universally quantified B,g tests; its conclusion is exactly the original arbitrary-scheme conclusion. The three quotes in citations.json are still verbatim substrings of the respective statements. The model has no openness assumption; the criterion does not assume polynomial tests. Hence neither child restates the item, and the short assembly supplies the missing link.

I checked n=0 and g=0, zero rings and empty spectra, empty schemes and infinite affine covers again. No evaluation map is assumed flat or injective, and no affine intersections or quasi-compactness hypotheses enter the criterion. Both children remain statement-only, the two assembly steps are below 2000 characters individually, and all six original arguments remain in the handoff above. No repository, launcher or Lean file was changed and no compiler was invoked.
