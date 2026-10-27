# Worker report

## Files written

- lem-sfb-local-domain-fg-field-dvr: parent statement unchanged; four-step assembly.
- lem-sfb-polynomial-origin-finite-field-reduction: statement, unsplit; no complete Mathlib match.
- lem-sfb-finite-normalization-local-dvr: statement, unsplit; no complete Mathlib match.

## Attachments

None. The project declaration IsLocalRing.exists_discreteValuationSubring_of_fg_extension in lean/Sheaf/RingTheory/DiscreteValuationRing/FinitelyGeneratedExtension.lean ends in sorry. The upstream IsLocalRing.exists_isDiscreteValuationRing in WeilConjectures/RingTheory/DiscreteValuationRing/Dominating.lean:250 does not prescribe its fraction field. Searches in the whole WeilConjectures tree by the item tag, declaration and concepts found no exact finished attachment.

## WANTED

None. All algebraic sources are present in literature/stacks-project/.

## Fault and repair

The returned proof contains eight valid arguments but 4979 characters, too much for the requested work allocation. There was no saved node/report in this sandbox; the live node is the returned eight-step version, so it was copied without changing its statement, Lean record, audit, approved tool uses or reviewer metadata. This delivery adds two genuinely different construction lemmas, of comparable proof workloads (former steps 1--3: 2265 characters; former steps 5--8: 2237 characters), each unsplit with empty proof/proof_deps/proof_origin and independently logged searches. The dimension-one bridge stays in the parent. No unit or chapter route changes. No statement dispute was found.

## Unfinished work

Only the two new nodes' future splits, intentionally reserved for independent workers; this delivery supplies their complete statements, sources and searches. No Lean was written and no compiler, Lake or build tool was run.

## Allocation of every former argument

The following is the returned proof verbatim, retained as handover material, not proof fields of the new unsplit nodes. Former steps 1--3 belong to the polynomial-origin node; former steps 5--7 and the C-to-D contraction of step 8 belong to the normalization node; former step 4 and the D-to-R contraction of step 8 are in the parent's assembly. Original citations remain attached to each argument below. This preserves the construction, coefficient-kernel argument, localization embedding, fraction fields, nonfield checks, nonzero-prime chain and domination calculations; nothing is dropped.

### Former step 1

Write $L=K(a_1,\ldots,a_n)$. By [lem-weil-pbc-finitely-generated-field-finite-transcendence-basis], choose a finite transcendence basis $x_1,\ldots,x_r$ and put $K_0=K(x_1,\ldots,x_r)\subseteq L$. Thus the $x_i$ are algebraically independent over $K$ and $L/K_0$ is algebraic. Also $L=K_0(a_1,\ldots,a_n)$: the right side contains $K$ and all the original generators, and is contained in $L$. Each $a_i$ is algebraic over $K_0$, so [lem-weil-pbc-algebraic-generators-finite-extension] gives $[L:K_0]<\infty$. This includes $r=0$, when $K_0=K$.

Cited nodes: lem-weil-pbc-finitely-generated-field-finite-transcendence-basis, lem-weil-pbc-algebraic-generators-finite-extension.

Source: Tag 00PH, algebra-lemma-exists-dvr, first paragraph; Fields Tags 030F (fields-lemma-transcendence-degree) and 09GH (fields-lemma-algebraic-finitely-generated).

### Former step 2

Let $P=R[x_1,\ldots,x_r]\subseteq K_0$. The polynomial-ring evaluation map [def-weil-pbc-mv-polynomial-ring] is injective: by algebraic independence [def-weil-pbc-transcendence-basis], a polynomial over $K$ vanishing at the $x_i$ has every coefficient zero, and $R\subseteq K$ is injective. Hence $P$ is a polynomial ring over $R$, and [lem-weil-pbc-finite-type-algebra-noetherian] makes it Noetherian. The map $P\to R/\mathfrak m_R$ sending every $x_i$ to zero and each coefficient to its residue is surjective. Its kernel is $\mathfrak n=(\mathfrak m_R,x_1,\ldots,x_r)$: a polynomial lies in the kernel exactly when its constant coefficient is in $\mathfrak m_R$, and its remaining monomials are multiples of the $x_i$. As the quotient is a field, $\mathfrak n$ is maximal and $\mathfrak n\cap R=\mathfrak m_R$.

Cited nodes: def-weil-pbc-mv-polynomial-ring, def-weil-pbc-transcendence-basis, lem-weil-pbc-finite-type-algebra-noetherian.

Source: Tag 00PH, algebra-lemma-exists-dvr, first paragraph, the polynomial ring and its origin maximal ideal; Tag 00FN, algebra-lemma-Noetherian-permanence.

### Former step 3

Set $B=P_{\mathfrak n}$ [def-weil-pbc-localization-at-prime]. Concretely regard it as the subring $\{p/s:p,s\in P,\ s\notin\mathfrak n\}$ of $K_0$: all such denominators are nonzero, and equality of fractions is checked by cross multiplication in the domain $P$. It is local with maximal ideal $\mathfrak nB$, and [lem-weil-pbc-localization-noetherian] makes it Noetherian. For $p\notin\mathfrak n$, $p/1$ is a unit with inverse $1/p$; for $p\in\mathfrak n$, $p/1\in\mathfrak nB$. Thus $\mathfrak m_B\cap P=\mathfrak n$ and $\mathfrak m_B\cap R=\mathfrak m_R$. Fix $0\ne t\in\mathfrak m_R$; it remains nonzero in $B$ and belongs to $\mathfrak m_B$, so $B$ is not a field. The fraction field of $P$, hence of $B$, is exactly $K_0$: the field of ratios of $P$ contains all ratios from $R$, hence $K$, and the $x_i$, hence $K_0$; conversely all these ratios lie in $K_0$. For $r=0$ this construction gives $B=R$.

Cited nodes: def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-noetherian.

Source: Tag 00PH, algebra-lemma-exists-dvr, first paragraph, localization at the origin; Tag 00FN, algebra-lemma-Noetherian-permanence.

### Former step 4

Apply [lem-sfb-local-domain-birational-dimension-one] to $B\subseteq K_0$. Its hypotheses hold by step 3. Obtain $B\subseteq D\subseteq K_0$ with $D$ a Noetherian local integral domain of dimension $1$, fraction field $K_0$, and $\mathfrak m_D\cap B=\mathfrak m_B$. In particular $t\ne0$ belongs to $\mathfrak m_D$, and contracting once more gives $\mathfrak m_D\cap R=\mathfrak m_R$. The finite extension $L/K_0$ from step 1 is unchanged by this replacement of the local ring.

Cited nodes: lem-sfb-local-domain-birational-dimension-one.

Source: Tag 00PH, algebra-lemma-exists-dvr, second paragraph; Tag 00P8, algebra-lemma-dominate-by-dimension-1.

### Former step 5

Let $C\subseteq L$ be the integral closure of $D$ in $L$ [def-weil-pbc-integral-closure]. Apply [lem-sc-integral-closure-dedekind-surjective-fibres] to the Noetherian domain $D$ of dimension $1$, with fraction field $K_0$ and finite extension $L/K_0$. It gives that $C$ is a Noetherian integrally closed domain of dimension $1$, and that $\operatorname{Spec}C\to\operatorname{Spec}D$ is surjective. Choose a prime $\mathfrak q\subset C$ contracting to $\mathfrak m_D$. Independently [lem-weil-pbc-integral-closure-finite-extension-normal], under the same finite-extension hypotheses, gives that the given field $L$ is the fraction field of $C$. Thus the required field is retained, even when $L/K_0$ is inseparable.

Cited nodes: def-weil-pbc-integral-closure, lem-sc-integral-closure-dedekind-surjective-fibres, lem-weil-pbc-integral-closure-finite-extension-normal.

Source: Tag 00PH, algebra-lemma-exists-dvr, final paragraph, normalization and lying over; Tag 09IG, algebra-lemma-integral-closure-Dedekind; the fraction-field clause of normalization in a finite extension.

### Former step 6

The prime $\mathfrak q$ is nonzero because it contains the nonzero element $t\in\mathfrak m_D$. It is maximal: if a proper prime strictly containing it existed, the chain $(0)\subsetneq\mathfrak q\subsetneq\mathfrak p$ in the domain $C$ would contradict $\dim C=1$. Equivalently, taking a maximal ideal containing $\mathfrak q$ forces equality by this chain argument. Thus $\mathfrak q$ is a nonzero maximal ideal of the Dedekind domain $C$.

Cited nodes: .

Source: Tag 00PH, algebra-lemma-exists-dvr, final sentence; elementary chain argument from the dimension-one conclusion of step 5.

### Former step 7

Set $A=C_{\mathfrak q}$ [def-weil-pbc-localization-at-prime]. Since $C$ is a normal domain with fraction field $L$ and $0\notin C\setminus\mathfrak q$, [lem-weil-pbc-localization-normal-domain] embeds $A$ into $L$ by $c/s\mapsto c/s$ and states that its fraction field is $L$. Since $C$ is a Noetherian integrally closed domain of dimension $1$ and $\mathfrak q$ is maximal, [lem-sc-dedekind-localization-dvr] gives that $A$ is a discrete valuation ring. We have the inclusions $R\subseteq B\subseteq D\subseteq C\subseteq A\subseteq L$.

Cited nodes: def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-normal-domain, lem-sc-dedekind-localization-dvr.

Source: Tag 00PH, algebra-lemma-exists-dvr, final sentence; Tag 00GY, algebra-lemma-localize-normal-domain; Tag 034X, algebra-lemma-characterize-Dedekind, nonzero-prime localization clause.

### Former step 8

By [def-weil-pbc-localization-at-prime], $\mathfrak m_A=\mathfrak qC_{\mathfrak q}$. If $c\in\mathfrak q$, then $c/1\in\mathfrak m_A$; if $c\notin\mathfrak q$, then $c/1$ has inverse $1/c$ in $A$, so is not in its proper maximal ideal. Hence $\mathfrak m_A\cap C=\mathfrak q$. Contracting through the inclusions yields $\mathfrak m_A\cap R=(\mathfrak q\cap D)\cap R=\mathfrak m_D\cap R=\mathfrak m_R$. Together with step 7 this proves every required clause, including that each element of $L$ is a quotient of elements of this very subring $A$.

Cited nodes: def-weil-pbc-localization-at-prime.

Source: Tag 00PH, algebra-lemma-exists-dvr, final sentence: domination; contraction through a prime localization.

## Not duplicates

lem-sfb-polynomial-origin-finite-field-reduction vs lem-sfb-local-domain-fg-field-dvr: the parent allows arbitrary dimension and finitely generated, possibly transcendental extensions; the new node states only its explicit polynomial reduction or its dimension-one finite normalization construction, not the parent theorem.

lem-sfb-polynomial-origin-finite-field-reduction vs lem-sfb-local-domain-same-field-dvr: the same-field existence theorem supplies neither a polynomial-origin model nor the normalization and all its closed-point localizations in a prescribed finite extension.

lem-sfb-polynomial-origin-finite-field-reduction vs lem-sfb-dense-generic-trait-selection: the existing node selects a geometric trait meeting an open; the new node is a commutative-algebra construction and asserts no geometric selection.

lem-sfb-polynomial-origin-finite-field-reduction vs lem-sc-integral-closure-dedekind-surjective-fibres: 09IG gives Dedekindness and spectral surjectivity with finite fibres, not the polynomial-origin reduction or the DVR localization, fixed fraction-field embedding and maximal-ideal contractions.

lem-sfb-finite-normalization-local-dvr vs lem-sfb-local-domain-fg-field-dvr: the parent allows arbitrary dimension and finitely generated, possibly transcendental extensions; the new node states only its explicit polynomial reduction or its dimension-one finite normalization construction, not the parent theorem.

lem-sfb-finite-normalization-local-dvr vs lem-sfb-local-domain-same-field-dvr: the same-field existence theorem supplies neither a polynomial-origin model nor the normalization and all its closed-point localizations in a prescribed finite extension.

lem-sfb-finite-normalization-local-dvr vs lem-sfb-dense-generic-trait-selection: the existing node selects a geometric trait meeting an open; the new node is a commutative-algebra construction and asserts no geometric selection.

lem-sfb-finite-normalization-local-dvr vs lem-sc-integral-closure-dedekind-surjective-fibres: 09IG gives Dedekindness and spectral surjectivity with finite fibres, not the polynomial-origin reduction or the DVR localization, fixed fraction-field embedding and maximal-ideal contractions.

lem-sfb-polynomial-origin-finite-field-reduction vs lem-sfb-finite-normalization-local-dvr: the first constructs a rational-function local model for general finitely generated extensions; the second normalizes a dimension-one local ring in a finite extension and localizes above the closed point. Neither states the other.

I searched the entire DAG (tags 00PH and 09IG, polynomial origin, finite transcendence basis, integral closure and discrete valuation), not just this unit. Existing field-theory and normalization ingredients remain reusable, but none states either complete construction. Whole-blueprint searches through tools/blueprint_refs.py for 00PH, 09IG, transcendence basis, integral closure, polynomial origin and normalization localization found no equivalent blueprint statement. The origin search has unrelated etale-origin results. The ancestor command reports None; the existing null ancestor and full via chain are retained, adding this item first for each child.

lem-sfb-polynomial-origin-finite-field-reduction vs lem-sfb-local-domain-affine-dvr-square: the existing node constructs an affine valuative square from a finite-type map and its residue fields; it supplies neither a finite transcendence basis nor the explicit polynomial-origin localization B, its origin ideal, and its rational-function fraction field.

lem-sfb-finite-normalization-local-dvr vs lem-sfb-local-domain-affine-dvr-square: the existing node asserts existence of some dominating DVR and a commuting affine square, not that the integral closure of a dimension-one local domain is Noetherian normal with fraction field L, or that every closed-point localization of that specified closure is the required DVR.

lem-sfb-polynomial-origin-finite-field-reduction vs lem-sfb-nongeneric-point-same-field-dvr: the existing geometric node selects a trait at a nongeneric point without changing the scheme function field; it does not construct the polynomial-origin local model for an arbitrary finitely generated field extension.

lem-sfb-finite-normalization-local-dvr vs lem-sfb-nongeneric-point-same-field-dvr: the existing geometric node supplies some dominating trait in the original function field; it specifies no integral closure in a finite extension, no Noetherian normalization conclusion and no assertion about every prime above the closed point.

## Mathlib searches

Each new node records at least six actual searches from searches.jsonl: LeanFinder twice with different questions, Loogle, LeanSearch and two source grep queries. The normalization node additionally records the follow-up grep that fixes the localization theorem at Dvr.lean:128 and confirms the separability hypothesis at IntegralClosure.lean:147. Search result names and log digests are retained exactly. Source reads distinguish a theorem about an already Dedekind domain from construction of the normalization of a nonnormal domain without separability. No full Mathlib leaf is claimed. The parent's historical searches are retained; additional Q122 searches recheck its exact fraction-field requirement.

## Review by Q122

I read the full statement and all three proof paragraphs of Stacks Tag 00PH, algebra.tex label lemma-exists-dvr, and the 00P8 dimension-one and 09IG normalization statements/proofs in the same file. The parent agrees hypothesis by hypothesis: R is Noetherian, local, a nonfield domain; K is its given fraction field; L/K is finitely generated. Its conclusion fixes a subring of this L and both the fraction-field and maximal-ideal contraction conditions. The statement is unchanged.

The polynomial-origin node states precisely the first paragraph's construction and every property formerly established in steps 1--3: finite basis, finite residual field extension, injective polynomial evaluation, origin ideal and quotient, Noetherian prime localization, embedding into K_0, fraction fields and nonfield domination. I opened the statements of the existing finite-transcendence-basis and algebraic-generators-finite-extension nodes, the polynomial/transcendence-basis definitions, finite-type-Noetherian theorem, localization definition and localization-Noetherian theorem. Their quoted content supports exactly the preserved arguments. The residue evaluation kernel is proved coefficient by coefficient; the embeddings and fraction fields use the explicit ratios, not an unproved transport. This is a substantial construction, not an elementary isolated fact or a clause of DVR existence.

The normalization node states the final paragraph's canonical construction for a dimension-one local domain and a finite field extension. I opened the 09IG node: it really asserts Noetherian normal dimension-one closure and surjective Spec. I opened integral-closure-finite-extension-normal: it explicitly supplies the given L as fraction field, without separability. I opened localization-normal-domain and dedekind-localization-dvr: they give the embedded localization fraction field and DVR property. The nonzero element t survives in C, makes q nonzero, and the dimension-one chain makes q maximal. The two-case test c in q / c outside q gives the exact contraction. Thus the statement covers every q above the closed point and specifies its actual subring in L; it is not an arbitrary dominating-DVR existence assertion. All original arguments and the appropriate non-elementary citations are preserved above for the next worker, while the delivered child remains statement-only.

Parent step 1 cites only the polynomial-origin node, whose statement explicitly supplies B, K_0, all local hypotheses, the finite degree and contraction. Parent step 2 cites the existing birational-dimension-one node: I read its full statement and checked it preserves K_0, gives a Noetherian local domain of dimension 1 and contracts the maximal ideal to m_B. The nonzero t exists since m_R is nonzero; all inclusions are inside fields, so it stays nonzero. Intersecting the two maximal-ideal equalities is elementary. Parent step 3 cites only the new normalization node: D has dimension 1 and m_D nonzero by step 2, K_0 is its fraction field, and L/K_0 is finite by step 1; every output it uses is a literal clause of that node. Parent step 4 is only the inclusion and contraction chain, plus unpacking the fraction-field conclusion. citations.json uses verbatim statement text for every parent citation. No use of a dependency's proof is hidden in these steps.

I tested r=0 and L=K: P=R, n=m_R and B=R, including finite algebraic extensions with no transcendental generators. For a positive-transcendence example R=Z_(p), L=Q(t), the model is R[t]_(p,t), with fraction field Q(t) and nonzero p in its maximal ideal. The normalization lemma includes the identity extension and nonnormal dimension-one rings (e.g. k[t^2,t^3]_(t^2,t^3)); it does not assume D is already Dedekind. Purely inseparable finite extensions in positive characteristic are allowed: 09IG and the fraction-field input require no separability. A field D and the zero ring are excluded by dimension 1 and the domain hypotheses; a zero prime over m_D is impossible because t survives. No finiteness of C as a D-module, excellence, completeness or separability has slipped into either statement.

I checked delivery-errors B--E against these files: self-contained objects and definition dependencies, single TeX escaping, Stacks tags with labels, exact search records, no duplicate or cycle, strict reduction in work per child, and full hypothesis checks above. There is no parent non-elementary step longer than 2000 characters. The one returned point is repaired by adding two unsplit nodes of comparable workloads and preserving the complete old argument in this handover, rather than merely shortening it.

## Delivery validation

The first server dry run passed at 1901f23c453. A final source-line correction and the Q122 parent search records were added before the final dry run. Local JSON comparisons confirmed the parent statement is verbatim, proof_deps is the union of uses, and every citations.json quote occurs verbatim in its node statement.

## Repair of the promotion return (2026-10-22)

The current return is L's landing refusal: the approved side completion had not been promoted into the live DAG. I retained the delivered three node files, all eight original arguments, the citations and searches. The retained readiness receipt identifies head 5b28aa98602. Against the current read clone the parent differs only in proof, proof_deps, split_report and the additional logged mathlib_searches; its statement, statement dependencies, source, Lean record, audits, reviewer metadata and blueprint provenance agree. Both proposed construction children are still absent from that clone. The required delivery command fetches current origin/sheaf-dag and overlays only split-owned fields, so this retry is built on the current DAG rather than on the old side completion.

I reopened the current statement of every node cited by the four-step assembly. The two retained construction statements still give exactly the outputs used in steps 1 and 3. In particular the polynomial node retains Frac(B)=K_0 and finite L/K_0, and the normalization node retains Frac(A)=L and the contraction to D. The current birational-dimension-one node has itself been split into smaller chart and height-one arguments; its statement still gives a Noetherian local domain D of dimension one inside K_0, with that fraction field and the required contraction. Step 2 uses only that unchanged statement, and its verbatim citation still matches. The nonzero element t in m_R stays nonzero through the inclusions and ensures m_D is nonzero. Step 4 remains the elementary contraction and inclusion calculation. I also reread every definition used by the children and the eight existing ingredient statements retained in the handover above, checking their hypotheses against Tag 00PH and Tags 00P8 and 09IG in algebra.tex. No proof-route or mathematical-statement change is required.

The first dry run in this repair exited with a duplicate-check failure: two newer nodes now also cite 00PH. I opened both complete statements. The affine-DVR-square node adds compatibility of scheme maps to an arbitrary DVR choice, while the nongeneric-point-same-field node selects a geometric trait without changing the function field. Neither gives the polynomial-origin construction or the specified integral closure and all its localizations. I added the four individual comparisons under Not duplicates. This is a substantive current-DAG audit and report repair, not an unchanged re-push. The existing Review by Q122 records the source, hypothesis and small-case checks, and this section extends that signed review to the present landing return. The assembly still has four steps and is below the requested 3000-character limit, with no non-elementary step over 2000 characters. The source and statements have not changed, so the recorded search questions and their actual retained results remain applicable and have not been rerun or invented.

## Continuation of the returned delivery repair

I continued the existing sandbox rather than recreating the delivery. The first required dry run in this continuation exited successfully: `OK (not pushed)` at `b2e761cf107`. It fetched the current server DAG and passed the maintainer preflight. I compared the retained parent to the current read-clone node field by field: only proof, proof_deps, split_report and the additional Q122 mathlib_searches differ. In particular the current Lean and review records, source, statement, statement dependencies and blueprint fields are retained. Neither child exists in the current read clone. This continues the promotion-return repair above; the old eight-step handover and actual search log remain intact.

I reread Stacks 00PH (lemma-exists-dvr), 00P8 (lemma-dominate-by-dimension-1) and 09IG (lemma-integral-closure-Dedekind), including their proofs. I reopened every current definition and ingredient statement used in the retained handover, and the current five-step split of the birational-dimension-one bridge. The bridge statement still asserts a Noetherian local integral domain inside the given field, dimension one, the prescribed fraction field and exact maximal-ideal contraction. Its new internal chart and height-one lemmas are not additional assumptions on its users. I therefore adjusted assembly step 2 to specify the input B, the ambient field K_0 and the name D of the output, and to check the nonfield and fraction-field hypotheses before application. Its two contraction equalities place the same nonzero t in m_D.

For step 3 I now spell out the substitution (D,K,L)=(D,K_0,L), each hypothesis supplied by steps 1 and 2, and the concrete set of fractions inside L supplied by the normalization node. This ensures that the fraction field and contraction statements concern this very subring A. Step 1 is supported by the complete polynomial-origin statement; step 4 only contracts the equality from D to R and unpacks the fraction-field condition. Every use is still a literal clause of its cited statement, so the three citations.json entries remain verbatim and cover every cited node. No extra assertion is taken from a dependency proof.

I reread the 17 retained search-result records, including the two different phrasings for each child, and the recorded Mathlib candidates in DedekindDomain/IntegralClosure.lean, DedekindDomain/Dvr.lean and Valuation/LocalSubring.lean. The available normalization Noetherian theorem assumes an integrally closed base and separability; the DVR-localization theorem assumes Dedekindness already; an arbitrary dominating valuation subring supplies no discreteness. Thus these hits do not give either complete construction as a one-line specialization. The questions and statements have not changed, and I did not repeat or fabricate searches. The Sheaf theorem still has sorry and the finished upstream dominating-DVR theorem does not prescribe its fraction field, so no attachment applies.

The current whole-DAG source-tag search gives the same six existing 00PH/09IG nodes already compared individually under Not duplicates. I also reopened the same-field semilocal normalization and Krull--Akizuki statements: they are reusable ingredients, not either complete construction (the former fixes L=K; the latter gives only Noetherianity). The blueprint tag searches still give zero blueprint matches. I checked the edge cases again: r=0 returns B=R, the identity extension retains the field, nonnormal dimension-one bases are permitted, and inseparable finite extensions require neither module-finite normalization nor separability. The revised assembly is below 3000 characters; each non-elementary step is below 2000. Both new nodes remain statement-only. This paragraph and the hypothesis checks extend my Review by Q122 to the current DAG and the revised applications.


## Final continuation check by Q122

The resumed dry run exited normally with `OK (not pushed)` at `c0f7c005e52`; no interrupted delivery remained active. I compared all parent fields against the current read clone: only proof, proof_deps, split_report and the additional actual search records differ. Both construction children remain absent from that DAG. I read the current dimension-one bridge statement and its five-step split, and reopened all definition and ingredient statements used by the retained eight-step handover. The bridge supplies exactly the prescribed embedded fraction field and contraction used in assembly step 2; its changed internal split adds no hypotheses. The three citation quotes remain verbatim and cover every use in assembly steps 1--3. Step 4 only intersects the maximal-ideal equalities and unpacks the fraction field. The parent statement is verbatim unchanged; the assembly has 1872 characters with step lengths 326, 615, 607 and 324.

I reread algebra.tex at lemma-exists-dvr (00PH), lemma-dominate-by-dimension-1 (00P8) and lemma-integral-closure-Dedekind (09IG), including the proofs. The polynomial-origin construction and the finite normalization construction still follow the first and final paragraphs of 00PH. The latter permits nonnormal D and inseparable L/K; 09IG supplies Noetherianity and dimension one without either extra hypothesis. In Mathlib's recorded candidate sources, the available Noetherian integral-closure theorem assumes an integrally closed base and a separable extension, and the DVR-localization theorem assumes Dedekindness already. Neither states the entire child construction. I read all 17 retained search results and checked that each of the children's 7 and 6 search records occurs in searches.jsonl with the exact tool and query; no search was invented or repeated. The project Sheaf declaration still ends in sorry and the upstream dominating-DVR theorem omits the prescribed fraction field, so attachment remains inapplicable.

The current source-tag scan yields the same six existing nodes individually distinguished under Not duplicates. Repeating the whole-blueprint tag and polynomial-origin searches finds no match; the broader finite-normalization search returns two sheaf-cohomology comparison statements (lem-finrepair-constant-finite-comparison and lemma-weil-pbc-curve-normalization-constant), whose full statements I opened and which assert neither algebraic construction. The ancestor query still gives None and the retained provenance chain is appropriate. The zero-variable, identity-field, nonnormal dimension-one and inseparable cases remain covered as checked in Review by Q122. Both children have empty proof and proof_deps and null proof_origin. No mathematical correction is needed beyond the retained repaired assembly and the current-DAG comparisons. This extends the signed review to the final resumed delivery; the required delivery tool rebases the overlay onto its freshly fetched server DAG.


## Promotion repair revalidation, 2026-10-23

The interrupted turn had no active delivery session. The required first dry run completed normally at 388f5fd61af with server preflight passed. I compared the retained three files with the current shared DAG: the parent still carries the original eight-step proof, both children are absent, and the released stage-1 repair note still requires two new construction nodes. The retained overlay changes only proof, proof_deps, split_report and the additional genuine Mathlib searches. Its statement and statement dependencies agree verbatim with the current parent. The delivery tool fetches origin/sheaf-dag and overlays the split fields on that base, preserving current maintainer metadata; this repairs the side-completion promotion refusal rather than assuming that a side completion landed.

I reopened the full current statements of all three assembly dependencies and every definition used by the children. Step 1 takes the finite-extension local model directly from the polynomial-origin statement. Step 2 uses the current dimension-one bridge with B and K_0; its statement supplies the embedded fraction field and contraction, and the surviving nonzero element of m_R verifies m_D is nonzero. Step 3 substitutes (D,K_0,L) into the normalization statement, using finite degree from step 1 and all local and dimension hypotheses from step 2. Its specified fraction subring is the very A whose fraction field and maximal-ideal contraction are asserted. Step 4 is the intersection calculation. Each of the three citation quotes is still verbatim and every use is covered. I reread the eight existing ingredient statements retained above; none requires an extra hypothesis in the uses recorded there.

I read algebra.tex at 00PH, 00P8 and 09IG, including their proofs, and the recorded Mathlib normalization and DVR-localization candidates. The Noetherian normalization candidate assumes both an integrally closed base and separability, whereas our child assumes neither; the localization candidate starts with Dedekindness. Both retained search phrasings and all 17 actual log results were reviewed without repeating their unchanged questions. The project exact declaration still ends in sorry. The current source-tag and whole-blueprint scans preserve the recorded duplicate distinctions. Small cases r=0, L=K, a nonnormal one-dimensional base and a purely inseparable finite extension remain valid: no module-finite normalization or separability is asserted. There is no statement correction. The 1872-character assembly, its two statement-only children, all old arguments, and the existing signed Review by Q122 are retained. This source and hypothesis reading extends that review to the current delivery base.
