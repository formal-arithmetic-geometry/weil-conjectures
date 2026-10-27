# Worker report: lem-trf-curve-normalization-completion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-curve-normalization-completion.json`: same statement, four-step proof assembly.
- `dag/nodes/sec-trace-formula/lem-trf-nagata-normalization-dvr-branches.json`: statement; unsplit; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-dvr-branch-completion.json`: statement; unsplit; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-birational-normalization-comparison.json`: statement; unsplit; no exact Mathlib match.
- `citations.json`: a verbatim statement quotation for every assembly citation.
- `searches.jsonl`: actual search log; preserved without manual editing.

## Attachments

None. The requested project search for the blueprint id and the normalization/completion notion found no finished project declaration for the item. `lean/Sheaf/TraceFormula/CurveNormalizationCompletion.lean` states the exact theorem as `RingTheory.curve_normalization_completion` but its proof is `sorry`. The relevant existing upstream component tools do not state any of the three complete new lemmas. No Lean source was written or compiled.

## WANTED

None. All sources used are local Stacks source or the supplied blueprint.

## What was wrong and what changed

The returned node carried 7568 characters of proof text across eleven steps, with no parallelizable new work. The sandbox initially contained only dispatcher marker files, no node, report, citations or searches; I copied the current shared item, which has exactly the returned eleven steps and the recorded Lean module. There was no prior sandbox split to discard or log to overwrite. The repair keeps the statement and all maintainer metadata, but distributes the actual work among three new nodes. None is the complete original statement: the first does not discuss completion, the second assumes the finite DVR-branch algebra and does not identify total fraction rings, and the third assumes the scalar extension is already integrally closed and does not prove finiteness of normalization or normality of completion. Each is a general reusable argument, not a restatement of an original clause.

The parent retains the field-to-Nagata argument (old step 1). Node 1 receives old steps 2 and 3 and the localization-to-DVR part of old step 4, approximately 2400 characters of argument. Node 2 receives the completion-to-normal-domain part of old step 4 and old steps 5--7, approximately 1900 characters. Node 3 receives old steps 8--11, approximately 2500 characters. These are comparable work packages, all status unsplit, with no proof steps or proof dependencies. The complete old argument is transcribed below with its citations, so no denominator calculation, prime-chain argument or compatibility assertion is lost. The parent is now 1905 characters, below 3000; no step exceeds 2000 characters.

No statement dispute was found. The current main-20261015 ancestor uses contracting local terms rather than the historical nearby-cycle branch. As the previous report metadata already says, this auxiliary algebra item refines the inherited local normalization input; it neither changes nor replaces the current unit route. I read the chapter, unit and current ancestor, and preserve the full inherited via ancestry. No SGA source is used.

## Unfinished work

The three new argument nodes intentionally have no proofs: independent workers can claim and split each. The complete argument allocation below is the handoff, not an assertion that a Lean proof has been completed. Nothing required for this stage-1 repair is omitted.

## Review by Q72

I read Stacks `varieties.tex`, Tag 0C3S (`lemma-pre-delta-invariant`) and all of Tag 0C3V (`lemma-normalization-same-after-completion`), especially the final product-of-completed-DVRs paragraph. These justify the source and route of the item and all three new nodes. The first new statement isolates the component integral-closure/Dedekind/local-DVR argument; the second is the same final paragraph formulated for an arbitrary injective finite algebra with the required DVR branches; the third makes explicit the finite birational and denominator argument used when the source concludes that a normal finite algebra is the integral closure. The latter two are clearly marked as agent-explicit formulations, not verbatim Stacks statements.

For assembly step 1 I opened all seven cited nodes. `def-weil-pbc-nagata-ring` includes Noetherianness and the prime-quotient N-2 condition; `def-weil-pbc-japanese-domain` says that a finite field extension has finite integral closure. A field has only the ideals 0 and itself, and powers of an algebraic element give the monic equation, so this base case uses no separability hypothesis. `def-weil-pbc-essentially-finite-type-algebra` gives the localization of a finite type algebra, and `def-weil-pbc-finite-type-algebra` gives the polynomial presentation. The three cited stability statements explicitly give polynomial, quotient (not merely arbitrary finite injection), and localization stability. This proves exactly the Noetherian Nagata hypothesis needed next. These three stability lemmas remain generic tools of another unit and retain the existing tool-use justifications.

For assembly step 2 I compared its only citation with the full new statement: it gives finite B and the local DVR property for every prime over the maximal ideal. The hypotheses reduced, local, Nagata, dimension one are precisely the parent hypotheses plus step 1. The identity A subset B subset Q(A) is in the definition of B and is not an extra normality assumption.

For assembly step 3 I compared its only citation with the full new statement: that statement gives flat A to R, reduced Noetherian local R of dimension one, injective R to C, and integral closedness of C in Q(C), as well as the compatible completed-branch product. Its assumptions Noetherian local A of dimension one, finite injective A to B, and DVR local branches all come from the preceding steps; no excellence or geometrically reduced formal fibres have been silently added.

For assembly step 4 the third new statement assumes arbitrary reduced A and R, a flat map, and finite B inside Q(A); all have now been supplied. Its extra integral-closedness hypothesis is applied only after step 3 provides it. Its conclusion explicitly contains both the same-denominator fraction map and the formula on pure tensors; consequently the parent does not replace the canonical map by an unspecified isomorphism. The common-denominator identities in this statement are typed with f(s) in R, and its quotient-ring identification is compatible with C. This quotation is recorded verbatim in citations.json along with every other citation.

I also opened every old cited statement before reallocating its argument. Finitely many minimal primes and the reduced Noetherian total-fractions lemma give the product of fields, not just a definition of Q(A). The domain integral-closure lemma applies with the degree-one extension K_i/K_i and really gives Dedekind. The Dedekind-localization lemma is used only after its prime is proved nonzero and maximal. The finite-extension-completion statement explicitly gives the B- and R-compatible product isomorphism; tensor flip is sufficient for its opposite order. The flat-ring-map definition itself states preservation of injective linear maps, so the tensor-injectivity uses do not rely on an unstated exactness theorem. The completion-dimension statement gives Noetherian-local completion as well as equality of dimensions. Finite-algebra-integrality and finite-algebra-Noetherianness are separate cited tools in the retained argument. The reduced-normal/total-fractions equivalence explicitly has the finite product of normal domains as clause (3), and is used only after reducedness and finite minimal primes have been established.

Small-case review: a field (dimension zero) is excluded from node 1, so no zero maximal prime is incorrectly called a DVR; in a local dimension-one ring every minimal prime is strictly smaller than the maximal ideal. The node 1 argument allows several branches, including the nodal ring k[x,y]_(x,y)/(xy), and uses no perfectness of k. The one-branch example A=B=k[t]_(t) verifies node 2's maps and k[[t]] product with one factor. The finite algebra in node 2 cannot have an empty closed fibre while admitting an injection from this nonzero local ring, and the injection R to C also rules out any empty-product pathology. For node 3 B=A gives the identity even when R has several components; a localization A to R may be nonfaithful without invalidating tensor-injectivity. Every t_h must be regular, not merely nonzero: k[x,y]/(xy) demonstrates why this distinction is necessary. If f(t) were a zero-divisor, tensoring multiplication by t contradicts flatness. The formula for the common denominator remains meaningful for the unit generating family and s=1. No assertion that arbitrary flat maps preserve normality or that arbitrary DVR maps have regular formal fibres has been made.

Against delivery-errors B--E: all objects and notions of each new statement are introduced there, with definition citations or explicit meanings, and no proof sketch is smuggled into a statement. Each new source names its Stacks tag and source label. The whole DAG/blueprint and project Lean were searched before the nodes were created; distinctions from close existing results are below. All Mathlib queries were run through msearch.py with two semantic phrasings per node and their hits read; LeanSearch's rate-limit failures are recorded as unavailable. There are no claimed Mathlib leaves. C1/C4 were checked citation by citation as described above; citations.json uses full verbatim statements rather than bent quotes. All three nodes have only definition statement dependencies and never cite the parent, so the re-split cannot create a cycle. The parent has four genuinely separate steps and is not a one-new-lemma relabelling. The retained proof below contains the explicit prime, product, denominator, multiplicativity, injection and inverse-fraction computations called for by E5.

## Not duplicates

- lem-trf-nagata-normalization-dvr-branches vs lem-trf-curve-normalization-completion: only finite normalization and DVR branches over a Nagata base; no completed ring or normalization comparison.
- lem-trf-nagata-normalization-dvr-branches vs lem-exc-punctured-curve-branches: the existing lemma identifies punctured fields for excellent strictly henselian rings with algebraically closed positive-characteristic residue field; it does not state this new arbitrary Nagata component-normalization and local-DVR result.
- lem-trf-finite-dvr-branch-completion vs lem-trf-curve-normalization-completion: starts from an already finite injective algebra with DVR branches; proves normality of its completed tensor algebra but no identification with the integral closure of the completed base.
- lem-trf-finite-dvr-branch-completion vs lem-exc-punctured-curve-branches: the existing lemma identifies punctured fields for excellent strictly henselian rings with algebraically closed positive-characteristic residue field; it does not state this new injective finite-algebra completion and total-integral-closedness result.
- lem-trf-flat-birational-normalization-comparison vs lem-trf-curve-normalization-completion: arbitrary flat base change criterion with integral closedness as a hypothesis; neither Nagata normalization finiteness nor completion normality is proved.
- lem-trf-flat-birational-normalization-comparison vs lem-exc-punctured-curve-branches: the existing lemma identifies punctured fields for excellent strictly henselian rings with algebraically closed positive-characteristic residue field; it does not state this new arbitrary flat finite-birational scalar-extension criterion and canonical fraction formulas.
- lem-trf-nagata-normalization-dvr-branches vs lem-sc-semilocal-dim-one-normalization: the old node treats one Noetherian domain and semilocality of its normalization; it does not provide the reduced multi-component product, Nagata finiteness over A, or the local-prime factor identification. Its underlying domain Dedekind input is reused in the allocated proof, not duplicated as another standalone domain lemma.
- lem-trf-nagata-normalization-dvr-branches vs lem-sc-integral-closure-dedekind-surjective-fibres: the old node treats a domain in a finite extension and supplies the Dedekind input; it does not identify normalization of a reduced ring as the finite product of those domain normalizations.
- lem-trf-finite-dvr-branch-completion vs lem-weil-pbc-completion-finite-extension: the old node supplies the compatible product but assumes no DVR branches and concludes neither reducedness of the completed base nor total-fraction integral closedness of the tensor algebra. That product theorem is reused in the allocated proof.
- lem-trf-finite-dvr-branch-completion vs lem-weil-pbc-local-nagata-domain-analytically-unramified: that node assumes a Nagata domain and only concludes reduced completion, not a normal finite algebra product. Our finite-algebra hypothesis has no Nagata or domain requirement.
- lem-trf-flat-birational-normalization-comparison vs lem-exc-weakly-etale-normalization-tensor: that node needs a universally catenary local domain and a local weakly etale map; our flat map and reduced rings may fail all these extra conditions, and our conclusion is conditional on the integral closedness of the tensor algebra.
- lem-trf-flat-birational-normalization-comparison vs lem-per-normalization-completion-base-change: that node is a geometric completion theorem under normality off a special fibre, not an arbitrary flat finite-birational fraction-map criterion.
- lem-trf-flat-birational-normalization-comparison vs lem-trf-normalization-completed-product-comparison: the old statement is an intersection test for an element of Frac(A) after passing to complete component quotient fields; it is not a tensor embedding nor a Q(C)=Q(R) comparison.

## Search reading

Whole-DAG searches included tags 0C3S, 0C3V, 07N9, 09IG and normalization/Dedekind/flat-birational/total-fraction concepts. Whole-blueprint queries were normalization, total fraction, DVR, Nagata, birational, completed DVR, 07N9, 0C3S, 0C3V, finite birational, total ring of fractions, normalization of a reduced, product of Dedekind, normalization completion and discrete valuation local. Broad queries had definition and unrelated geometric hits; the more specific queries had zero statement-identical hits. `blueprint_refs.py ancestor` returned lem-trf-local-term-locality. The inherited main-20261015 ancestor source was read in full.

All actual new Mathlib searches are in searches.jsonl and copied, with the exact tool/query and digest, into their own nodes. I read the returned signatures and the plausible source: DedekindDomain/IntegralClosure.lean:220--248; DedekindDomain/Dvr.lean:128; NumberTheory/NumberField/Completion/FinitePlace.lean:60--82; Smooth/IntegralClosure.lean:39--72,161--172,380--390; Algebraic/Integral.lean:505--532; and PicardGroup.lean:921. Domain-only Dedekind, valuation completions, localization comparisons, and inverse invertible-ideal theorems do not specialize in one line to any of the three new statements.

## Full retained argument and ownership

This is the exact pre-repair argument, not a shortened substitute. Its use of the original k-algebra hypotheses supplies valid proofs for the generalized new statements as follows: steps 2--4 use only the reduced local Nagata dimension-one hypotheses of node 1; steps 4 (completion part), 5--7 use only the injective finite algebra, Noetherian local base and DVR-branch hypotheses of node 2; steps 8--11 use only the finite subalgebra of total fractions, flatness and integral closedness hypotheses of node 3. Parent step 1 is retained unchanged. The calculations do not depend on the source of flatness or on a field once those hypotheses have been supplied.

### Old step 1: parent assembly step 1

First $k$ is Nagata directly from the definitions: its ideals are $0,k$, its only prime is $0$, and for every finite field extension $L/k$ the integral closure of $k$ in $L$ is all of $L$, hence a finite $k$-module. Indeed a linear dependence among the powers of an element of $L$, scaled by its nonzero leading coefficient, gives a monic equation. Write $A\cong W^{-1}T$ with $T$ a finite type $k$-algebra, and choose the defining surjection $k[X_1,\ldots,X_n]\twoheadrightarrow T$. Starting from $k$, apply the polynomial-Nagata lemma $n$ times (base case $n=0$); the quotient clause of the finite-over-Nagata lemma gives that $T$ is Nagata, and the localization lemma gives that $A$ is Nagata. In particular $A$ is Noetherian. No perfection or separability assumption on $k$ is used.

Cited statements: def-weil-pbc-nagata-ring, def-weil-pbc-japanese-domain, def-weil-pbc-essentially-finite-type-algebra, def-weil-pbc-finite-type-algebra, lem-weil-pbc-polynomial-nagata, lem-weil-pbc-finite-over-nagata-nagata, lem-weil-pbc-nagata-localization.

### Old step 2: lem-trf-nagata-normalization-dvr-branches

Let $\mathfrak p_1,\ldots,\mathfrak p_t$ be the finitely many minimal primes of $A$. Apply the reduced-Noetherian total-fractions lemma to obtain the canonical isomorphism $Q(A)\cong\prod_i K_i$, where $K_i=A_{\mathfrak p_i}$ is a field and $\mathfrak p_iA_{\mathfrak p_i}=0$. Put $D_i=A/\mathfrak p_i$. The kernel of $A\to K_i$ is exactly $\mathfrak p_i$: one inclusion follows from the displayed vanishing, and if $a/1=0$, some $u\notin\mathfrak p_i$ has $ua=0$, so primality gives $a\in\mathfrak p_i$. Thus $D_i$ embeds in $K_i$; writing elements of $K_i$ as $a/u$ shows that it is its fraction field. Each $D_i$ is a local Noetherian Nagata domain by the quotient clause. Moreover $\dim D_i=1$: the maximal ideal of $A$ is not minimal (otherwise every prime, being contained in it, equals it and $\dim A=0$), so $\mathfrak p_i\subsetneq\mathfrak m$ gives a chain of length one in $D_i$, while any longer chain would lift to one in $A$.

Cited statements: lem-weil-pbc-noetherian-finitely-many-minimal-primes, lem-weil-pbc-reduced-noetherian-total-ring-fractions, lem-weil-pbc-finite-over-nagata-nagata.

### Old step 3: lem-trf-nagata-normalization-dvr-branches

Let $E_i$ be the integral closure of $D_i$ in $K_i$. The Nagata condition says $D_i$ is N-2, and the Japanese-domain definition, with the degree-one extension $K_i/K_i$, says $E_i$ is a finite $D_i$-module. The one-dimensional integral-closure lemma, applied to the Noetherian domain $D_i$, gives that $E_i$ is a Dedekind domain. View $P=\prod_i E_i$ inside $\prod_iK_i=Q(A)$. Finite module generators of the $E_i$, placed in one coordinate at a time, generate $P$ over $A$, since $A\twoheadrightarrow D_i$. Thus $P$ is finite over $A$, so the finite-algebra-is-integral lemma gives $P\subseteq B$. Conversely a monic equation over $A$ for $b\in B$ projects to a monic equation over $D_i$ for its $i$th component, which therefore belongs to $E_i$. Hence $B=P$. This proves that $B$ is finite over $A$ and identifies its factors as Dedekind domains.

Cited statements: def-weil-pbc-nagata-ring, def-weil-pbc-japanese-domain, def-weil-pbc-integral-closure, def-weil-finitely-generated-module, lem-sc-integral-closure-dedekind-surjective-fibres, lem-weil-pbc-finite-algebra-is-integral.

### Old step 4: lem-trf-nagata-normalization-dvr-branches (through DVR localization); lem-trf-finite-dvr-branch-completion (completion and normality)

For a prime $\mathfrak q$ of $B$ lying over $\mathfrak m$, the product description of $B$ selects a single factor $E_i$ and a prime $\mathfrak r$ of it: in the domain $B/\mathfrak q$, each coordinate idempotent is $0$ or $1$, exactly one is $1$, so all the other factors disappear. Consequently $B_{\mathfrak q}\cong(E_i)_{\mathfrak r}$. The contraction of $\mathfrak r$ to $D_i$ is $\mathfrak m/\mathfrak p_i\ne0$, hence $\mathfrak r\ne0$. Since $E_i$ is a one-dimensional domain, a nonzero prime is maximal: $0\subsetneq\mathfrak r\subsetneq\mathfrak r'$ would be a chain of length two. Apply the Dedekind-localization lemma to see that $B_{\mathfrak q}$ is a DVR. Its completion is a DVR by the DVR-completion lemma; the DVR definition gives its principal-ideal-domain property, and the PID-normality lemma makes it a normal domain.

Cited statements: lem-sc-dedekind-localization-dvr, lem-weil-pbc-completion-of-dvr-is-dvr, def-sc-discrete-valuation-ring, lem-weil-pbc-pid-noetherian-normal.

### Old step 5: lem-trf-finite-dvr-branch-completion

Write $R=\widehat A$ and $C=B\otimes_A R$. Apply the finite-extension completion lemma with the Noetherian ring $A$, the finite algebra $B$, and the prime $\mathfrak m$. Since $A$ is local, $A_{\mathfrak m}=A$ (all denominators outside $\mathfrak m$ are units). It gives a finite product decomposition $C\cong\prod_{\mathfrak q\mid\mathfrak m}\widehat{B_{\mathfrak q}}$, using the tensor flip $r\otimes b\mapsto b\otimes r$. The isomorphism is compatible with both the $B$- and $R$-algebra structures. Step 4 shows every factor is a normal domain. Thus $C$ is reduced and is a finite product of normal domains.

Cited statements: lem-weil-pbc-completion-finite-extension, def-weil-module-base-change.

### Old step 6: lem-trf-finite-dvr-branch-completion

The Noetherian completion-flatness lemma and the definition of flatness apply to $A\to R$. Tensoring the injection $A\hookrightarrow B\subset Q(A)$ gives an injection $i:R\hookrightarrow C$, $r\mapsto1\otimes r$. Since $C$ is reduced by step 5, so is $R$: $r^n=0$ implies $i(r)^n=0$, then $i(r)=0$, then $r=0$. The completion-dimension lemma says that $R$ is Noetherian local and $\dim R=\dim A=1$. If $b_1,\ldots,b_h$ generate $B$ over $A$, the elements $b_j\otimes1$ generate $C$ over $R$, by expanding each pure tensor. Therefore $C$ is a finite $R$-module and the finite-algebra-is-integral lemma says it is integral over $R$.

Cited statements: lem-weil-pbc-noetherian-completion-flat, def-weil-pbc-flat-ring-map, lem-weil-pbc-completion-dimension, def-weil-finitely-generated-module, def-weil-module-base-change, lem-weil-pbc-finite-algebra-is-integral.

### Old step 7: lem-trf-finite-dvr-branch-completion

The finite-algebra-Noetherian lemma applies to $R\to C$, so $C$ is Noetherian and hence has finitely many minimal primes. Together with its reducedness and its finite-product-of-normal-domains description in step 5, these are all the hypotheses for the reduced-normal-total-fractions equivalence. Apply implication (3)$\Rightarrow$(2) there: $C$ is integrally closed in $Q(C)$.

Cited statements: lem-weil-pbc-finite-algebra-noetherian, lem-weil-pbc-noetherian-finitely-many-minimal-primes, lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions.

### Old step 8: lem-trf-flat-birational-normalization-comparison

For the chosen finite generators write $b_j=a_j/t_j$ in $Q(A)$, where every $t_j$ is a non-zero-divisor of $A$. Put $s=\prod_jt_j$. Then $s$ is a non-zero-divisor and $sB\subseteq A$: explicitly $sb_j=a_j\prod_{\ell\ne j}t_\ell\in A$, and extend by linearity. Multiplication by $s$ on $B$ is injective because $s$ is invertible in $Q(A)$. Tensor this injection and the injection $s:A\to A$ with the flat $A$-module $R$. Thus multiplication by $s$ is injective on both $C$ and $R$. Here and below $s$ also denotes its image in these rings.

Cited statements: def-weil-finitely-generated-module, def-weil-pbc-flat-ring-map.

### Old step 9: lem-trf-flat-birational-normalization-comparison

The $A$-linear map $d:B\to A$, $b\mapsto sb$, induces $d_R:C\to R$, $d_R(b\otimes r)=(sb)r$. On pure tensors, $i(d_R(c))=sc$ and $d_R(i(r))=sr$, hence these identities hold for every $c,r$. Define $j:C\to R[1/s]$ by $j(c)=d_R(c)/s$. It is additive and sends $1$ to $1$. For multiplication, apply the injective map $i$ to obtain $i(d_R(c)d_R(c'))=s^2cc'=i(s\,d_R(cc'))$, so $d_R(c)d_R(c')=s\,d_R(cc')$, proving multiplicativity of $j$. If $j(c)=0$, some power of $s$ annihilates $d_R(c)$; its regularity on $R$ gives $d_R(c)=0$, hence $sc=0$ and then $c=0$. Also $j(i(r))=r$. We have therefore explicitly embedded $R\subseteq C\subseteq R[1/s]\subseteq Q(R)$.

Cited statements: def-weil-module-base-change.

### Old step 10: lem-trf-flat-birational-normalization-comparison

These embeddings identify $Q(C)$ with $Q(R)$. Indeed if $r\in R$ is a non-zero-divisor and $rc=0$ in $C$, multiply by $s$ to get $r(sc)=0$ in $R$, since $sC\subseteq R$. Thus $sc=0$ and $c=0$, so $r$ remains regular in $C$. Conversely if $t\in C$ is regular, then $st\in R$ is regular on $R$: $(st)r=0$ in $C$ implies $r=0$ by the regularity of $s$ and $t$ on $C$. Hence every fraction $c/t\in Q(C)$ equals $(sc)/(st)\in Q(R)$. The inclusion in the other direction sends $a/r$ to the same fraction in $Q(C)$; these formulas are inverse and agree on $C$.

Cited statements: .

### Old step 11: lem-trf-flat-birational-normalization-comparison

Under this common fraction-ring identification, step 6 makes every element of $C$ integral over $R$. Conversely, an element of $Q(R)=Q(C)$ integral over $R$ satisfies the same monic equation over $C$, so step 7 puts it in $C$. Thus $j$ identifies $C$ with the integral closure of $R$ in $Q(R)$. Finally every non-zero-divisor $t$ of $A$ remains one in $R$, by tensoring the injection $t:A\to A$ with $R$ using flatness. Thus $A\to R$ extends to $\phi:Q(A)\to Q(R)$ with $\phi(a/t)=\bar a/\bar t$. For $b=a/t\in B$, the identity $t(b\otimes1)=a\otimes1$ in $C$ forces $j(b\otimes1)=\bar a/\bar t=\phi(b)$, and $R$-linearity gives $j(b\otimes r)=r\phi(b)$. This proves that the normalization identification is precisely the canonical map with the denominator convention required in the statement.

Cited statements: def-weil-pbc-integral-closure, def-weil-pbc-flat-ring-map.

