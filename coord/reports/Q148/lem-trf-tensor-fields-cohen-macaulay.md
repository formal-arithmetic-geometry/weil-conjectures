# Repair of lem-trf-tensor-fields-cohen-macaulay — Q148

## Changes and return addressed

The sandbox initially contained only dispatcher marker files, with no node files, report, citations, or earlier search log. I recovered the returned nine-step split from the current read-only repository, compared it with the return's step sizes and Lean module, and retained the statement exactly. Its proof has 7035 characters and the described nine arguments. Existing source, searches, origin, blueprint, Lean, audit, review, and creation metadata are preserved on the item. No repository or launcher files were written and no git, Lean compiler, Lake, or build command was run by the worker.

The return requires distributing all the work, not shortening its description. Three new statement-only unsplit nodes carry distinct arguments. The parent now has four assembly steps, fewer than 3000 proof-text characters. Each child has empty proof and proof_deps and null proof_origin. No child is the whole tensor-fields theorem or a mere clause of it: the first identifies a special intermediate rational base; the second constructs a finite-free reduction without asserting Cohen–Macaulayness; the third is a general finite-flat ascent result with a Cohen–Macaulay base as hypothesis. All are independently assignable. There are three new nodes and zero Mathlib leaves.

## Attachment and source checks

Searched lean/WeilConjectures for the exact blueprint tag, tensor-fields terminology, and Cohen–Macaulay statements, and read lean/Sheaf/RingTheory/TensorFieldsCohenMacaulay.lean. The exact declaration there has a sorry, so no attachment applies. Its hfg disjunction and local depth/dimension conclusion agree with the unchanged item. The rational, finite-free and finite-flat keyword searches of WeilConjectures and Sheaf did not find a finished declaration stating any complete child.

Read Stacks algebra.tex, lemma-tensor-fields-CM (045M), lines 47266–47286: choose a finite extension of a rational function field, tensor to obtain a finite free map, and use the polynomial-localization Cohen–Macaulay base. Also read lemma-finite-flat-over-regular-CM (00R5), lines 27489–27506, including its flat plus dimension-bound alternative; lemma-CM-polynomial-algebra (00ND), lines 25389–25400; fields.tex lemma-transcendence-degree (030F), lines 3398 onward; and lemma-algebraic-finitely-generated (09GH), lines 693 onward. For the expanded ascent argument I read algebra.tex lemma-integral-no-inclusion (00GT), lemma-apply-grothendieck (0337), and lemma-bound-depth (00LK). No source is wanted and no statement dispute or source error was found. The fixed chapter and sk-i-curve-zero route are unchanged. The main-20261015 ancestor lem-trf-local-term-locality is reached through the existing relative-associated specialization chain; this is the same 045M tensor-residue-field input already recorded by the accepted split.

## New nodes and searches

### lem-trf-rational-field-tensor-local-cm

Let $k$ be a field [def-weil-field], let $F/k$ and $L/k$ be field extensions [def-pc-field-extension], and let $r\geq0$ and $t_1,\ldots,t_r\in F$ be algebraically independent over $k$, with $F=k(t_1,\ldots,t_r)$; here this notation means the smallest subfield containing $k$ and these elements, and algebraic independence means that evaluation $k[x_1,\ldots,x_r]\to F$, $x_i\mapsto t_i$, is injective [def-weil-pbc-mv-polynomial-ring]. Put $P=L[x_1,\ldots,x_r]$, let $W\subset P$ be the image of $k[x_1,\ldots,x_r]\setminus\{0\}$ under coefficient inclusion, and put $A=F\otimes_kL$ with the usual algebra tensor multiplication [def-weil-pbc-module-tensor-product]. There is an $L$-algebra isomorphism $W^{-1}P\cong A$ [def-weil-pbc-module-localization] sending $l x^\alpha/w$ to $(t^\alpha/w(t))\otimes l$. The ring $A$ is Noetherian [def-weil-pbc-noetherian-ring], and for every prime $\mathfrak p\subset A$ its localization $A_{\mathfrak p}$ is a Noetherian local ring [def-weil-pbc-localization-at-prime] satisfying $\operatorname{depth}(A_{\mathfrak p})=\dim A_{\mathfrak p}$ [def-weil-pbc-depth; def-weil-pbc-krull-dimension-ring].

Source: Tag 045M (lemma-tensor-fields-CM), last two sentences of the proof: the rational-field tensor base is a localization of a polynomial ring and is Cohen–Macaulay. No complete match: localization and fraction-ring hits cover ingredients only; the prime-local depth equality is absent. MvPolynomial.isLocalization localizes coefficients, rather than asserting this whole rational-field tensor and local Cohen–Macaulay statement. The exact query texts, logged responses/digests and verdicts are in this node and searches.jsonl. Each has leanfinder, loogle, grep and leansearch attempts, with an alternate wording. The ascent LeanSearch attempt was rate-limited and is recorded unavailable, not no match.

### lem-trf-fg-field-tensor-finite-free-reduction

Let $k$ be a field [def-weil-field], let $K/k$ and $L/k$ be field extensions [def-pc-field-extension], and assume $K=k(a_1,\ldots,a_n)$ for finitely many elements of $K$, where this denotes the smallest subfield containing $k$ and these elements. There exist $r\geq0$ and elements $t_1,\ldots,t_r\in K$ forming a transcendence basis [def-weil-pbc-transcendence-basis], a subfield $F=k(t_1,\ldots,t_r)\subset K$, an integer $d\geq1$, and an $F$-basis $e_1,\ldots,e_d$ of $K$ [def-weil-pbc-free-module]. For these choices put $A=F\otimes_kL$ and $T=K\otimes_kL$ with algebra tensor multiplication [def-weil-pbc-module-tensor-product], and give $T$ its $A$-algebra structure by $f\otimes l\mapsto f\otimes l$. The map $A\otimes_FK\to T$, $(f\otimes l)\otimes u\mapsto fu\otimes l$, is an $A$-algebra isomorphism. The map $A^d\to T$, $(c_i)\mapsto\sum_i c_i(e_i\otimes1)$, is an $A$-linear isomorphism. In particular $T$ is finite free over $A$, and $A\to T$ is flat [def-weil-pbc-flat-ring-map] and integral [def-weil-pbc-integral-closure]. No separability hypothesis is imposed.

Source: Tag 045M (lemma-tensor-fields-CM), proof: choose a finite extension of a purely transcendental extension and form its finite free tensor map. No complete match or one-line specialization: finite transcendence basis, finite algebraic extension, tensor reassociation, and finite-free base change must be combined. Module.Free.tensor and Module.Finite.base_change cover only the base-change ingredient; the statement also constructs the rational subfield from finite field generation. The exact query texts, logged responses/digests and verdicts are in this node and searches.jsonl. Each has leanfinder, loogle, grep and leansearch attempts, with an alternate wording. The ascent LeanSearch attempt was rate-limited and is recorded unavailable, not no match.

### lem-trf-finite-flat-algebra-local-cm

Let $A$ be a commutative Noetherian ring [def-weil-pbc-noetherian-ring] such that $\operatorname{depth}(A_{\mathfrak p})=\dim A_{\mathfrak p}$ for every prime ideal $\mathfrak p\subset A$, where prime localizations, depth, and Krull dimension are as in [def-weil-pbc-localization-at-prime; def-weil-pbc-depth; def-weil-pbc-krull-dimension-ring]. Let $\varphi:A\to B$ be a homomorphism of commutative rings such that $B$ is a finite $A$-module [def-weil-finitely-generated-module] and is flat over $A$ [def-weil-pbc-flat-ring-map]. Then $B$ is Noetherian, and for every prime ideal $\mathfrak q\subset B$, writing $\mathfrak p=\varphi^{-1}(\mathfrak q)$, the ring $B_{\mathfrak q}$ is Noetherian local and satisfies $\operatorname{depth}(B_{\mathfrak q})=\dim B_{\mathfrak q}=\dim A_{\mathfrak p}$.

Source: Tag 00R5 (lemma-finite-flat-over-regular-CM), second alternative after prime localization; global finite-flat form used in the proof of Tag 045M (lemma-tensor-fields-CM). No match: going-down, localized flatness, smooth-flatness, and Noetherian dimension hits do not assert the local depth equality for a finite flat algebra. The depth name search returns Lean recursion-depth utilities, not commutative-algebra depth. The exact query texts, logged responses/digests and verdicts are in this node and searches.jsonl. Each has leanfinder, loogle, grep and leansearch attempts, with an alternate wording. The ascent LeanSearch attempt was rate-limited and is recorded unavailable, not no match.

## Work allocation: every original argument retained

The following is the returned proof verbatim, including its uses lists and sources, so no mathematical work is lost. These are handoff arguments in this report, not proofs or proof sketches in the new statement-only nodes. Original step 1 splits between the parent's explicit swap and the finite-free reduction. Original steps 2–4 belong to the rational-base node; steps 1 and 5 and the flat/integral part of 6 to the finite-free node; the Noetherian part of 6 and steps 7–9 to finite-flat ascent. The old field-specific conclusion of step 9 is the parent's last application. The three substantial work packages are approximately 2650, 1970, and 2500 characters of the old proof.

### Original step 1

The swap $K\otimes_kL\longrightarrow L\otimes_kK$, $u\otimes v\mapsto v\otimes u$, is a ring isomorphism with its swap as inverse, by bilinearity and the multiplication in the statement. Thus assume $K=k(a_1,\ldots,a_n)$. Apply [lem-weil-pbc-finitely-generated-field-finite-transcendence-basis] to choose algebraically independent $t_1,\ldots,t_r\in K$ with $K$ algebraic over $F=k(t_1,\ldots,t_r)$. Since $F\subset K$ and $k\subset F$, the original generators also give $K=F(a_1,\ldots,a_n)$. They are algebraic over $F$, so [lem-weil-pbc-algebraic-generators-finite-extension] makes $K$ a finite-dimensional $F$-vector space. Choose a finite $F$-basis $e_1,\ldots,e_d$ of $K$. No assertion of separability is used.

Uses: def-weil-pbc-module-tensor-product, lem-weil-pbc-finitely-generated-field-finite-transcendence-basis, lem-weil-pbc-algebraic-generators-finite-extension.

Source: Tag 045M, lemma-tensor-fields-CM, proof: choose a finite extension of a purely transcendental extension; Fields Tags 030F (lemma-transcendence-degree) and 09GH (lemma-algebraic-finitely-generated).

### Original step 2

Put $B=k[t_1,\ldots,t_r]\subset K$, $W=B\setminus\{0\}$, and $P=L[t_1,\ldots,t_r]$. Algebraic independence identifies $B$ with the polynomial ring on these symbols, and $F=W^{-1}B$: the fractions in $B$ form exactly the smallest subfield containing $k$ and all $t_i$. There is a ring isomorphism $B\otimes_kL\cong P$ sending $t^\alpha\otimes l$ to $lt^\alpha$; its inverse sends $\sum_\alpha l_\alpha t^\alpha$ to $\sum_\alpha t^\alpha\otimes l_\alpha$. The two maps preserve multiplication by the monomial rule and are inverse by bilinearity. Apply [lem-weil-pbc-localization-tensor-over-base] with base $k$, algebra and module $B$, multiplicative set $W$, and module $L$. It identifies
$$A:=F\otimes_kL\cong W^{-1}(B\otimes_kL)\cong W^{-1}P.$$
The localization formula $(b\otimes l)/w\mapsto (b/w)\otimes l$ respects products, since both products multiply the two numerators and the two denominators. Here $W$ in $P$ denotes its image under the coefficient inclusion; no nonzero polynomial in $B$ becomes zero in $P$.

Uses: def-weil-pbc-mv-polynomial-ring, def-weil-pbc-module-tensor-product, lem-weil-pbc-localization-tensor-over-base.

Source: Tag 045M, lemma-tensor-fields-CM, proof: the purely transcendental tensor factor is a localization of a polynomial ring; Tag 00DK (lemma-tensor-localization), with tensor associativity Tag 00D2.

### Original step 3

The field $L$ is Noetherian because its only ideals are $(0)$ and $L$, and its only prime is $(0)$, with localization $L_{(0)}=L$. Its Krull dimension is zero. Its maximal ideal is zero, so its depth is zero: the empty regular sequence exists and a positive-length sequence in that ideal begins with zero, whose multiplication on the nonzero module $L$ is not injective. Therefore $L$ satisfies every hypothesis of [lem-trf-polynomial-algebra-cm]. Applying that node with coefficient ring $L$ and $r$ variables shows that $P$ is Noetherian and that every $P_{\mathfrak r}$ has depth equal to dimension. Since $A=W^{-1}P$, [lem-weil-pbc-localization-noetherian] also shows that $A$ is Noetherian.

Uses: def-weil-pbc-depth, lem-trf-polynomial-algebra-cm, lem-weil-pbc-localization-noetherian.

Source: Tag 045M, lemma-tensor-fields-CM, last sentence, using Tag 00ND (lemma-CM-polynomial-algebra) and Tag 00FN (lemma-Noetherian-permanence).

### Original step 4

Fix a prime $\mathfrak p$ of $A=W^{-1}P$. By [lem-weil-pbc-localization-quotient-by-prime], its contraction $\mathfrak r\subset P$ is prime, avoids $W$, and $\mathfrak p=\mathfrak r A$. The fraction formulas give mutually inverse local ring maps
$$P_{\mathfrak r}\longrightarrow A_{\mathfrak p},\quad f/g\longmapsto(f/1)/(g/1),\qquad
 A_{\mathfrak p}\longrightarrow P_{\mathfrak r},\quad (a/s)/(b/t)\longmapsto at/(sb).$$
In the second formula $s,t\in W$, and $b/t\notin\mathfrak p$ means $b\notin\mathfrak r$; hence $sb\notin\mathfrak r$. The fraction equality relation makes the maps well-defined, and multiplication and cancellation show their composites fix every fraction. Thus $A_{\mathfrak p}$ has the same depth and dimension as $P_{\mathfrak r}$, so is Cohen–Macaulay by step 3. The local-ring assertion is part of [def-weil-pbc-localization-at-prime], and its Noetherianity follows from [lem-weil-pbc-localization-noetherian].

Uses: lem-weil-pbc-localization-quotient-by-prime, def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-noetherian.

Source: Tag 045M, lemma-tensor-fields-CM, localization sentence; Tag 00E3 (lemma-spec-localization) and the fraction construction in Tag 00CO (definition-localization).

### Original step 5

The $A$-algebra $T=K\otimes_kL$ is identified with $A\otimes_FK$ by
$$ (f\otimes l)\otimes u\longmapsto fu\otimes l,\qquad
 u\otimes l\longmapsto(1\otimes l)\otimes u.$$
These formulas are balanced over $k$ and $F$, preserve multiplication, and are mutually inverse on the displayed generators. If $\lambda_i:K\to F$ are the coordinate maps in the basis $(e_i)$ of step 1, the maps
$$A^d\longrightarrow A\otimes_FK,\quad(c_i)\longmapsto\sum_i c_i\otimes e_i,\qquad
 A\otimes_FK\longrightarrow A^d,\quad c\otimes u\longmapsto(c\lambda_i(u))_i$$
are inverse $A$-linear maps: $\lambda_i(e_j)=\delta_{ij}$ checks one composite, and $u=\sum_i\lambda_i(u)e_i$ checks the other. Consequently $T$ is a finite free $A$-module. This construction works for inseparable finite extensions as well.

Uses: def-weil-pbc-module-tensor-product.

Source: Tag 045M, lemma-tensor-fields-CM, proof: the displayed ring map is finite free; the coordinate verification uses the universal property in Tag 00CX (lemma-tensor-product).

### Original step 6

By step 3, $A$ is Noetherian, and step 5 exhibits finitely many $A$-module generators of $T$. Hence [lem-weil-pbc-finite-algebra-noetherian] makes $T$ Noetherian. By [lem-sc-affine-standard-cover-finite-free-local-fp-flat], its finite free $A$-module structure makes $A\to T$ flat. By [lem-weil-pbc-finite-algebra-is-integral], the same finiteness makes $A\to T$ integral. These are statements about the global finite free map, before localization at a prime of $T$.

Uses: lem-weil-pbc-finite-algebra-noetherian, lem-sc-affine-standard-cover-finite-free-local-fp-flat, lem-weil-pbc-finite-algebra-is-integral.

Source: Tag 045M, lemma-tensor-fields-CM, Noetherian and finite-free assertions; Tags 00FN (lemma-Noetherian-permanence), 00NX (lemma-finite-projective), 00GK (lemma-finite-is-integral).

### Original step 7

Let $\mathfrak q\subset T$ be any prime and $\mathfrak p=\mathfrak q\cap A$. Put $R=A_{\mathfrak p}$ and $S=T_{\mathfrak q}$. They are local rings with the displayed prime-generated maximal ideals by [def-weil-pbc-localization-at-prime], and they are Noetherian by [lem-weil-pbc-localization-noetherian] and steps 3 and 6. The map $R\to S$ exists since elements of $A\setminus\mathfrak p$ map outside $\mathfrak q$, hence become units; it is local since $\mathfrak pR$ maps into $\mathfrak qS$. Apply [lem-pc-affine-flat-module-local-criterion] to the flat $A$-module $T$ to conclude that $S$ is flat over $R$. Step 4 gives $\operatorname{depth}R=\dim R$.

Uses: def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-noetherian, lem-pc-affine-flat-module-local-criterion.

Source: Tag 045M, lemma-tensor-fields-CM, application of Tag 00R5 (lemma-finite-flat-over-regular-CM), localized using Tag 00HT (lemma-flat-localization), part (6).

### Original step 8

By [lem-weil-pbc-localization-dimension-chains-below-prime], $\dim S$ is the supremum of the lengths of strict prime chains in $T$ lying below $\mathfrak q$. For any such chain $\mathfrak q_0\subsetneq\cdots\subsetneq\mathfrak q_m\subseteq\mathfrak q$, integrality of $A\to T$ from step 6 and [lem-weil-pbc-integral-incomparability] show that its contractions are a strict prime chain in $A$ lying below $\mathfrak p$. The same dimension-chain node applied to $A,\mathfrak p$ bounds its length by $\dim R$. Taking suprema yields $\dim S\leq\dim R$. This uses incomparability for $A\to T$ itself; it makes no finiteness or integrality claim about $R\to S$.

Uses: lem-weil-pbc-localization-dimension-chains-below-prime, lem-weil-pbc-integral-incomparability.

Source: Tag 045M, lemma-tensor-fields-CM, finite-flat Cohen–Macaulay step; the dimension-bound hypothesis of Tag 00R5 (lemma-finite-flat-over-regular-CM), using Tag 00GT (lemma-integral-no-inclusion) and Tag 00E3 (lemma-spec-localization).

### Original step 9

The map $R\to S$ is flat and local between Noetherian local rings by step 7, so [lem-weil-pbc-flat-local-depth-formula] gives
$$\operatorname{depth}S=\operatorname{depth}R+\operatorname{depth}(S/\mathfrak pRS)\geq\operatorname{depth}R=\dim R.$$
The inequality uses only nonnegativity of depth in [def-weil-pbc-depth]. The ring $S$ is nonzero: $A$ is a nonzero localization of the nonzero polynomial ring $P$, and step 5 makes $T$ finite free of positive rank over $A$, so its prime localization $S$ is nonzero. Apply [lem-weil-pbc-depth-le-support-dimension] to the nonzero finite $S$-module $S$ itself: its support is all of $\operatorname{Spec}S$, because each prime localization has a proper maximal ideal and is nonzero. Thus $\operatorname{depth}S\leq\dim S$. Together with step 8,
$$\dim R\leq\operatorname{depth}S\leq\dim S\leq\dim R.$$
In particular $\operatorname{depth}T_{\mathfrak q}=\dim T_{\mathfrak q}$ for every $\mathfrak q$. This proves the required Cohen–Macaulay assertion, and step 6 already proved Noetherianity. The swap of step 1 handles the case where only $L/k$ is finitely generated.

Uses: lem-weil-pbc-flat-local-depth-formula, def-weil-pbc-depth, lem-weil-pbc-depth-le-support-dimension.

Source: Tag 045M, lemma-tensor-fields-CM, application of Tag 00R5 (lemma-finite-flat-over-regular-CM), with its depth inequality supplied by Tag 0337 (lemma-apply-grothendieck); upper bound Tag 00LK (lemma-bound-depth).

The ascent child replaces the symbols T and A in original steps 6–9 by arbitrary B and A. Its module-finite hypothesis gives B Noetherian and A→B integral by the already cited finite-algebra nodes. At a prime q, both local rings are nonzero because they localize at proper prime ideals; no global nonzero or positive-rank hypothesis is needed. The local map is flat by the existing localized-flatness statement. Contracting strict chains along the global integral map gives dim B_q ≤ dim A_p. The depth formula and the bound for the nonzero finite module B_q give the reverse inequalities, hence both local Cohen–Macaulayness and dimension equality. This keeps every inference of the original argument while removing its unnecessary field-specific nonzeroness explanation in the generalized child. The original explanation remains above.

## Review by Q148

I read the item against 045M and kept its field-finite-generation hypothesis, including the L-only case and inseparable cases. I read 00R5's hypotheses rather than applying its finite-local alternative to a localization where finiteness may fail. The children are self-contained and cite definitions for every non-inline notion: finite field generation is spelled out, rational-field generation and independence are explicit, finite/free modules and flatness are defined by existing nodes, and Cohen–Macaulayness is the displayed local depth equality. Their sources were checked at the labels and tags named above.

For current step 1, def-weil-pbc-module-tensor-product states the bilinear universal property and generation by pure tensors; checking multiplication and swapping twice on those generators proves the ring isomorphism in a few lines. It is the only elementary step. For step 2, the complete statement of lem-trf-fg-field-tensor-finite-free-reduction provides the t_i, rational subfield, positive finite basis, tensor isomorphism, and flat integral A-algebra, exactly as used. Its K/k finite-generation hypothesis is the parent's after the swap; L/k is arbitrary. For step 3, lem-trf-rational-field-tensor-local-cm assumes precisely algebraic independence and F=k(t), both supplied by step 2, and states the localization identification, Noetherianity, and every local depth equality. For step 4, lem-trf-finite-flat-algebra-local-cm assumes a Noetherian base with those equalities and a finite flat algebra, all supplied by steps 2–3; its conclusion supplies every remaining clause for T. citations.json quotes the actual statements verbatim for all four steps; no step relies on a cited node's proof instead of its statement.

I also opened every old proof dependency and read its statement, to check the handoff arguments: the transcendence-basis and algebraic-generators nodes supply just the finite-basis reduction; tensor-localization is a module isomorphism and old step 2 separately checks multiplication; polynomial-algebra-cm supplies the Noetherian polynomial ring and its local depth equality; localization-noetherian and localization-quotient-by-prime supply exactly the localization claims. Finite-algebra-noetherian, finite-free-flat, and finite-algebra-is-integral supply old step 6. The localized-flatness node really states flatness over A_p of the target q-localization. The prime-chain dimension and integral-incomparability statements supply the dimension bound for the global map. Finally the flat-local-depth formula includes a nonzero local closed fibre, and depth-le-support-dimension applies to the finite nonzero regular module. The full support argument is explicit in original step 9. The old three generic off-unit tool uses move into the unsplit ascent child's future proof; the item no longer invokes them directly, and the existing maintainer-owned tool_uses metadata is left untouched.

I checked B1–B10: children have only statements, introduce their own objects, use existing definition nodes, contain single-escaped TeX and verified Stacks labels, and carry genuine logged searches and populated blueprint fields. C1–C8: all non-elementary parent facts are the statements of cited children; every quote matches, all dependencies run downward, and the unit route stays fixed. D1–D5: three distinct intermediate arguments replace nine steps, with the whole old proof retained above, rather than one renamed theorem or a clause-only split. E1–E7: checked every hypothesis and ring map, explicit tensor/fraction formulas, and the global-integrality versus local-flatness distinction.

Edge cases: r=0 makes F=k, W consists of nonzero constants, and the rational node gives A=L with depth and dimension zero. K=k makes d=1. Algebraic inseparable K/k is allowed; for K=L=k(b^(1/p)) in characteristic p the tensor can be nonreduced Artinian, which still has local depth and dimension zero. In the ascent child A=B, or B=A×A, recovers the expected equality, and B=0 gives a vacuous prime-local assertion with a Noetherian zero ring. No injectivity, reducedness, perfectness, or finiteness of A_p→B_q was smuggled into the statement. Every current non-elementary step is under 2000 characters; there is no hidden inline lemma in the assembly.

## Not duplicates

lem-trf-fg-field-tensor-finite-free-reduction vs lem-trf-base-change-residual-fibre-cm: The existing node identifies a scheme residual fibre and asserts its tensor ring is Cohen–Macaulay. It constructs no transcendence basis, rational intermediate subfield, finite field basis, tensor reassociation, or finite-free algebra map, all of which the new node supplies without asserting Cohen–Macaulayness. The existing proof applies the item itself in its last step, so using it here would also be circular.

lem-trf-rational-field-tensor-local-cm vs lem-trf-base-change-residual-fibre-cm: The existing node concerns residual fibres of locally finite type scheme morphisms and their Cohen–Macaulay tensor rings. It gives no polynomial localization isomorphism or formula for monomials divided by nonzero k-polynomials. The new node proves exactly that rational intermediate-base identification and its local consequences, which are input to the item. Even where their Cohen–Macaulay conclusions overlap after constructing a scheme example, the existing proof depends on the item and cannot replace this input without a cycle.

lem-trf-finite-flat-algebra-local-cm vs lem-trf-base-change-residual-fibre-cm: The existing node has field-tensor and scheme hypotheses and gives no dimension equality against a prime-local base. The new node applies to arbitrary finite flat algebras over locally Cohen–Macaulay Noetherian rings, including non-field bases, and gives depth(B_q) = dim(B_q) = dim(A_p). It is a general algebraic ascent input, not the existing geometric application of the item.


lem-trf-rational-field-tensor-local-cm vs lem-trf-tensor-fields-cohen-macaulay: The new node identifies the rational intermediate tensor base and proves its local properties; it assumes F is purely transcendental and does not cover a general finitely generated K or its finite-extension ascent. This is an intermediate ring used together with the other two children, not a clause split.

lem-trf-fg-field-tensor-finite-free-reduction vs lem-trf-tensor-fields-cohen-macaulay: The new node constructs a rational intermediate field and a finite-free tensor map; it makes no Cohen–Macaulay assertion. The item concludes local depth equality for the final field tensor using the separate rational-base and finite-flat-ascent arguments.

lem-trf-finite-flat-algebra-local-cm vs lem-trf-tensor-fields-cohen-macaulay: The new node concerns an arbitrary finite flat algebra over a base already assumed locally Cohen–Macaulay; it does not construct that base or the field-tensor finite-free reduction. The item has neither input ready before its other two children.

Additional keyword candidates were read and ruled out: polynomial-algebra-cm concerns P over a Cohen–Macaulay coefficient ring, not the rational tensor localization; the existing finite-transcendence-basis node supplies only an algebraic residual extension and does not give the tensor finite-free reduction; finite-algebra-noetherian gives no depth equality; the depth formula and integral-incomparability nodes give separate inputs, not finite-flat Cohen–Macaulay ascent. The other whole-DAG keyword hits concern finite free resolutions, punctured finite-flat models, or chains of geometric charts. Blueprint searches for 045M, 00R5, purely transcendental, Cohen-Macaulay, tensor fields, tensor free, and rational localization found no blueprint node stating a child. Their same_as lists are empty. All created ids were checked absent before writing.

## Remaining work and validation

The three children are deliberately unsplit for other workers. No Lean proof is claimed finished, no Mathlib leaf was established, no statement change was needed, and no WANTED source remains. The old direct proof_deps have been replaced by the tensor definition and the three children; their mathematical arguments and original citations remain above for future workers. The required deliver.py --no-push completed with exit 0: OK (not pushed) deliver/Q148/lem-trf-tensor-fields-cohen-macaulay at 8ff80e08f55: preflight passed. The server preflight (including check_dag.py and review_split.py) accepted the repaired parent and all three new nodes. The final direct push reruns preflight on the delivery including this validation note.


## Repair of landing return (2026-10-22)

The single return point is L's landing refusal for head ccc186fecfb: the side-project completion had not been promoted to the live queue DAG. I compared the retained delivered split with returned-item.json and with the current read-only DAG. The current item equals returned-item.json in every field: its nine-step proof is still the old 7035-character proof, not this three-child re-split. The released stage-1 repair note still explicitly orders at least two independently assignable children and assembly text at most 3000 characters. The three child ids remain absent from the current DAG. Thus the repair remains necessary; the old reviewed record is not a reason to discard it.

I rebased through the authorized delivery tool, which fetched the current origin/sheaf-dag and overlaid only the worker-owned stage-1 fields while preserving current maintainer metadata. Its completed dry run on this base printed OK (not pushed) at 6121fbbe069 with preflight passed. I then revised the item's split_report to explain this landing return and to map the four actual assembly steps to the original nine; the prior blueprint summary spoke about the old step numbers without distinguishing them from the assembly.

I re-opened all four assembly citations and every definition cited by the three children in the current DAG. The tensor definition's complete statement still matches the saved citation quote; the other three quotes still exactly match the retained children. None needs a replacement citation or changed hypothesis. The current depth definition covers finite modules and local depth, prime localization defines the local ring, and the transcendence-basis definition provides precisely the independence needed by assembly step 3. Finite and free module definitions justify the terms in the reduction and ascent statements. All are active unmerged ids. I also read the current field-extension Cohen–Macaulay-locus node lem-pur-cohen-macaulay-field-extension: it concerns locally finite-type schemes and does not state any of the three algebraic handoff results or their explicit identifications, so it supplies no replacement for a child.

For the renewed source check I read 045M (lemma-tensor-fields-CM), 00R5 (lemma-finite-flat-over-regular-CM), and 00ND (lemma-CM-polynomial-algebra) in algebra.tex, and re-read the exact incomparability, local-depth formula and depth-bound statements used by the saved ascent argument. The global finite integral map is still the map used for strict contraction of prime chains; no finiteness of the prime-local target over the prime-local base is assumed. Inseparable finite extensions, transcendence rank zero, and the zero finite-flat algebra remain covered. The attachment search still finds only the exact sorry-containing Sheaf statement, not a finished WeilConjectures declaration. Searches already logged were read and reused because neither the children nor their search questions changed. No source, statement or proof route was replaced to overcome the landing refusal.

The only mathematical edits on this retry are the clarified split_report explanation and assembly-to-old-proof map; the complete argument, three statements, citations, search records, and original nine-step handoff text are retained. The final dry run below is required again for these updated delivery contents, followed by the direct push requested in the brief.

## Continuation after transport interruption

The interrupted dry run left a completed stage-1 readiness record for fbd8d347b04. Its old tool session is no longer available and no delivery process for this item remains active. I am running a new sequential dry run to obtain its final result before pushing. I again compared the current item with returned-item.json: they are identical, and all three child ids are still absent from the read clone. I re-read the four assembly citations and all definitions used by the children; all four saved quotation strings remain verbatim. The source checks of 045M, 00R5 and 00ND still justify the rational-base / finite-free-reduction / finite-flat-ascent division. The exact Sheaf declaration still ends in sorry, and the current WeilConjectures search gives no exact finished attachment. I read and reused searches.jsonl because the statements and search questions are unchanged. This continuation retains the previous repair edits to split_report and the full original proof handoff, rather than treating the transport failure as grounds to replace completed work.


## Current-DAG landing repair, 2026-10-23

I continued the retained sandbox rather than reconstructing its split. The first required dry run completed and refused three new same-tag pairs: the live read clone now has lem-trf-base-change-residual-fibre-cm, which cites 045M in addition to its geometric source 05DC. I read that node's entire statement and its proof: its final step applies this item. Its statement gives a scheme residual-fibre identification and the resulting tensor ring's local Cohen–Macaulay property; it does not supply the rational polynomial-localization formula, finite-basis reduction, or general finite-flat ascent with dimension equality. The three pair-specific comparisons above repair this actual new preflight failure. Citing the residual-fibre node as a proof input would create a cycle.

The current item still equals returned-item.json exactly; the sandbox differs only in proof, proof_deps and split_report before this retry. Thus the retained work has not yet landed in the queue's current DAG. I retained its unchanged statement and all current maintainer-owned fields. The released stage-1 repair note still requests at least two statement-only children and at most 3000 characters of assembly. All three retained child ids are absent from the current read clone. The authorized deliver.py tool fetches the current base and creates the rebased delivery; I run no git command myself.

For this retry I read the four assembly citations, all distinct existing statement-definition dependencies of the item and children, and the existing lemma statements supporting every saved old proof step. All four citation quotes are still verbatim, with each step's hypotheses as checked in Review by Q148. None of those statements requires a changed hypothesis or replacement input. The saved search log has been read and reused: no child statement or search question changed. I read 045M, 00R5, 00ND, 00GT, 0337 and 00LK in the current local Stacks algebra.tex. In particular 00R5's flat plus dimension-bound alternative supports the saved ascent, without assuming the prime-local finite algebra map remains finite. The rational isomorphism uses the stated coefficient inclusion and denominators; its rank-zero case is L. The finite-basis argument permits inseparability. For ascent, B = 0 has no primes and the local assertion is vacuous, while B = A and B = A × A give the stated local dimension equality. These checks preserve the existing proof route and all handoff arguments.

The renewed WeilConjectures tag/name/concept search finds no finished declaration proving this item. The exact Sheaf declaration at TensorFieldsCohenMacaulay.lean:79 still has sorry. No Lean file, repository file, launcher file, or search result was modified. Besides the new duplicate analysis in this report, I refreshed the item's split_report to record the current-base comparison and the new residual-fibre dependency check. This is a concrete repair of the current failure, not an unchanged re-push. The renewed dry run and final delivery validate these contents on the fetched current DAG.

The repaired dry run exited 0 with `OK (not pushed) deliver/Q148/lem-trf-tensor-fields-cohen-macaulay at f01a5794d48: preflight passed`. The report now records that completed validation; a final sequential dry run will cover this report note before the authorized push.
