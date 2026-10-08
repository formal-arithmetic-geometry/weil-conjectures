+++
id = "prop-trf-pairing-local-decomposition"
kind = "theorem"
title = "Decomposition of the pairing into local terms"
order = 2349
tags = ["latex:proposition"]
uses = ["def-trf-correspondence-between-pairs", "def-trf-dualizing-complex", "def-trf-integration", "def-trf-local-term", "def-trf-local-term-pair", "def-trf-supported-pairing", "lem-trf-integration-component-sum", "lem-trf-trace-class-diagonal-pairing", "prop-trf-pairing-point-normalization"]
+++
Let $(C,c,u)$, $(D,d,v)$ be an opposite pair of cohomological
correspondences as in [def-trf-supported-pairing], with intersection
support $E=E(C,D)$ (the fiber product of the two supports of
[def-trf-correspondence-between-pairs]) and Borel–Moore section
$\langle u,v\rangle_{\mathrm{LV}}:A_E\to\omega_{E,A}$. Suppose that
$E$ is a finite disjoint union

$$
E=\coprod_{\beta\in B}\beta
$$

of open-and-closed subschemes $j_\beta:\beta\hookrightarrow E$, each
proper over $s$. For $\beta\in B$ let
$\langle u,v\rangle_{\mathrm{LV}}|_\beta:=j_\beta^*\langle u,v\rangle_{\mathrm{LV}}:A_\beta\to\omega_{\beta,A}$
be the restricted pairing and

$$
\LT_\beta(u,v)=\int_\beta\bigl(\langle u,v\rangle_{\mathrm{LV}}|_\beta\bigr)\in A
$$

the local term of the pair on $\beta$, both as in
[def-trf-local-term-pair]; the restricted pairing is the restriction
of [lem-trf-integration-component-sum] (both are the composite
$A_\beta\simeq Lj_\beta^*A_E\to Lj_\beta^*\omega_{E,A}\cong\omega_{\beta,A}$),
and for $v=1_K$ and $\beta\subseteq\Fix(c)$ the local term is
$\LT_\beta(u)$ of [def-trf-local-term]. Then $E$ is proper over $s$ and

$$
\int_E\langle u,v\rangle_{\mathrm{LV}}
=\sum_{\beta\in B}\LT_\beta(u,v).
$$

If $E=\emptyset$ both sides are $0$. Moreover, for a perfect
$A$-complex $P$ on $s$ and an endomorphism $w:P\to P$, regarded as an
endocorrespondence with support $s$ (whose sole component is $s$),

$$
\LT_s(w)=\LT_s(w,1_P)=\tr_A(w\mid P).
$$

## Proof

Apply [lem-trf-integration-component-sum] to $T=E$, the finite
decomposition $E=\coprod_{\beta\in B}\beta$ and
$\tau=\langle u,v\rangle_{\mathrm{LV}}$: it shows that $E$ is proper
over $s$, so that $\int_E$ of [def-trf-integration] is defined, and
that

$$
\int_E\langle u,v\rangle_{\mathrm{LV}}
=\sum_{\beta\in B}\int_\beta\bigl(\langle u,v\rangle_{\mathrm{LV}}|_\beta\bigr)
=\sum_{\beta\in B}\LT_\beta(u,v),
$$

the last equality being the definition of the local terms in
[def-trf-local-term-pair]; for
$E=\emptyset$ the lemma gives $0=0$. When $v=1_K$, so that
$\langle u,1_K\rangle_{\mathrm{LV}}=\Tr_c(u)$ by
[lem-trf-trace-class-diagonal-pairing], the restriction to a component
$\beta\subseteq\Fix(c)$ is the composite used in [def-trf-local-term],
whence $\LT_\beta(u,1_K)=\LT_\beta(u)$, as also recorded in
[def-trf-local-term-pair].

For the point case, $E=s$, $B=\{s\}$, and $j_s$ and the structure map
$a_s$ are identities. Then $\omega_{s,A}=Ra_s^!A=A$ by
[def-trf-dualizing-complex], the restriction to the sole component is
the section itself, and both adjunction maps in [def-trf-integration]
(the unit of $La_s^*\dashv Ra_{s*}$ and the counit of
$Ra_{s!}\dashv Ra_s^!$) are identities, so $\int_s$ is the
identification $\Hom_{D(s,A)}(A,A)=A$. Hence
$\LT_s(w,1_P)=\langle w,1_P\rangle_{\mathrm{LV}}$, which equals
$\tr_A(1_P\circ w\mid P)=\tr_A(w\mid P)$ by the point normalization
[prop-trf-pairing-point-normalization].
