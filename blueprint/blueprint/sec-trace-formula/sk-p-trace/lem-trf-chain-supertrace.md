+++
id = "lem-trf-chain-supertrace"
kind = "lemma"
title = "Chain-level supertrace computation, with explicit conventions"
order = 2303
uses = ["def-trf-categorical-trace", "def-trf-coefficient-conventions"]
+++
Let $A$ be a commutative ring, let
$P^\bullet=(P^i,d^i)_{i\in\mathbf Z}$ be a bounded complex of finite
projective $A$-modules, and let $v:P^\bullet\to P^\bullet$ be a chain
map. On the model category of bounded complexes of finite projective
$A$-modules use the following *strict* symmetric monoidal
structure (the Koszul convention of
the categorical trace):

1. the tensor product of complexes is the total complex of the
double complex $(P^i\otimes_AQ^j)$, with the differential
$d(p\otimes q)=dp\otimes q+(-1)^{|p|}p\otimes dq$, the unit is
$A$ concentrated in degree $0$, and the associator and unit
isomorphisms are the identity maps;
1. the braiding is
$\operatorname{sym}_{P,Q}(p\otimes q)=(-1)^{|p||q|}q\otimes p$;
1. the dual complex $P^\vee$ is
$(P^\vee)^n=\operatorname{Hom}_A(P^{-n},A)$ with the differential
$$
(d^\vee\varphi)(x):=(-1)^{|\varphi|+1}\varphi(dx),
$$
so that $|e^\vee|=-|e|$ for the dual basis element $e^\vee$ of a
basis element $e$;
1. the evaluation and the coevaluation are
$$
\operatorname{ev}_P(\varphi\otimes p):=\varphi(p),\qquad
\operatorname{coev}_P(1):=\sum_{\alpha}e_\alpha\otimes e_\alpha^\vee,
$$
where $(e_\alpha)$ is a basis of the finite projective $A$-module
$\oplus_iP^i$ (the sum is finite because $P^\bullet$ is bounded, and
is independent of the basis).

Then:

1. **(a)** $\operatorname{ev}_P$ and $\operatorname{coev}_P$ are
chain maps of degree $0$;
1. **(b)** the triangle identities hold:
$$
(\operatorname{ev}_P\otimes1)\circ(1\otimes\operatorname{coev}_P)=1_{P^\vee},\qquad
(1\otimes\operatorname{ev}_P)\circ(\operatorname{coev}_P\otimes1)=1_P;
$$
1. **(c)** the categorical
trace of $v$ is the supertrace of its components,
$$
\operatorname{tr}_A(v\mid P)=
\sum_{i\in\mathbf Z}(-1)^i\operatorname{Tr}\bigl(v^i\mid P^i\bigr),
$$
the sum of the ordinary traces of the components; in particular
$\operatorname{tr}_A(\operatorname{id}_P)=\sum_i(-1)^i\operatorname{rank}_AP^i$,
the Euler characteristic.

Consequently the value depends only on the homotopy, hence the
quasi-isomorphism, class of $v$: it is a well-defined function

$$
\operatorname{tr}_A:\operatorname{End}_{D(A)}(P)\longrightarrow A
$$

on the derived category, which is the categorical trace of
Definition
[def-trf-categorical-trace].

## Proof

The conventions being explicit, all four assertions are direct
computations in the model category; by
[def-trf-coefficient-conventions] (and the local projectivity of
a bounded complex of finite projective modules) the derived tensor
products of [def-trf-categorical-trace] are computed by these
strict tensor products, and

$$
\operatorname{End}_{D(A)}(A,A)=
\operatorname{Hom}_{K(A)}(A,A)=\operatorname{Hom}_A(A,A)\cong A
$$

(the only chain maps $A\to A$ are the degree-$0$ scalars, and there
are no homotopies, as $A$ is concentrated in degree $0$), so the
composite of [def-trf-categorical-trace] is an element of $A$.

*Step 1: $\operatorname{ev}_P$ is a chain map of degree $0$.*
For $\varphi\in(P^\vee)^n$ and $p\in P^m$,

$$
\begin{aligned}
\operatorname{ev}\bigl(d(\varphi\otimes p)\bigr)
&=\operatorname{ev}\bigl(d^\vee\varphi\otimes p+(-1)^{|\varphi|}
\varphi\otimes dp\bigr)\\
&=(d^\vee\varphi)(p)+(-1)^{|\varphi|}\varphi(dp)
=(-1)^{|\varphi|+1}\varphi(dp)+(-1)^{|\varphi|}\varphi(dp)=0,
\end{aligned}
$$

and $d\operatorname{ev}(\varphi\otimes p)=0$ since $A$ has zero
differential; the degree count
$|\varphi|+|p|=n+m$ is unchanged, so $\operatorname{ev}_P$ is a
chain map of degree $0$. (By the same computation the dual
differential is a differential: $(d^\vee)^2\varphi(x)= (-1)^{|\varphi|+2}(d^\vee\varphi)(dx)= (-1)^{|\varphi|+2}(-1)^{|\varphi|+1}\varphi(d^2x)=0$.)

*Step 2: $\operatorname{coev}_P$ is a chain map.* Write
$d e_\alpha=\sum_\beta d_{\beta\alpha}e_\beta$ with
$d_{\beta\alpha}=e_\beta^\vee(de_\alpha)$, so that
$d^\vee e_\alpha^\vee=\sum_\beta(-1)^{|e_\alpha^\vee|+1}d_{\alpha\beta} e_\beta^\vee$ by the rule of item (3). Then

$$
\begin{aligned}
d\bigl(\operatorname{coev}_P(1)\bigr)
&=\sum_\alpha\Bigl(de_\alpha\otimes e_\alpha^\vee+
(-1)^{|e_\alpha|}e_\alpha\otimes d^\vee e_\alpha^\vee\Bigr)\\
&=\sum_{\alpha,\beta}d_{\beta\alpha}\,e_\beta\otimes e_\alpha^\vee
+\sum_{\alpha,\beta}
(-1)^{|e_\alpha|}(-1)^{|e_\alpha^\vee|+1}d_{\alpha\beta}\,
e_\alpha\otimes e_\beta^\vee\\
&=\sum_{\alpha,\beta}\Bigl(d_{\alpha\beta}
+(-1)^{|\alpha|+(-|\alpha|)+1}d_{\alpha\beta}\Bigr)
e_\alpha\otimes e_\beta^\vee=0,
\end{aligned}
$$

where in the last line the summation indices of the first sum were
swapped ($\alpha\leftrightarrow\beta$) and the identities
$|e_\alpha^\vee|=-|e_\alpha|$ and
$(-1)^{|\alpha|-|\alpha|+1}=-1$ were used. Hence
$\operatorname{coev}_P$ is a chain map of degree $0$.

*Step 3: the triangle identities.* The associator and the unit
isomorphisms are the identity maps, so

$$
\begin{aligned}
(\operatorname{ev}_P\otimes1_P)(1_{P^\vee}\otimes
\operatorname{coev}_P)(\psi)
&=\sum_\alpha
\operatorname{ev}_P(\psi\otimes e_\alpha)\,e_\alpha^\vee
=\sum_\alpha\psi(e_\alpha)e_\alpha^\vee=\psi,\\
(1_P\otimes\operatorname{ev}_P)(\operatorname{coev}_P\otimes1_P)(p)
&=\sum_\alpha
e_\alpha\,\operatorname{ev}_P(e_\alpha^\vee\otimes p)
=\sum_\alpha e_\alpha\,e_\alpha^\vee(p)=p,
\end{aligned}
$$

for all $p\in\oplus_iP^i$ and $\psi\in\oplus_i(P^\vee)^i$; both
identities are degreewise and are the two triangle identities (a)
and (b) of the statement. (The braiding $\operatorname{sym}$ is
not used in these two identities; it is the Koszul sign
$(-1)^{|p||q|}$ that produces the alternating signs in Step 4.)

*Step 4: the trace of the composite.* Let
$(e_{i,a})_{a}$ be a basis of $P^i$ for each $i$ and
$e_{i,a}^\vee$ the dual basis of $(P^\vee)^{-i}$ (so
$|e_{i,a}^\vee|=-i$). The composite of
[def-trf-categorical-trace] is

$$
\begin{aligned}
1&\longmapsto\sum_{i,a}e_{i,a}\otimes e_{i,a}^\vee
\longmapsto\sum_{i,a}v\,e_{i,a}\otimes e_{i,a}^\vee\\
&\longmapsto\sum_{i,a}(-1)^{|v e_{i,a}||e_{i,a}^\vee|}
e_{i,a}^\vee\otimes v\,e_{i,a}
=\sum_{i,a}(-1)^{i(-i)}e_{i,a}^\vee\otimes v\,e_{i,a}\\
&\longmapsto\sum_{i,a}(-1)^{i(-i)}e_{i,a}^\vee(v\,e_{i,a})
=\sum_{i,a}(-1)^i e_{i,a}^\vee(v^i e_{i,a})
=\sum_i(-1)^i\operatorname{Tr}(v^i\mid P^i),
\end{aligned}
$$

because $i(-i)=-i^2\equiv i^2\equiv i\pmod 2$, so
$(-1)^{i(-i)}=(-1)^i$. This is (c). (The second arrow uses that
$v$ is a chain map of degree $0$, whence
$|v\,e_{i,a}|=i$.)

*Step 5: independence of the representative.* The sum of Step 4
is visibly independent of the chosen bases (a change of basis
$e'_\alpha=\sum_\beta c_{\alpha\beta}e_\beta$ with inverse matrix $c^{-1}$
substitutes $\sum e'_\alpha\otimes e'^\vee_\alpha=\sum e_\alpha\otimes e_\alpha^\vee$, as $\sum_\alpha c_{\alpha\beta} (c^{-1})_{\gamma\alpha}=\delta_{\beta\gamma}$). It is invariant under
homotopy: if $v-v'=ds+sd$ with $s:P^i\to P^{i-1}$ of degree $-1$,
then, using the cyclicity of the trace,

$$
\begin{aligned}
&\sum_i(-1)^i\operatorname{Tr}(d^{i-1}s^i\mid P^i)
+\sum_i(-1)^i\operatorname{Tr}(s^{i+1}d^i\mid P^i)\\
&=\sum_i(-1)^i\operatorname{Tr}(d^{i-1}s^i)
-\sum_i(-1)^{i-1}\operatorname{Tr}\bigl(s^{i}d^{i-1}\bigr)=0,
\end{aligned}
$$

the two sums cancelling term by term after the index shift
$i\mapsto i+1$ in the second. Hence $\operatorname{tr}_A(v\mid P)$
depends only on the homotopy class, i.e. on the morphism
$v\in\operatorname{End}_{D(A)}(P)$; this is precisely the value of the
composite of [def-trf-categorical-trace] (its tensor products are
the strict ones of this model, its
$\operatorname{coev}_P,\operatorname{ev}_P$ the maps of steps 1–3,
and $\operatorname{End}_{D(A)}(A)\cong A$), so the derived-level
categorical trace of a quasi-isomorphism class of endomorphisms equals
the supertrace of any projective representative, as stated.
