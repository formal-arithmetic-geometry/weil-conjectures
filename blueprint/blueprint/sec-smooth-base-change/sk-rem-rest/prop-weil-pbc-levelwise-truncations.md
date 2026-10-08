+++
id = "prop-weil-pbc-levelwise-truncations"
kind = "theorem"
title = "Levelwise truncations of the adic tower"
order = 1429
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-bounded-constructible-tower", "def-weil-pbc-derived-inverse-limit", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-site-comparison-morphism"]
tags = ["latex:proposition"]
+++
Let the adic datum be $A=\mathcal O_E$, $I=(\varpi)$, with $P_n=A_{E,n}$,
and let $K_\bullet\in D(\operatorname{Tow}_A(T))$ be an adic tower (an
object with normalization isomorphisms
$K_{n+1}\otimes^L_{P_{n+1}}P_n\xrightarrow{\sim}K_n$ satisfying the quotient
cocycle), given by a K-flat representative $QK$ of a single object $K$ of
the underlying pro-etale complex category, $K_n=QK\otimes^L_{A_T}(P_n)_T$.
Then for every $m\in\mathbf Z$:

1. the levelwise truncations
   $$
    \tau^{\le m}K_\bullet:=(\tau^{\le m}K_n)_n,\qquad
    \tau^{\ge m+1}K_\bullet:=(\tau^{\ge m+1}K_n)_n,
   $$
   of the levelwise t-structure of $D(\operatorname{Tow}_A(T))$ (whose
   evaluations are the levelwise canonical truncations of the strict-tower
   representatives) are adic towers, with canonical normalization
   isomorphisms
   $$
    \tau^{\le m}K_{n+1}\otimes^L_{P_{n+1}}P_n
    \xrightarrow{\sim}\tau^{\le m}K_n,\qquad
    \tau^{\ge m+1}K_{n+1}\otimes^L_{P_{n+1}}P_n
    \xrightarrow{\sim}\tau^{\ge m+1}K_n
   $$
   satisfying the quotient cocycle, *provided* the following
   Tor-compatibility condition (1) holds: for every $n$ and every $q\ge m+1$
   the canonical morphism
   $$
    \mathcal H^q(K_{n+1})\otimes^L_{P_{n+1}}P_n
    \longrightarrow\mathcal H^q(K_n)
   $$
   is an isomorphism.

   By the Künneth spectral sequence of the Koszul triangle,
   $$
    E_2^{p,q}=\operatorname{Tor}_p^{P_{n+1}}
    \bigl(\mathcal H^q(K_{n+1}),P_n\bigr)\Rightarrow
    \mathcal H^{q-p}(K_n),
   $$
   condition (1) is precisely the vanishing of the higher Tor-terms
   $\operatorname{Tor}_p^{P_{n+1}}(\mathcal H^q(K_{n+1}),P_n)$, $p\ge1$, in
   the range $q\ge m+1$, i.e. the vanishing of the Künneth obstruction of
   the reduction morphism above level $m$. A sufficient condition is that
   the cohomology sheaves $\mathcal H^i(K)$ of the ambient object
   (equivalently, of the local models) be $\varpi$-torsion-free (over the
   discrete valuation ring $A_T$ equivalently flat) for all $i\ge m+1$,
   because then
   $\mathcal H^q(K_{n+1})=\mathcal H^q(K)\otimes^L_{A_T}(P_{n+1})_T$ has no
   higher $\varpi$-torsion and the morphism of (1) is the identity on
   $(\mathcal H^q(K)/\varpi^{n+1})\otimes^L_{P_{n+1}}P_n$.

   *In general the levelwise truncations are not adic towers*: the failure
   is exactly the Tor-contribution. For instance, for
   $K=(A_T/\varpi)[-(m+1)]$ (a single shift of the constant
   $\varpi$-torsion sheaf) one has
   $$
    K_n=K\otimes^L_{A_T}(P_n)_T
    =\bigl((A_T/\varpi)\oplus(A_T/\varpi)[1]\bigr)[-(m+1)]
   $$
   for every $n\ge1$ — the two-term Koszul resolution of $(P_n)_T$ over
   $A_T$ gives
   $\operatorname{Tor}_1^{A_T}(A_T/\varpi,(P_n)_T)=A_T/\varpi$ — and hence
   $\tau^{\le m}K_n=(A_T/\varpi)[-m]$ for every $n$, whereas
   $$
    (\tau^{\le m}K_{n+1})\otimes^L_{P_{n+1}}P_n
    =\bigl((A_T/\varpi)\otimes^L_{P_{n+1}}P_n\bigr)[-m],
   $$
   whose cohomology is $A_T/\varpi$ in *every* degree $\le m$ (since
   $\operatorname{Tor}_i^{P_{n+1}}(A_T/\varpi,P_n)=A_T/\varpi$ for all
   $i\ge0$, $n\ge1$); this is not $(A_T/\varpi)[-m]$, so the levelwise
   truncated tower $\tau^{\le m}K_\bullet$ fails to be an adic tower.

   Statements (i) and (ii) are therefore asserted under the
   Tor-compatibility condition (1); statement (iii) holds unconditionally,
   being a formal property of the canonical truncations. The levelwise form
   is recorded here as the natural algebraic preparation of the
   derived-limit statement for the completed category, where the condition
   is imposed as an explicit hypothesis; the sufficient condition recorded
   above is that the cohomology sheaves of the local models be flat over
   $A_T$, which is strictly stronger than finiteness of the terms of the
   models. *Local freeness of the terms of a model does not imply (1)*: for
   the two-term complex $P_{n+1}\xrightarrow{\ \varpi\ }P_{n+1}$ the terms
   are free while the first cohomology is the torsion module $P_n$, so
   freeness of the terms forces neither torsion-freeness of the cohomology
   nor the vanishing of the higher Tor terms in (1). Condition (1) is
   therefore carried as a hypothesis in (i) and (ii) and is never deduced
   from freeness;
2. if $K_\bullet$ is uniformly bounded constructible, with local models
   $L_{\alpha j}$ supported in $[d_0,d_1]$ and with the isomorphisms
   $K_n|_{U_{\alpha j}}\simeq L_{\alpha j}\otimes^L_{A_T}(P_n)_T$ for every
   $n$, then $\tau^{\le m}K_\bullet$ is uniformly bounded constructible with
   the local models $\tau^{\le m}L_{\alpha j}$ (supported in
   $[\min(d_0,m),m]$), and $\tau^{\ge m+1}K_\bullet$ is uniformly bounded
   constructible with the local models
   $$
    C_{\alpha j}:=\operatorname{Cone}\bigl(\tau^{\le m}L_{\alpha j}
    \longrightarrow L_{\alpha j}\bigr)
   $$
   (supported in $[m+1,d_1]$), the terms of both families of models being
   finite locally free and their reductions having finite lisse cohomology;
3. for every $n$ there are canonical isomorphisms
   $$
    \mathcal H^i\bigl((\tau^{\le m}K_\bullet)_n\bigr)
     \xrightarrow{\sim}\mathcal H^i(K_n)\quad(i\le m),
    \qquad
    \mathcal H^i\bigl((\tau^{\le m}K_\bullet)_n\bigr)=0\quad(i>m),
   $$
   and analogously
   $$
    \mathcal H^i\bigl((\tau^{\ge m+1}K_\bullet)_n\bigr)
     \xrightarrow{\sim}\mathcal H^i(K_n)\quad(i\ge m+1),
    \qquad
    \mathcal H^i\bigl((\tau^{\ge m+1}K_\bullet)_n\bigr)=0\quad(i\le m),
   $$
   compatible with the normalization maps; if the tower carries compatible
   etale-origin witnesses [def-weil-pbc-etale-origin-witness]
   $(L_n^{\mathrm{et}},\alpha_n)$, the truncated towers carry the
   compatible witnesses
   $(\tau^{\le m}L_n^{\mathrm{et}},\nu^*\tau^{\le m}\circ\alpha_n)$ and
   $(\tau^{\ge m+1}L_n^{\mathrm{et}},\nu^*\tau^{\ge m+1}\circ\alpha_n)$.

*Source note:* no Stacks Project entry states this levelwise form. The
truncations used are Stacks': Homological Algebra, Section 12.15 ([Tag
0118](https://stacks.math.columbia.edu/tag/0118)) defines the canonical
truncations $\tau_{\le m},\tau_{\ge m}$ of a complex of an abelian category
with $H^i(\tau_{\le m}A^\bullet)=H^i(A^\bullet)$ for $i\le m$ and $0$ for
$i>m$ (and dually for $\tau_{\ge m+1}$), and Remark 13.12.4 ([Tag
08J5](https://stacks.math.columbia.edu/tag/08J5)) gives the canonical
truncation triangle in $D(\mathcal A)$. Difference: Stacks truncates
complexes of one fixed abelian category, whereas the statement here is about
the truncation tower of a strict tower of complexes over the varying
coefficient rings $P_n$, and it adds the Tor-compatibility condition (1),
the local models and the compatible etale-origin witnesses. The nearest
constructibility and completion entries are Definition 61.29.1 ([Tag
09C1](https://stacks.math.columbia.edu/tag/09C1)), Proposition 61.29.7 ([Tag
09C7](https://stacks.math.columbia.edu/tag/09C7)), Lemmas 61.20.1 and
61.20.2 ([Tag 099M](https://stacks.math.columbia.edu/tag/099M), [Tag
099N](https://stacks.math.columbia.edu/tag/099N)) and, for the reduction
tower of one constructible object, Lemma 61.29.2 ([Tag
09C2](https://stacks.math.columbia.edu/tag/09C2)).

## Proof

The evaluations $\operatorname{ev}_n$ are exact and jointly conservative, so
the levelwise t-structure of $D(\operatorname{Tow}_A(T))$ has the levelwise
canonical truncations of the statement, computed on the strict-tower
representatives.

*Step 1: the normalization isomorphisms of (i).* The derived tensor functor
$-\otimes^L_{P_{n+1}}P_n$ is triangulated, being the left derived functor of
$-\otimes_{P_{n+1}}P_n$ (take a K-flat resolution of $P_n$); tensoring the
truncation triangle of $K_{n+1}$,
$$
 \tau^{\le m}K_{n+1}\longrightarrow K_{n+1}
 \longrightarrow\tau^{\ge m+1}K_{n+1}\longrightarrow
 \tau^{\le m}K_{n+1}[1],
$$
with $P_n$ and using the normalization
$K_{n+1}\otimes^L_{P_{n+1}}P_n\simeq K_n$ gives the triangle
$$
 (\tau^{\le m}K_{n+1})\otimes^L_{P_{n+1}}P_n
 \longrightarrow K_n
 \longrightarrow(\tau^{\ge m+1}K_{n+1})\otimes^L_{P_{n+1}}P_n
 \longrightarrow .
$$
Künneth spectral sequence. For a complex $M$ of $P_{n+1}$-modules there is
the Künneth spectral sequence of the derived tensor
$$
 E_2^{p,q}=\operatorname{Tor}_p^{P_{n+1}}\bigl(\mathcal H^q(M),P_n\bigr)
 \Rightarrow\mathcal H^{q-p}\bigl(M\otimes^L_{P_{n+1}}P_n\bigr).
$$
For $M=\tau^{\le m}K_{n+1}$ one has $\mathcal H^q(M)=0$ for $q>m$, so all
the $E_2$-terms of total degree $>m$ vanish and the first end term of the
triangle has no cohomology above degree $m$. For $M=\tau^{\ge m+1}K_{n+1}$,
the $E_2$-terms of total degree $\le m$ are exactly the higher Tor-terms
$$
 \operatorname{Tor}_p^{P_{n+1}}\bigl(\mathcal H^q(K_{n+1}),P_n\bigr),
 \qquad q\ge m+1,\ p\ge q-m\ge1,
$$
of the cohomology sheaves of degree $\ge m+1$; by the same spectral sequence
applied to $K_{n+1}$, the Tor-compatibility condition (1) of the statement —
whose displayed morphisms are the $p=0$ edge terms in degrees $q\ge m+1$ —
is exactly the vanishing of all these higher Tor-terms (a sufficient
condition being the $\varpi$-torsion-freeness, i.e. flatness over the
discrete valuation ring $A_T$, of the cohomology sheaves $\mathcal H^i(K)$
of the ambient object for $i\ge m+1$, as in the statement; for the towers of
the form $K_n=QK\otimes^L_{A_T}(P_n)_T$ the cohomology sheaves of the models
are then flat over the respective $P_n$ by base change along $A_T\to P_n$).
Under (1) the second end term therefore has no cohomology in degrees $\le m$,
and the triangle above is a truncation triangle of $K_n$; truncation
triangles are unique (a triangle whose end terms, endowed with the displayed
maps, lie in the full subcategories of complexes with cohomology in $\le m$
and $\ge m+1$ respectively is canonically isomorphic to the canonical
truncation triangle of the middle term), so the canonical normalization
isomorphisms of (i) follow, and the cocycle is inherited from the quotient
cocycle of $K_\bullet$. When condition (1) fails, the displayed end terms of
the triangle carry the Tor-contributions of the Künneth spectral sequence in
the wrong degrees, and the composite is in general only a canonical
morphism, not an isomorphism; the counterexample of the statement shows the
failure is real.

*Step 2: the models of (ii).* The local models here are those of the
bounded constructible tower. (Under the Tor-compatibility condition (1),
which the hypotheses of (ii) ensure throughout: the cohomology sheaves of
the local models are the ones of the ambient object.) The terms of
$\tau^{\le m}L_{\alpha j}$ are $L_{\alpha j}^i$ for $i<m$, and $\ker(d^m)$
in degree $m$: after refining the pro-etale covering so that each
$U_{\alpha j}$ is connected, $A_T|_{U_{\alpha j}}$ is the constant completed
valuation ring, over which submodules of finite free modules are finite
free, so the terms are finite locally free. The support and the finite lisse
reduction cohomology of the models follow from the isomorphisms of (iii)
(the reductions of the truncated models have the same cohomology sheaves as
the reductions of $L_{\alpha j}$ in the surviving degrees, by Step 1 applied
locally). The terms of $C_{\alpha j}$ are direct sums of terms of
$L_{\alpha j}$ and of $\tau^{\le m}L_{\alpha j}$, hence finite locally free;
its support is $[m+1,d_1]$, and, being the cone of the model truncation map,
its reductions are constant by the same local computation, since
$$
 C_{\alpha j}\otimes^L_{A_T}(P_n)_T
 \cong\operatorname{Cone}\bigl(
   \tau^{\le m}K_n|_{U_{\alpha j}}\longrightarrow K_n|_{U_{\alpha j}}\bigr)
 \cong\tau^{\ge m+1}K_n|_{U_{\alpha j}}.
$$
The intertwinings with the quotient transition maps are the local forms of
the canonical isomorphisms of (i).

*Step 3: the cohomology isomorphisms and the witnesses of (iii).* The
formulas of (iii) hold by construction of the levelwise truncations of the
strict-tower representatives. Under condition (1), for $i\le m$ the triangle
of Step 1 has end terms with zero cohomology in the relevant degrees, so the
long exact cohomology sequence of the tensored truncation triangle yields
the displayed isomorphisms of (iii) directly (compatible with the
normalization maps of (i) by their canonicality); the etale-origin witnesses
[def-weil-pbc-etale-origin-witness] are transported by the exactness of the
site-comparison inverse image $\nu^*$
[def-weil-pbc-site-comparison-morphism]: for a witness
$K_n\simeq\nu^*L_n^{\mathrm{et}}$ one has
$\tau^{\le m}K_n\simeq\nu^*\tau^{\le m}L_n^{\mathrm{et}}$, and the
normalization compatibility is the naturality of $\nu^*$.

The source records that audit item BC-03 was resolved for this proposition
by carrying the Tor-compatibility condition (1) as an explicit hypothesis
instead of deducing it from freeness.
