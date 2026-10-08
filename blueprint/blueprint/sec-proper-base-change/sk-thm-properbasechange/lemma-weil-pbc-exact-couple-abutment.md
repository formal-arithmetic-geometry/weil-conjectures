+++
id = "lemma-weil-pbc-exact-couple-abutment"
kind = "lemma"
title = "Finite rows and the abutment comparison"
order = 1318
uses = ["def-sp-convergence", "def-weil-pbc-derived-exchange", "def-weil-pbc-hypercohomology-filtrations", "def-weil-pbc-truncation-exact-couples", "lem-sp-couple-morphism", "lemma-weil-pbc-hypercohomology-convergence", "thm-sp-half-plane-convergence"]
+++
In total degree $n$, the two exact couples have only the finite row range
$a\leq q\leq n$. Their induced abutment map is the cohomology map

$$
\mathcal H^n(g^{-1}Rf_*K)\longrightarrow
\mathcal H^n(Rf'_*g'^{-1}K)
$$

of the derived exchange morphism, with the image filtrations of Definition
[def-weil-pbc-hypercohomology-filtrations].

## Proof

On $\mathcal E_1^{p,q}$ one has $p\geq0$ and $q\geq a$. The equality
$p+q=n$ therefore forces $a\leq q\leq n$. On a hypercover total complex,
only these finitely many filtered quotients contribute to degree $n$.
Consequently direct-sum and product totalization agree in that degree, the
filtration is finite and separated, and passage from a finite skeleton to
the full hypercover changes none of its graded terms.

The maps $e_q:A_q\to B_q$ commute with
$\tau_{\leq q}K\to K$. For $q\geq n$, the omitted cohomology sheaves of
$K$ have degrees greater than $n$; after a nonnegative right-derived
functor they cannot contribute to total degree $n$. Hence

$$
\mathcal H^n(A_q)\xrightarrow{\sim}
\mathcal H^n(g^{-1}Rf_*K),\qquad
\mathcal H^n(B_q)\xrightarrow{\sim}
\mathcal H^n(Rf'_*g'^{-1}K).
$$

Under these identifications, $\mathcal H^n(e_q)$ is
$\mathcal H^n(\operatorname{Ex}_{\square,K})$ by naturality of exchange in
the truncation map. Its filtration is the image of
$\mathcal H^n(A_q)$ and maps to the image of $\mathcal H^n(B_q)$, exactly
the two filtrations defined earlier. Thus the exact-couple abutment map is
the specified derived exchange map, rather than an unnamed filtered
isomorphism.

## Detailed form

In total degree $n$, the map on the abutments of the spectral sequences of
[def-weil-pbc-hypercohomology-filtrations] is

$$
 \mathcal H^n(\Ex_{\square,K}):
 g^{-1}\mathcal H^n(Rf_*K)\longrightarrow
 \mathcal H^n(Rf'_*g'^{-1}K),
$$

with the image filtrations of
[def-weil-pbc-truncation-exact-couples].

## Proof

Choose $a$ with $\mathcal H^q(K)=0$ for $q<a$. In both couples of
[def-weil-pbc-truncation-exact-couples], their terms $D^{p,q}$ vanish
for $q<a$, since $\tau_{\leq q}K=0$. The $E_2^{p,q}$ terms vanish for $q<a$
and for $p<0$, the latter because right-derived direct image on a sheaf has no
negative cohomology. Thus the hypotheses of the half-plane convergence theorem
hold for both couples. By the couple-morphism lemma, their morphism induces,
for every $n$, a map of the abutments of the two spectral sequences of
[def-weil-pbc-hypercohomology-filtrations] respecting their filtered
structures. The abutments are $\mathcal H^n(g^{-1}Rf_*K)$ and $\mathcal
H^n(Rf'_*g'^{-1}K)$ with the image filtrations supplied by the truncation
triangles of [def-weil-pbc-truncation-exact-couples]. More
explicitly, the canonical abutment is $D^{0,n}$, and its map is the component
$t_D^{0,n}$, obtained by applying the exchange morphism of
[def-weil-pbc-derived-exchange] to $\tau_{\leq n}K$. Both functors carry
$\tau_{\geq n+1}K$ to complexes with no cohomology in degrees $\leq n$, so the
truncation triangle identifies these $D^{0,n}$ terms with the displayed
degree-$n$ cohomology of the whole complexes. Naturality of exchange in
$\tau_{\leq n}K\to K$ identifies $t_D^{0,n}$ with $\mathcal
H^n(\Ex_{\square,K})$, as required.
