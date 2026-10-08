+++
id = "lem-weil-derived-limit-existence"
kind = "lemma"
title = "Existence and computation of derived limits"
order = 1208
uses = ["def-weil-derived-limit"]
+++
Let $\mathcal D$ be a triangulated category and let $(K_n,f_n)$ be an inverse
system of objects of $\mathcal D$.

1. If $\prod_nK_n$ exists in $\mathcal D$, then a derived limit
   [def-weil-derived-limit] $R\varprojlim_nK_n$ exists, and any two derived
   limits of the system are isomorphic, although not canonically so.
2. Let $\mathcal A$ be an abelian category with exact countable products and
   let $\mathcal D=D(\mathcal A)$. Then countable products exist in $\mathcal
   D$, are represented by termwise products of any representatives, and
   satisfy $H^p\bigl(\prod_iK_i\bigr)\cong\prod_iH^p(K_i)$ for all $p$.
3. In the situation of (2), assume in addition that $\mathcal A$ has enough
   injectives. If $I_\bullet$ is a K-injective representative, in the abelian
   category of towers in $\mathcal A$, of the system $(K_n,f_n)$, then
   $\varprojlim_nI_n$ represents $R\varprojlim_nK_n$. Consequently "choosing
   a K-injective replacement of the tower" and "taking the first term of the
   Roos triangle" [def-weil-derived-limit] produce isomorphic objects.

## Proof

Assertion (1) is axiom TR1 applied to the defining triangle of
[def-weil-derived-limit], together with TR3 for the uniqueness of a cone;
this is Definition 13.34.1 of the Stacks Project, Tag
[08TC](https://stacks.math.columbia.edu/tag/08TC) and the remarks following
it, and it also explains why a derived limit is determined only up to a
non-unique isomorphism. Assertion (2) is Lemma 13.34.2 of the Stacks Project,
Tag [07KC](https://stacks.math.columbia.edu/tag/07KC): since countable
products are exact in $\mathcal A$, the termwise product of representatives
represents the product in $D(\mathcal A)$, and its cohomology is the product
of the cohomologies. Assertion (3) is the K-injective presentation of the
right derived functor of $\varprojlim$. The Stacks Project form of the model
statement is Lemma 13.34.6, Tag
[070M](https://stacks.math.columbia.edu/tag/070M), which treats the
truncation tower $I_n$ built from a single complex $K^\bullet$ by the
construction of Lemma 13.29.3 and concludes that $\varprojlim_nI_n$ exists,
is K-injective, and represents $R\varprojlim_n\tau_{\ge-n}K^\bullet$; the
general-tower form used here is the same argument applied to a K-injective
replacement of the given tower. Its inputs are that a product of K-injective
complexes is K-injective (Tag
[0BK6](https://stacks.math.columbia.edu/tag/0BK6), Lemma 13.31.5, stated
there without a bounded-below hypothesis, only that the termwise products
exist) and that every complex of the ambient category admits a K-injective
resolution: for a Grothendieck abelian category this is Tag
[079P](https://stacks.math.columbia.edu/tag/079P), Theorem 19.12.6, and the
ambient categories occurring in this blueprint are categories of sheaves of
modules, which are Grothendieck; the general form for an abelian category
with exact countable products and enough injectives is Spaltenstein's
theorem. The existence of the products used is Lemma 13.34.3, Tag
[0BK7](https://stacks.math.columbia.edu/tag/0BK7).
