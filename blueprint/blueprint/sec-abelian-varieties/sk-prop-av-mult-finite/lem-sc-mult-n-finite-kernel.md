+++
id = "lem-sc-mult-n-finite-kernel"
kind = "lemma"
title = "Multiplication by $n$ is finite"
lean = ["AlgebraicGeometry.isFinite_npow_id"]
order = 552
uses = ["def-sc-abelian-variety", "def-sc-group-scheme", "def-sc-mult-n", "lem-sc-abelian-variety-projective", "lem-sc-ample-positive-degree", "lem-sc-ample-tensor", "lem-sc-av-commutative", "lem-sc-mult-n-homomorphism", "lem-sc-mult-n-pullback", "thm-pqf-finite-iff-proper-finite-fibres"]
+++
Let $A$ be an abelian variety
over a field $k$, and let $n\geq1$. Then the map $[n]$ of
[def-sc-mult-n] is a finite homomorphism of
group schemes, and its kernel
$A[n]$ is a finite group scheme over $k$.

## Proof

*Reference: Stacks Project, Groupoid Schemes, Proposition
39.9.11 (3) and (5), [Tag 03RP](https://stacks.math.columbia.edu/tag/03RP), whose proof is Lemma 39.9.8,
[Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG).* We give
the argument of loc. cit. The map $[n]$ of [def-sc-mult-n] is
a homomorphism of group schemes: the group law of $A$ is commutative
by [lem-sc-av-commutative], and for a commutative group scheme the
$n$-fold sum map is a homomorphism by
[lem-sc-mult-n-homomorphism].

*(i) Finiteness of the kernel.* By
[lem-sc-abelian-variety-projective] and
[lem-sc-ample-tensor] there is an ample invertible module
$\mathcal N$ on $A$ with $[-1]^*\mathcal N\cong\mathcal N$,
and by [lem-sc-mult-n-pullback]
$[n]^*\mathcal N\cong\mathcal N^{\otimes n^2}$. Since
[lem-sc-ample-positive-degree] is stated over an algebraically closed
field, we first reduce to that case. Let $\bar k$ be an algebraic
closure of $k$. Then $A_{\bar k}$ is an abelian variety over $\bar k$
($A$ is connected with a rational point, hence geometrically
connected, Stacks Project, Varieties, Lemma 33.7.14,
[Tag 04KV](https://stacks.math.columbia.edu/tag/04KV)), $[n]$
base-changes to $[n]$ of $A_{\bar k}$, the isomorphism
$[n]^*\mathcal N\cong\mathcal N^{\otimes n^2}$ base-changes, and
$\mathcal N_{\bar k}$ is ample (a closed immersion
$A\hookrightarrow\mathbf P^N_k$ with
$\mathcal N^{\otimes m}\cong\mathcal O(1)|_A$ base-changes to one of
$A_{\bar k}$). If all fibres of $[n]_{\bar k}$ are finite, so are those
of $[n]$: the fibre of $[n]$ over $y\in A$ is the image of the fibre of
$[n]_{\bar k}$ over any point $\bar y$ above $y$, the latter being the
base change of the former along $\kappa(y)\subseteq\kappa(\bar y)$, and
such a base change is surjective on points. So assume $k$ algebraically
closed. As the quasi-finite locus of $[n]$ is open and $A$ is
Jacobson, it suffices to treat the fibres over closed points $y$, which
are closed subschemes of $A$. If such a fibre
$[n]^{-1}(y)$ had positive dimension, it would contain a proper
curve $C$ (a positive-dimensional scheme of finite type over a
field contains an integral closed subscheme of dimension one), and
on $C$ the morphism $[n]$ is constant, so
$\mathcal O_C\cong[n]^*\mathcal N|_C\cong\mathcal N^{\otimes n^2}|_C$; but the restriction of an ample module to a closed
subscheme is ample, and an ample module on a proper curve has
positive degree ([lem-sc-ample-positive-degree]), in particular it is not trivial – a
contradiction. Hence every fibre of $[n]$ is finite. The
morphism $[n]$ is proper ($A$ is proper and the target is
separated), so $[n]$ is proper and quasi-finite, hence finite
([thm-pqf-finite-iff-proper-finite-fibres] of the quasi-finite chapter;
*reference: Stacks Project, Cohomology of Schemes,
[Tag 02OG](https://stacks.math.columbia.edu/tag/02OG): proper
and quasi-finite implies finite*). In particular the kernel
$A[n]=[n]^{-1}(e)$ is finite.
