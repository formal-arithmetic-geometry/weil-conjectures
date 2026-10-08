+++
id = "thm-sc-p1-duality"
kind = "theorem"
title = "Duality on the projective line"
order = 696
uses = ["def-sc-ext-sheaf", "def-sc-kahler-differentials", "def-sc-p1-standard", "lem-pc-projective-space-serre-pairing", "lem-sc-ext-locally-free", "lem-sc-four-lemma", "lem-sc-p1-graded-resolution", "lem-sc-p1-hi-vanishing", "lem-sc-p1-monomial", "lem-sc-p1-twist-exists"]
+++
Let $k$ be an algebraically closed field. For every coherent
$\mathcal O_{\mathbf P^1_k}$-module $\mathcal G$, with

$$
\omega_{\mathbf P^1}:=\Omega^1_{\mathbf P^1_k/k}\cong\mathcal O(-2)
$$

([def-sc-kahler-differentials],
[lem-sc-p1-monomial](iii)), there are canonical isomorphisms

$$
H^1(\mathbf P^1_k,\mathcal G)^{\vee}\;\cong\;
\operatorname{Hom}_{\mathcal O_{\mathbf P^1}}\bigl(\mathcal G,
\omega_{\mathbf P^1}\bigr),
$$

$$
H^0(\mathbf P^1_k,\mathcal G)^{\vee}\;\cong\;
\operatorname{Ext}^1_{\mathbf P^1}\bigl(\mathcal G,
\omega_{\mathbf P^1}\bigr)
$$

(with $\operatorname{Ext}$ of [def-sc-ext-sheaf]; all groups
involved are finite-dimensional, the cohomology of coherent modules
on a proper scheme over a field being finite-dimensional: *Source:
Stacks Project, Cohomology of Schemes, Proposition 30.19.1,
[Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)*).

## Proof

*Step 1: the twisted structure sheaves.* For
$\mathcal E=\bigoplus_j\mathcal O(d_j)$ both statements are
additive in $\mathcal E$, so it suffices to check $\mathcal O(d)$,
$d\in\mathbf Z$. For $\mathcal O(d)$, the Cech computation of
[lem-sc-p1-monomial] gives the monomial duality: with the bases

$$
H^1(\mathbf P^1_k,\mathcal O(d))=\bigoplus_{j=d+1}^{-1}k\cdot[t^{j}],
\qquad
H^0(\mathbf P^1_k,\mathcal O(-2-d))=\bigoplus_{j=d+1}^{-1}k\cdot
x_0^{j-d-1}x_1^{-1-j}
$$

(for $d\leq-2$; both are zero otherwise), the pairing
$\langle[t^{j}],x_0^{j-d-1}x_1^{-1-j}\rangle=1$ is perfect (the case $n=1$, $A=k$ of [lem-pc-projective-space-serre-pairing]), because
the product class is the basis element $[t^{-1}]$ of
$H^1(\mathbf P^1_k,\mathcal O(-2))\cong k$. Hence, for $d\leq-2$,

$$
H^1(\mathbf P^1_k,\mathcal O(d))^{\vee}\cong
H^0(\mathbf P^1_k,\mathcal O(-2-d))
\cong\operatorname{Hom}(\mathcal O(d),\mathcal O(-2))
\cong\operatorname{Hom}(\mathcal O(d),\omega_{\mathbf P^1}),
$$

the second isomorphism being
$\mathcal H om(\mathcal O(d),\mathcal O(-2))=\mathcal O(-2-d)$
for the line bundles of [def-sc-p1-standard], which are
invertible by [lem-sc-p1-twist-exists] (the dual of
$\mathcal O(d)$ is $\mathcal O(-d)$, from the glueing of
[def-sc-p1-standard]), and both sides are zero for $d\geq-1$.
Similarly, by
$\operatorname{Ext}^i(\mathcal F,\mathcal G)=H^i(\mathcal F^{\vee}\otimes\mathcal G)$
for finite locally free $\mathcal F$
([lem-sc-ext-locally-free], the $\operatorname{Ext}$ of
[def-sc-ext-sheaf]):

$$
H^0(\mathbf P^1_k,\mathcal O(d))^{\vee}\cong
H^1(\mathbf P^1_k,\mathcal O(-2-d))\cong
\operatorname{Ext}^1(\mathcal O(d),\omega_{\mathbf P^1})
$$

for all $d$ (for $d\leq-2$ both sides are zero, for $d\geq0$
they have dimension $d+1$ by (i), (ii) of
[lem-sc-p1-monomial]). So Step 1 holds for all $\mathcal E$.

*Step 2: the devissage.* The isomorphisms of Step 1 are
natural, and both pairings defining them (the pairing of the Cech
class with the monomial, and the Yoneda pairing
$\operatorname{Ext}^1(\mathcal G,\omega)\times H^0(\mathcal G)\to \operatorname{Ext}^1(\mathcal O_{\mathbf P^1},\omega) =H^1(\mathbf P^1_k,\omega)\cong k$) are natural in the sheaf and
compatible with the connecting maps of the long exact sequences
(standard homological algebra: the pairings are induced by
compositions in the derived category of $\mathcal O_{\mathbf P^1}$-modules). Fix a coherent $\mathcal G$ and choose a
resolution $0\to\mathcal E_2\to\mathcal E_1\to\mathcal E_0\to \mathcal G\to0$ as in [lem-sc-p1-graded-resolution]; put
$\mathcal K:=\operatorname{coker}(\mathcal E_2\to\mathcal E_1)$,
so that

$$
0\to\mathcal E_2\to\mathcal E_1\to\mathcal K\to0,\qquad
0\to\mathcal K\to\mathcal E_0\to\mathcal G\to0
$$

are exact. For a short exact sequence
$0\to\mathcal A\to\mathcal B\to\mathcal C\to0$ of coherent
modules the cohomology sequence ends with $H^2=0$
([lem-sc-p1-hi-vanishing]), so, dualizing the six-term sequence
(finite-dimensional vector spaces, all finite-dimensional as noted
in the statement),

$$
0\to H^1(\mathcal C)^{\vee}\to H^1(\mathcal B)^{\vee}\to
H^1(\mathcal A)^{\vee}\to H^0(\mathcal C)^{\vee}\to
H^0(\mathcal B)^{\vee}\to H^0(\mathcal A)^{\vee}\to0
$$

is exact; and the long exact Ext sequence, truncated (the groups
$\operatorname{Ext}^i(\mathcal F,\mathcal G)$ for coherent
$\mathcal F$ on the smooth curve $\mathbf P^1_k$ vanish for
$i\geq2$: the Exts are Zariski-local in $\mathcal F$, and the
local rings $\mathcal O_{\mathbf P^1,x}$ are regular of dimension
one, in which every module has projective dimension at most one –
homological algebra), gives the exact sequence

$$
0\to\operatorname{Hom}(\mathcal C,\omega)\to
\operatorname{Hom}(\mathcal B,\omega)\to
\operatorname{Hom}(\mathcal A,\omega)\to
\operatorname{Ext}^1(\mathcal C,\omega)\to
\operatorname{Ext}^1(\mathcal B,\omega)\to
\operatorname{Ext}^1(\mathcal A,\omega)\to0,
$$

$\omega:=\omega_{\mathbf P^1}$. The maps of Step 1 and the
compatibility make the vertical maps of these two exact sequences a
morphism of exact sequences. Applying [lem-sc-four-lemma]
first with $(\mathcal A,\mathcal B,\mathcal C)= (\mathcal E_2,\mathcal E_1,\mathcal K)$ and then with
$(\mathcal A,\mathcal B,\mathcal C)= (\mathcal K,\mathcal E_0,\mathcal G)$ proves the two
isomorphisms of the statement for $\mathcal K$, then for
$\mathcal G$: in both applications the columns $2,3,5,6$ are
isomorphic (Step 1 for the $\mathcal E_i$, and for the second
application the two isomorphisms just proved for $\mathcal K$).
