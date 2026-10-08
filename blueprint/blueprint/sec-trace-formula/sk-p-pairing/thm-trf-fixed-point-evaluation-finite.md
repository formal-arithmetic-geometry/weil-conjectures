+++
id = "thm-trf-fixed-point-evaluation-finite"
kind = "theorem"
title = "Stalk traces on a finite etale fixed scheme"
order = 2321
uses = ["def-trf-categorical-trace", "def-trf-coefficient-conventions", "def-trf-fixed-scheme", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-scheme-morphism-properties", "def-weil-site-perfect-complex", "lem-trf-chain-supertrace", "thm-trf-internal-hom-pullback"]
+++
Use the finite coefficient ring
$A=A_{E,n}$. Let $h:X\to X$ be an endomorphism of a
separated finite-type
$k$-scheme and let $K\in D^b_{ctf}(X,A)$ be a
site-perfect complex.
Suppose its fixed scheme
$j:F=\operatorname{Fix}(h)\to X$ is finite etale over $k$.
For the derived internal Hom
there is a natural morphism

$$
\sigma_{h,K}:Lj^*R\mathcal Hom_A(Lh^*K,K)\longrightarrow A_F.
$$

If $u:Lh^*K\to K$ has internal-Hom mate
$\widetilde u:A_X\to R\mathcal Hom_A(Lh^*K,K)$, the value at
$y\in F(k)$ of $\sigma_{h,K}\circ Lj^*\widetilde u$ is

$$
\operatorname{tr}_A(u_y\mid K_y),
$$

the categorical trace of the
endomorphism obtained from $hj=j$. This is a statement about stalk
traces; it does not identify them with Verdier local terms.

## Proof

Put $W=Lj^*K$. A local bounded finite-free representative, as in
[def-weil-site-perfect-complex], pulls back to such a representative
of $W$, so $W$ is site-perfect. The fixed-scheme identity $hj=j$
of [def-trf-fixed-scheme] and
[thm-trf-internal-hom-pullback], applied with first variable
$Lh^*K$, give

$$
Lj^*R\mathcal Hom_A(Lh^*K,K)\simeq R\mathcal Hom_A(W,W).
$$

Since $k$ is algebraically closed, a finite etale $k$-scheme is a
finite disjoint union of copies of $\Spec k$; its sheaf category is
the product of their sheaf categories. On each such component set
$W_y^\vee=R\operatorname{Hom}_A(W_y,A)$.
The tensor–Hom adjunction of [def-weil-derived-tensor] identifies
$R\operatorname{Hom}_A(W_y,W_y)$ with
$W_y\otimes_A^LW_y^\vee$. Compose this identification with the
Koszul symmetry and evaluation to obtain a morphism to $A$.
Their finite product defines $\sigma_{h,K}$.

The mate of $u$, after restriction to $y$, is the mate of $u_y$
by the naturality of the internal-Hom comparison. Under the preceding
tensor–Hom identification it is coevaluation followed by
$u_y\otimes1$. The composite with symmetry and evaluation is
exactly the categorical trace of [def-trf-categorical-trace].
More explicitly, on a bounded finite-projective representative $P$
and a chain representative $v$ of $u_y$, it is
$\sum_i(-1)^i\operatorname{tr}_A(v^i\mid P^i)$, by
[lem-trf-chain-supertrace]. This also proves independence of the
representative and the asserted naturality.
