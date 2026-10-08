+++
id = "cor-mg-central-determinant-weight"
kind = "theorem"
title = "Central element determines the determinant weight"
order = 2557
tags = ["latex:corollary"]
uses = ["d-weights", "def-wf-arithmetic-monodromy-extension", "def-wf-degree-components", "def-wf-monodromy-data", "def-wf-weil-category", "lem-mg-degree-component-functoriality", "lem-mg-determinant-monodromy-morphism", "lem-wf-rank-one-algebraic-extension", "lem-wf-schur-scalar"]
+++
Let $X_0$ be a normal geometrically connected curve over $k_0$, put
$|k_0|=q$, and fix a real weight character $\lambda$ ([d-weights]). Let
$\rho:W(X_0)\to\operatorname{GL}(V)$ be the representation of a lisse
Weil sheaf, with the monodromy data of [def-wf-monodromy-data], computed
with one fixed degree-one element $s$, and let
$z=(h,m)\in G^{[m]}(\Qlb)$ be an algebraic-monodromy element of positive
degree $m$ which is central in $G_{\mathrm{arith}}(\rho)$ (an element
furnished by [lem-mg-common-positive-central-element] when $\rho$ is
semisimple). Let $Q\neq0$ be a Weil-stable subquotient of $V$, or more
generally any of the tensor, exterior-power or iterated-subquotient
constructions of [lem-mg-degree-component-functoriality], of rank $r$,
with Weil representation $\rho_Q$, with finite geometric determinant,
i.e. $\det\rho_Q(\pi_1(X))$ finite, and with the homomorphism
$\Phi_Q:G_{\mathrm{arith}}(\rho)\to G_{\mathrm{arith}}(\rho_Q)$ of that
lemma. The representation $Q$ need not be irreducible or semisimple.
Say that $z$ *acts on $Q$ as a scalar* $c_Q\in\Qlb^\times$ if the matrix
of $\Phi_Q(z)$ under the matrix map $(h',n)\mapsto h'\rho_Q(s)^n$ of
[def-wf-arithmetic-monodromy-extension] is $c_Q\,1_Q$. If $z$ acts on
$Q$ as a scalar $c_Q$, then

$$
\dw_\lambda(Q)=\frac{\lambda(c_Q)}{m}.
$$

The scalar-action hypothesis holds whenever $Q$ is Weil-irreducible.
In particular, for an irreducible lisse Weil sheaf $\mathcal W_0$ of rank
$r$ with representation $\rho_{\mathcal W}$ and finite geometric
determinant, and $z\in G^{[m]}$ central in
$G_{\mathrm{arith}}(\rho_{\mathcal W})$ (the case $V=Q$, $\Phi_Q$ the
identity), $z$ acts by a scalar $c_W$ and

$$
\dw_\lambda(\mathcal W_0)=\frac{\lambda(c_W)}{m};
$$

for $\lambda=\lambda_\iota$ this reads

$$
\frac{2\log_q|\iota(\det\rho_{\mathcal W}(s))|}{r}=\frac{2\log_q|\iota(c_W)|}{m},
$$

where $\log_q$ is the base-$q$ logarithm. The determinant weight
$\dw_\lambda(Q)$ does not depend on the degree-one element used to
define it in [d-weights].

## Proof

*The matrix map is a homomorphism.* For $(h',n),(h'',p)$ in
$G_{\mathrm{arith}}(\rho_Q)$, the product
$(h'\alpha^n(h''),n+p)$ of [def-wf-arithmetic-monodromy-extension] has
matrix
$h'\rho_Q(s)^nh''\rho_Q(s)^{-n}\rho_Q(s)^{n+p}
=(h'\rho_Q(s)^n)(h''\rho_Q(s)^p)$. If $w\in W(X_0)$ has degree $n$,
then $ws^{-n}\in\pi_1(X)$, so $(\rho_Q(ws^{-n}),n)$ lies in
$G_{\mathrm{arith}}(\rho_Q)$ and its matrix is $\rho_Q(w)$.

*The general scalar case.* Let
$\chi_{\det}=\det\circ\rho_Q:W(X_0)\to\Qlb^\times$ be the character of
the determinant line of $Q$, and put $c=\chi_{\det}(s)$. Write
$\Phi_Q(z)=(h_Q,m)$ with $h_Q\in H_{\mathrm{geom}}(\rho_Q)$; the degree
is $m$ because $\Phi_Q$ preserves degrees
([lem-mg-degree-component-functoriality]). By hypothesis its matrix is
$h_Q\rho_Q(s)^m=c_Q1_Q$, and taking determinants on the $r$-dimensional
space $Q$ gives

$$
c_Q^r=\det(h_Q)\,c^m .
$$

The morphism $\Delta_{\rho_Q}$ of
[lem-mg-determinant-monodromy-morphism] sends $\Phi_Q(z)$ to
$(\det h_Q,m)$ in the arithmetic monodromy group of the rank-one
determinant line. The group $A=\chi_{\det}(\pi_1(X))$ is finite by
hypothesis, so [lem-wf-rank-one-algebraic-extension] applies: in the
notation of [def-wf-degree-components],
$H_{\mathrm{geom}}(\chi_{\det})=A$ and
$G_{\mathrm{arith}}(\chi_{\det})=A\times\mathbf Z$, so
$a:=\det h_Q\in A$. The element $a$ has finite order, and a real weight
character kills finite-order elements: if $a^e=1$ with $e>0$, then
$e\lambda(a)=\lambda(a^e)=0$. Applying $\lambda$ therefore gives
$r\lambda(c_Q)=m\lambda(c)$, that is,

$$
\frac{\lambda(c_Q)}{m}=\frac{\lambda(c)}{r}=\dw_\lambda(Q)
$$

by the definition in [d-weights]. Only the scalar action of $z$ on $Q$
was used here, not the irreducibility or semisimplicity of $Q$.

*Irreducible $Q$.* By [lem-mg-degree-component-functoriality],
$\Phi_Q(z)$ is central in $G_{\mathrm{arith}}(\rho_Q)$. By the first
paragraph its matrix commutes with the matrix $\rho_Q(w)$ of every
$(\rho_Q(ws^{-n}),n)$, i.e. with the whole Weil-group image. If $Q$ is
Weil-irreducible, [lem-wf-schur-scalar] makes this matrix a scalar
$c_Q$, nonzero because the matrix is invertible. Taking $V=Q$ and
$\Phi_Q$ the identity gives the stated case of $\mathcal W_0$, and the
case $\lambda=\lambda_\iota$ is the last display.

*Independence of the lift.* Replacing the degree-one element by $us$
with $u\in\pi_1(X)$ multiplies $\chi_{\det}(s)$ by the finite-order
element $\chi_{\det}(u)\in A$, which $\lambda$ kills; so
$\dw_\lambda(Q)$ does not depend on the degree-one lift.
