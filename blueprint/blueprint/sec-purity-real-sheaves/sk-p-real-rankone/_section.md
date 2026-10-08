+++
id = "sk-p-real-rankone"
kind = "section"
title = "Purity of rank-one Weil sheaves"
order = 2617
uses = ["sk-d-real-jacobian", "sk-d-real-log", "sk-d-real-setup", "sk-d-real-weights", "sk-d-real-weil", "sk-def-av-jacobian", "sk-def-av-pic", "sk-i-real-compactification", "sk-i-real-sheaves", "sk-lem-finite", "sk-p-rankone", "sk-p-real-integral", "sk-p-real-operations", "sk-prop-hilbert90", "sk-prop-jacobian-descent", "sk-prop-sf-open-closed-triangle", "sk-thm-av-final", "sk-thm-derived-duality", "sk-thm-frobenius"]
lean = ["AlgebraicGeometry.WeilGroup.IsLisse.finite_geometric_image", "AlgebraicGeometry.WeilGroup.IsLisse.isPunctuallyPure_of_finrank_eq_one"]
+++
*Proposition (sketch).*

Let $L$ be a rank-one lisse Weil sheaf on a
smooth geometrically connected curve $U_0/\Fq$,
with character $\chi:W(U_0)\to E^\times$ under [sk-i-real-sheaves].
Its geometric image $\chi(\pi_1(U))$ is finite, so the rank-one
factorization of [sk-p-rankone] applies. Consequently $L$ is
punctually $\iota$-pure of weight
$w=2\log|\iota(c)|/\log q$, where $c=\chi(\gamma)$ for any degree-one
lift $\gamma$.

## Proof

*Proper curves.*
Choose a completion with [sk-i-real-compactification] and let $J_0$ be
the Jacobian of the completed curve over $\Fq$ given by
[sk-prop-jacobian-descent], with geometric fibre $J$.
On the proper geometric curve, global functions are constant: properness
makes the image of a nonconstant $f$ closed and hence all of $\mathbf A^1$,
while the closed locus
$tf=1$ in $C\times\mathbf A^1$ would have nonclosed projected image,
contradicting properness. Thus $H^0(C,\mathbf G_m)=k^\times$.
The cover adjoining an $\ell^n$th root of a unit is etale (its derivative
is invertible), giving the Kummer sequence. Its long exact sequence, the
identification $H^1(C,\mathbf G_m)=\operatorname{Pic}(C)$ of
[sk-prop-hilbert90] — canonical, hence natural, so that $u\mapsto u^m$
on $\mathbf G_m$ becomes the $m$-th tensor power of line bundles and the
identification commutes with the Galois action — and algebraic
closedness of $k$ give

$$
H^1(C,\mu_{\ell^n})\simeq\operatorname{Pic}(C)[\ell^n]
\simeq J[\ell^n].
$$

The second isomorphism is the only place the Jacobian enters, and it needs
no separate input: [sk-prop-jacobian-descent] identifies $J(k)$ with
$\operatorname{Pic}^0(C)$, and the $\ell^n$-torsion of
$\operatorname{Pic}(C)$ already lies in $\operatorname{Pic}^0(C)$, since
$L^{\otimes\ell^n}\cong\mathcal O_C$ forces $\ell^n\deg L=0$ in the
torsion-free group $\mathbf Z$, hence $\deg L=0$. So
$\operatorname{Pic}(C)[\ell^n]=\operatorname{Pic}^0(C)[\ell^n]=J[\ell^n]$,
and the identification is $\Gal(k/\Fq)$-equivariant by the equivariance
clause of [sk-prop-jacobian-descent].
These maps respect the transitions in [sk-d-real-jacobian]: the
transition $z\mapsto z^\ell$ on roots of unity is the $\ell$-th tensor
power on line bundles and multiplication by $\ell$ on $J$, a group
isomorphism commuting with both.
The maps on $H^0(C,\mu_{\ell^n})$ are surjective. Hence the degree-one
derived inverse limit is the ordinary inverse limit: in the two-term
product model, the difference map
$(a_n)\mapsto(a_n-r_n(a_{n+1}))$ on $H^0$ is onto by successive lifting.
After inverting $\ell$ and extending coefficients, this proves
$H^1(C,E)(1)\simeq V_\ell J\otimes E$.

A Frobenius-fixed vector in $V_\ell J$ clears denominators to an
integral fixed tuple $(t_n)$. The Tate module is $\ell$-torsion-free,
since $\ell t=0$ implies $t_n=\ell t_{n+1}=0$.
Each $t_n$ belongs to the finite group $J_0(\Fq)$, whose $\ell$-primary
part is killed by some $\ell^a$; hence $t_n=\ell^at_{n+a}=0$.
Here $C$ is proper, so finite dimensionality is [sk-lem-finite] and the
perfect pairing is [sk-thm-derived-duality] in dimension $d=1$ (with
$H_c$ replaced by $H$), Frobenius-equivariantly by [sk-thm-frobenius];
together they identify $H^1(C,E)$ with $(V_\ell J\otimes E)^\vee$.
Thus $\Frob-1$ is injective on the finite-dimensional $\Ql$-space
$V_\ell J$, hence bijective, and it stays bijective on
$V_\ell J\otimes E$, the inverse extending $E$-linearly. The transpose
of an invertible map is invertible, and so is
$\Frob^{-1}-1=-\Frob^{-1}(\Frob-1)$; hence Frobenius, which acts on the
dual $(V_\ell J\otimes E)^\vee$ through the transpose of $\Frob^{\pm1}$,
has no fixed vector there. This explicitly retains the Tate twist.

*Open curves and additive characters.*
For $D=(C_0\setminus U_0)(k)$, the constant open–closed sequence
[sk-prop-sf-open-closed-triangle] together with the compact-support duality of
[sk-thm-derived-duality] gives
$0\to H^1(C,E)\to H^1(U,E)\to(E^D)^\vee(-1)$.
A positive Frobenius power on the boundary term is a scalar $q^r\ne1$,
so $H^1(U,E)^{\Frob=1}=0$.
If a continuous additive map $b:\pi_1(U)\to E$ is invariant under
conjugation by $\gamma$, choose a $\Ql$-basis of $E$ with coordinate maps
$t_i:E\to\Ql$. Compactness of $\pi_1(U)$ makes $b(\pi_1(U))$ bounded, so for
some $a$ each $b_i=\ell^at_i\circ b$ is a continuous homomorphism
$\pi_1(U)\to\Zl$, again invariant under conjugation by $\gamma$. Its
reductions modulo $\ell^n$ are classes in
$H^1(U,\Z/\ell^n)=\Hom_{\mathrm{cont}}(\pi_1(U),\Z/\ell^n)$, compatible in
$n$, and conjugation by the degree-one lift $\gamma$ is the Frobenius action
on these groups; so $b_i$ is a Frobenius-fixed element of
$H^1(U,\Zl)=\Hom_{\mathrm{cont}}(\pi_1(U),\Zl)$. This group is torsion free,
and the image of $b_i$ in $H^1(U,E)$ is Frobenius fixed, hence zero by the
previous paragraph; so $b_i=0$ for every $i$, and $b=0$.

*Logarithm and purity.*
By [sk-p-real-integral], take a stable integral rank-one model
for $\chi|_{\pi_1(U)}$. A finite reduction gives $N\ge1$ with
$\chi(g)^N\in U_E$ for every geometric $g$.
The series in [sk-d-real-log] is continuous and additive by the formal
logarithm identity. It is injective because, for $v_\ell(x)\ge2$,
each term $x^n/n$ with $n\ge2$ has strictly larger valuation than $x$.
Thus $b(g)=\log(\chi(g)^N)$ is an invariant additive map, hence zero.
Injectivity gives $\chi(g)^N=1$, proving finite geometric image.
Apply [sk-p-rankone] to obtain the finite-image character and constant
factor. At a degree-$d$ point the scalar is $\zeta c^d$
with $\zeta$ a root of unity, so its complex modulus is
$|\iota(c)|^d=q^{dw/2}$. This is purity in [sk-d-real-weights].

Uses: [sk-d-real-jacobian], [sk-d-real-log], [sk-d-real-setup], [sk-d-real-weights], [sk-d-real-weil], [sk-def-av-jacobian], [sk-def-av-pic], [sk-i-real-compactification], [sk-i-real-sheaves], [sk-lem-finite], [sk-p-rankone], [sk-p-real-integral], [sk-p-real-operations], [sk-prop-hilbert90], [sk-prop-jacobian-descent], [sk-prop-sf-open-closed-triangle], [sk-thm-av-final], [sk-thm-derived-duality], [sk-thm-frobenius]
