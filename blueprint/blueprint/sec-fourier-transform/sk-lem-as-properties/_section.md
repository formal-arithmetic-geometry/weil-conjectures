+++
id = "sk-lem-as-properties"
kind = "section"
title = "The Artin–Schreier sheaf is a lisse character sheaf"
order = 2679
lean = ["AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf", "AlgebraicGeometry.Etale.artinSchreierSheafAddIso", "AlgebraicGeometry.Etale.artinSchreierSheafZeroIso"]
uses = ["sk-def-as", "sk-def-fourier-set"]
+++
*Lemma (sketch).*

$\pi$ is finite étale of degree $p$, and the translations $\sigma_a$
($a\in\Fp$) act simply transitively on its geometric fibres: they make $Y$
an $\Fp$-torsor over $X_0$. The automorphisms of $Y$ *as an
$\Fp$-torsor* (those commuting with the $\sigma_a$) form $\Gamma(X_0,\Fp)$,
which is $\Fp$ when $X_0$ is connected; and $\Fp\to\operatorname{Aut}(Y/X_0)$
is an isomorphism when $Y$ is connected, but not in general (for $f=0$ the
cover $Y=\coprod_{a\in\Fp}X_0$ is split, and e.g. for $p=3$,
$X_0=\Spec\mathbf F_3$ its full automorphism group over $X_0$ is $S_3$).
Over $\Aone_{k_0}$ the covering is $y\mapsto x=y^p-y$. Its pushforward
decomposes as
$\pi_*\Qlb\cong\bigoplus_{\chi\in\widehat{\Fp}}\mathcal L_\chi$ with each
$\mathcal L_\chi$ lisse of rank one and $\mathcal L_0=1$ (for $\chi\ne0$,
$\mathcal L_\chi$ may or may not be constant, e.g. all are constant when $f=0$);
consequently $\mathcal L_{\psi,f}$ is lisse of rank one,

$$
\mathcal L_{\psi,f}\otimes\mathcal L_{\psi,g}\cong\mathcal L_{\psi,f+g},
\qquad
(\mathcal L_{\psi,f})^{-1}\cong\mathcal L_{\psi,-f}.
$$

At a closed point $u$ the geometric Frobenius acts on $\mathcal L_{\psi,f}$ by
$\Psi(\Tr_{\kappa(u)/\Fp}f(u))=\psi(\Tr_{\kappa(u)/k_0}f(u))$; so its trace
function on $\Aone_{k_0}$ is
$t_{\mathcal L_{\psi,ax}}(u)=\psi(\Tr_{\kappa(u)/k_0}(au))$; and
$H^q(\Aone_{\bar k},\mathcal L_{\psi_a})=0$ for $(q,a)\neq(0,0)$, while
$H^0(\Aone_{\bar k},\Qlb)=\Qlb$ and $H^q(\Aone_{\bar k},\Qlb)=0$ for $q>0$.
(Blueprint lem:fd-as-cover, lem:fd-as-cover-affine-line,
lem:fd-as-characters, lem:fd-as-lisse, lem:fd-as-trace,
lem:fd-cohomology-affine-line-character.)

## Proof

The derivative of $T^p-T-f$ is $-1$, so $\pi$ is étale; $\pi$ is finite of
degree $p$; the translations $\sigma_a$ act simply transitively on each
geometric fibre (two roots of $T^p-T-f(\bar x)$ in an algebraically closed
field differ by a root of $T^p-T$, i.e. by an element of $\Fp$), so $Y$ is
an $\Fp$-torsor over $X_0$ and
$\pi_*\Qlb$ is lisse of rank $p$ with regular representation at each stalk
(thm:galois-lc-etale, thm:galois-torsor-h1,
def:weil-pbc-finite-torsors). An automorphism of $Y$ over $X_0$ sends
$T$ to another root $T+e$ of $T^p-T-f$, where $e^p=e$, i.e. $e:Y\to\Fp$ is a
locally constant function; it commutes with the $\sigma_a$ exactly when $e$
is $\Fp$-invariant, i.e. comes from $\Gamma(X_0,\Fp)$, and when $Y$ is
connected $e$ is a constant $a\in\Fp$, so every automorphism is a
translation. Since $p\ne\ell$ and $\Qlb$ contains the
$p$-th roots of unity, Maschke splits the group algebra: this gives the
isotypic decomposition with each part of rank one, because every character of
the abelian group occurs exactly once in the regular representation. The
$\chi=0$ part is the invariant part of a pushforward along a torsor, i.e. the
constant sheaf. The group law of the torsor makes the decomposition one of
algebras, whence the multiplicativity and the inverse formula. Over
$\Aone_{k_0}$ the equation reads $T^p-T-x$ with $y=T$. For the trace: at a closed point $u$ with $|\kappa(u)|=q^m$, a
point $y$ of the fibre satisfies
$y^{q^m}=y+\sum_{0\le j<r}f(u)^{p^j}=y+\Tr_{\kappa(u)/\Fp}f(u)$, where $p^r=q^m$, so the
geometric Frobenius (pullback along the $q^m$-power map) acts on the fibre
functions as $\sigma_{\Tr_{\kappa(u)/\Fp}f(u)}$, hence on the $\Psi$-isotypic
part by $\Psi(\Tr_{\kappa(u)/\Fp}f(u))=\psi(\Tr_{\kappa(u)/k_0}f(u))$; take
$f=ax$.
For the cohomology: the finite-pushforward identity
$H^q(X_0,\pi_*\mathcal F)\cong H^q(Y,\mathcal F)$
(lem:fd-finite-pushforward-cohomology) turns
$\bigoplus_\chi H^q(\Aone_x,\mathcal L_\chi)$ into
$H^q(\Aone_y,\Qlb)$, which is $\Qlb$ in degree $0$ and $0$ above
(lem:fd-affine-line-constant-cohomology); the $\Fp$-action on
$H^0(\Aone_y,\Qlb)$ is trivial, so only $\chi=0$ survives there; in
particular $\mathcal L_{\psi,x}=\mathcal L_\Psi$, the component with
$\chi=\Psi\neq0$ of this cover, has vanishing cohomology in every degree.
For $a\neq0$ the sheaf $\mathcal L_{\psi_a}=\mathcal L_{\psi,ax}$ is not a
component of the same cover $u^p-u=x$ (its nontrivial components are indexed
by $\Fp^\times$ only); instead, the scaling $m_a:x\mapsto ax$ is an
automorphism of $\Aone$ with $m_a^*\mathcal L_{\psi,x}=\mathcal L_{\psi,ax}$
(the Artin–Schreier covering of $ax$ is the pullback along $m_a$ of that of
$x$), so $H^q(\Aone_{\bar k},\mathcal L_{\psi_a})\cong
H^q(\Aone_{\bar k},\mathcal L_{\psi,x})=0$ for all $q$.

Uses: [sk-def-as], [sk-def-fourier-set]
