+++
id = "lem-fd-as-characters"
kind = "lemma"
title = "Isotypic decomposition of the Artin–Schreier pushforward"
order = 2682
uses = ["def-fd-artin-schreier-sheaf", "def-weil-pbc-etale-sheaves", "def-weil-pbc-finite-torsors", "lem-fd-as-cover", "lem-fd-character-orthogonality"]
+++
With the $\mathbf F_p$-action of [lem-fd-as-cover], there is a canonical decomposition

$$
\pi_*\overline{\mathbf Q}_\ell\cong\bigoplus_{\chi\in\widehat{\mathbf F}_p}\mathcal L_\chi,
$$

where each $\mathcal L_\chi$ is lisse of rank one on $X_0$, and $\mathcal L_0=1$ (for $\chi\neq0$ the summand $\mathcal L_\chi$ need not be nonconstant: all are constant when $f=0$). In particular
$\mathcal L_{\psi,f}\otimes\mathcal L_{\psi,g}\cong\mathcal L_{\psi,f+g}$, $(\mathcal L_{\psi,f})^{-1}\cong\mathcal L_{\psi,-f}$, and $\mathcal L_{\psi^{-1},f}\cong\mathcal L_{\psi,-f}$.

## Proof

*Step 1 (the cover trivializes itself).* By [lem-fd-as-cover],
$\pi$ is finite étale of degree $p$ with the $\mathbf F_p$-action
$y\mapsto y+a$, and $Y=\Spec\mathcal O_{X_0}[T]/(T^p-T-f)$. In
$\mathcal O_Y[T']$ one has the identity

$$
T'^p-T'-f=\prod_{a\in\mathbf F_p}\bigl(T'-(T+a)\bigr),
$$

because the right-hand side equals $(T'-T)^p-(T'-T) =T'^p-T'-(T^p-T)$ and $T^p-T=f$ in $\mathcal O_Y$; the factors are pairwise
comaximal, their differences being the units $a'-a\in\mathbf F_p^\times$.
The Chinese remainder theorem therefore gives

$$
\mathcal O_Y\otimes_{\mathcal O_{X_0}}\mathcal O_Y
=\mathcal O_Y[T']/(T'^p-T'-f)\xrightarrow{\ \sim\ }
\prod_{a\in\mathbf F_p}\mathcal O_Y,
\qquad T'\longmapsto(T+a)_a ,
$$

that is $Y\times_{X_0}Y\cong\mathbf F_p\times Y$ by $(y,y')\mapsto(y'-y,y)$.
Consequently the $\mathbf F_p$-action is simply transitive on the geometric
fibres of $\pi$, so $\pi$ is an $\mathbf F_p$-torsor and
$\underline{\operatorname{Hom}}_{X_0}(-,Y)$ is a finite locally constant sheaf
with simply transitive $\mathbf F_p$-action in the sense of
[def-weil-pbc-finite-torsors].
*Step 2 (the pushforward is lisse of rank $p$).* Pulling back along the
étale cover $\pi$ and using Step 1 identifies
$\pi^*\pi_*\overline{\mathbf Q}_\ell$ with the constant sheaf
$\overline{\mathbf Q}_\ell[\mathbf F_p]$ carrying the regular representation;
by [def-weil-pbc-etale-sheaves] a sheaf which becomes constant after an
étale base change is locally constant, so $\pi_*\overline{\mathbf Q}_\ell$
is lisse of rank $p$, its stalk at every geometric point being the regular
representation.
*Step 3 (the idempotents split it).* Since $p\neq\ell$, the elements
$e_\chi=\frac1p\sum_{a\in\mathbf F_p}\chi(-a)\sigma_a$ of the group algebra are
well defined; expanding the product and substituting $c=a+b$, the coefficient
of $\sigma_c$ in $e_\chi e_{\chi'}$ is
$\frac1{p^2}\chi'(-c)\sum_{a\in\mathbf F_p}(\chi^{-1}\chi')(a) =\frac1p\delta_{\chi,\chi'}\chi(-c)$ by the orthogonality relation
[lem-fd-character-orthogonality]. Hence
$e_\chi e_{\chi'}=\delta_{\chi,\chi'}e_\chi$ and $\sum_\chi e_\chi=1$, so

$$
\pi_*\overline{\mathbf Q}_\ell=\bigoplus_{\chi\in\widehat{\mathbf F}_p}
\mathcal L_\chi,\qquad \mathcal L_\chi=e_\chi\,\pi_*\overline{\mathbf Q}_\ell ,
$$

a direct sum decomposition by idempotents, with no appeal to a splitting
theorem for group algebras.
*Step 4 (each summand is lisse of rank one; $\mathcal L_0=1$).* Pulling $\mathcal L_\chi$ back along $\pi$ gives the constant
subsheaf $e_\chi\overline{\mathbf Q}_\ell[\mathbf F_p]$ of the regular
representation; the rank of an idempotent equals its trace, and
$\operatorname{tr}\sigma_a=p\delta_{a,0}$, so
$\operatorname{tr}e_\chi=\chi(0)=1$. Hence $\pi^*\mathcal L_\chi$ is constant
of rank one, and $\mathcal L_\chi$ is lisse of rank one by
[def-weil-pbc-etale-sheaves]. The summand $\chi=0$ is the invariant part
$(\pi_*\overline{\mathbf Q}_\ell)^{\mathbf F_p}$, i.e. the invariants of the
pushforward along a torsor, which is the constant sheaf
$\overline{\mathbf Q}_\ell$; so $\mathcal L_0=1$.
*Step 5 (multiplicativity).* By [def-fd-artin-schreier-sheaf],
$\mathcal L_{\psi,f}=e_\Psi\pi_*\overline{\mathbf Q}_\ell$ is the summand
$\mathcal L_\chi$ for $\chi=\Psi$, so it is lisse of rank one by Step 4. Let
$f,g\in\Gamma(X_0,\mathcal O_{X_0})$ with covers $\pi_f:Y_f\to X_0$,
$\pi_g:Y_g\to X_0$, and put $W=Y_f\times_{X_0}Y_g$, $\pi_W:W\to X_0$. At a
geometric point the stalk of $\pi_{W*}\overline{\mathbf Q}_\ell$ is the space
of functions on the product of the two fibres, i.e. the tensor product of the
stalks, so
$\pi_{W*}\overline{\mathbf Q}_\ell\cong\pi_{f*}\overline{\mathbf Q}_\ell\otimes\pi_{g*}\overline{\mathbf Q}_\ell$,
compatibly with the action of $\mathbf F_p\times\mathbf F_p$; hence
$\mathcal L_{\psi,f}\otimes\mathcal L_{\psi,g}$ is the rank-one subsheaf on
which $(a,b)$ acts by $\Psi(a)\Psi(b)$. Since
$(T_f+T_g)^p-(T_f+T_g)=f+g$, the element $T_f+T_g$ defines
$h:W\to Y_{f+g}$ over $X_0$ with $h\circ\sigma_{(a,b)}=\sigma_{a+b}\circ h$.
Pullback $h^*:\pi_{f+g,*}\overline{\mathbf Q}_\ell\to\pi_{W*}\overline{\mathbf Q}_\ell$
is injective on stalks, $h$ being surjective on geometric fibres (the action
on the fibre of $Y_{f+g}$ is transitive), and it carries a section $\varphi$
with $\sigma_c^*\varphi=\Psi(c)\varphi$ to one with
$\sigma_{(a,b)}^*h^*\varphi=h^*\sigma_{a+b}^*\varphi=\Psi(a)\Psi(b)\,h^*\varphi$.
So $h^*$ maps $\mathcal L_{\psi,f+g}$ injectively on stalks into
$\mathcal L_{\psi,f}\otimes\mathcal L_{\psi,g}$; both are lisse of rank one,
so this is an isomorphism
$\mathcal L_{\psi,f}\otimes\mathcal L_{\psi,g}\cong\mathcal L_{\psi,f+g}$.
For $f=0$ the covering is the trivial torsor $X_0\times\mathbf F_p$ and the
$\Psi$-isotypic part of the functions on $\mathbf F_p$ is spanned by the
nowhere vanishing function $a\mapsto\Psi(a)$, so
$\mathcal L_{\psi,0}\cong\overline{\mathbf Q}_\ell$; taking $g=-f$ gives
$\mathcal L_{\psi,f}\otimes\mathcal L_{\psi,-f}\cong\overline{\mathbf Q}_\ell$,
i.e. $(\mathcal L_{\psi,f})^{-1}\cong\mathcal L_{\psi,-f}$.
Finally, $T\mapsto-T$ defines an isomorphism $Y_{-f}\to Y_f$ over $X_0$
(as $(-T)^p-(-T)=-(T^p-T)$ for $p$ odd, and $-T=T$ for $p=2$) which
intertwines $\sigma_a$ on $Y_f$ with $\sigma_{-a}$ on $Y_{-f}$; it therefore
carries the $\Psi^{-1}$-isotypic part of $\pi_{f*}\overline{\mathbf Q}_\ell$
onto the $\Psi$-isotypic part of $\pi_{-f,*}\overline{\mathbf Q}_\ell$, i.e.
$\mathcal L_{\psi^{-1},f}\cong\mathcal L_{\psi,-f}$.
