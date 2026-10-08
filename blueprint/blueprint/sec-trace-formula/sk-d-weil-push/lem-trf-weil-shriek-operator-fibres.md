+++
id = "lem-trf-weil-shriek-operator-fibres"
kind = "lemma"
title = "Global operator and fibres of the Weil $!$-pushforward"
order = 2366
uses = ["d-relative-frob", "def-exchange-projection", "def-trf-frobenius-coefficient-morphism", "def-trf-scheme-frobenius", "def-trf-weil-shriek-pushforward", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "fix-lem-exchanges", "i-relative-frob", "lem-trf-adjoint-mate", "lem-trf-weil-shriek-iterates", "prop-functor-package", "prop-trf-graph-operator"]
+++
In the setting of [def-trf-weil-shriek-pushforward], let
$K\in D^b_{ctf}(X,A)$, let $u:L\Phi_X^*K\to K$ be a Frobenius
coefficient morphism of [def-trf-frobenius-coefficient-morphism] (no
invertibility assumed), and let $(L,\psi)=(Rf_!K,Rf_!u\circ\theta_{f,1})$
be its Weil $!$-pushforward, with iterates
$\psi_m=Rf_!u_m\circ\theta_{f,m}$ ([lem-trf-weil-shriek-iterates]).

1. *Global operators.* Let
$c_f:R\Gamma_c(Y,Rf_!K)\xrightarrow{\sim}R\Gamma_c(X,K)$ be the
composition isomorphism for $a_Yf=a_X$ ([prop-functor-package],
clause (3)). For every $m\geq1$ the global operators of
[def-trf-frobenius-coefficient-morphism] satisfy
$$
c_f\circ F_{c,m}(\psi)=F_{c,m}(u)\circ c_f .
$$
1. *Fibres.* Let $m\geq1$, $y\in Y_0(\mathbf F_{q^m})$, and let
$\bar y:\operatorname{Spec}k\to Y$ be the geometric point over $y$, so
that $\Phi_Y^m\bar y=\bar y$. Put $X_{\bar y}=X\times_{f,Y,\bar y}\operatorname{Spec}k$,
with $i_{\bar y}:X_{\bar y}\to X$, and $K|_{\bar y}=Li_{\bar y}^*K$.
Then $X_{\bar y}=X_{0,y}\times_{\mathbf F_{q^m}}k$ for the separated
finite-type $\mathbf F_{q^m}$-scheme $X_{0,y}=X_0\times_{Y_0,y}\operatorname{Spec}\mathbf F_{q^m}$,
and for the finite-field datum with $q$ replaced by $q^m$
([def-weil-finite-field-fiber]) the $q^m$-power scheme Frobenius of
$X_{0,y}$ is the restriction $\Phi_{X_{\bar y}}$ of $\Phi_X^m$. The
composite
$$
u_m|_{\bar y}:L\Phi_{X_{\bar y}}^*K|_{\bar y}\xrightarrow{\ \sim\ }
Li_{\bar y}^*L\Phi_X^{m*}K\xrightarrow{\ Li_{\bar y}^*u_m\ }K|_{\bar y}
$$
is a Frobenius coefficient morphism for this datum, and the proper
base-change isomorphism
$\beta_{\bar y}:L_{\bar y}=\bar y^*Rf_!K\xrightarrow{\sim}R\Gamma_c(X_{\bar y},K|_{\bar y})$
([prop-functor-package], clause (4)) satisfies
$$
\beta_{\bar y}\circ\psi_{m,\bar y}=F_{c,1}\bigl(u_m|_{\bar y}\bigr)\circ\beta_{\bar y},
$$
where $\psi_{m,\bar y}:L_{\bar y}\cong(L\Phi_Y^{m*}L)_{\bar y}\to L_{\bar y}$
is the stalk map of $\psi_m$ at the fixed point $\bar y$ and $F_{c,1}$ is
the degree-one global operator over $\mathbf F_{q^m}$.
1. *Points and stalks.* $X_0(\mathbf F_{q^m})$ is the disjoint union of
the sets $X_{0,y}(\mathbf F_{q^m})$ over $y\in Y_0(\mathbf F_{q^m})$, and
for $x\in X_{0,y}(\mathbf F_{q^m})$ with geometric point $\bar x$ the
stalk map of $u_m|_{\bar y}$ at $\bar x$ is the stalk map $u_{m,\bar x}$.

Invertibility of $u$ is used nowhere.

## Proof

For a finite $k$-morphism $h:T'\to T$ of separated finite-type
$k$-schemes and $M\in D^b_{ctf}(T,A)$ write
$$
h^\sharp_M:R\Gamma_c(T,M)\xrightarrow{\ \eta_h\ }R\Gamma_c(T,Rh_*Lh^*M)
\xrightarrow{\ \sim\ }R\Gamma_c(T',Lh^*M)
$$
for the map induced by the unit of $Lh^*\dashv Rh_*$
([def-weil-derived-direct-image]), followed by $Rh_*\simeq Rh_!$ and
the composition law for $a_Th=a_{T'}$ ([prop-functor-package],
clause (3)). By [prop-trf-graph-operator], the global operator of the
graph correspondence of an endomorphism $h$ with coefficient
$w:Lh^*M\to M$ is $R\Gamma_c(T,w)\circ h^\sharp_M$; in particular
$F_{c,m}(u)=R\Gamma_c(X,u_m)\circ(\Phi_X^m)^\sharp_K$ and
$F_{c,m}(\psi)=R\Gamma_c(Y,\psi_m)\circ(\Phi_Y^m)^\sharp_L$. Two formal
properties are used.

(α) *Composition.* For finite $h':T''\to T'$ and $h:T'\to T$,
$(hh')^\sharp_M=h'^\sharp_{Lh^*M}\circ h^\sharp_M$ after
$Lh'^*Lh^*\simeq L(hh')^*$ ([def-weil-derived-pullback-tensor-hom]):
the unit of the composite adjunction is the composite of the units, and
the composition law is associative ([prop-functor-package],
clause (3)).

(β) *Base change.* In the Cartesian square of [d-relative-frob]
defining $X'_m$, the maps $\Phi_Y^m$ and $p_m$ are finite
([def-trf-scheme-frobenius]; $p_m$ is a base change of $\Phi_Y^m$). The
exchange $\operatorname{Ex}_!:L\Phi_Y^{m*}Rf_!\to Rf'_{m!}Lp_m^*$ of
[def-exchange-projection] is the mate, for the adjunctions
$L\Phi_Y^{m*}\dashv R\Phi^m_{Y*}$ and $Lp_m^*\dashv Rp_{m*}$, of the
composition isomorphism
$Rf_!Rp_{m!}\simeq R(fp_m)_!=R(\Phi_Y^mf'_m)_!\simeq R\Phi^m_{Y!}Rf'_{m!}$
([fix-lem-exchanges], item (4)). The unit compatibility of mates
([lem-trf-adjoint-mate], item (2)) says that $R\Phi^m_{Y*}\operatorname{Ex}_!$
after the unit $\eta_{\Phi_Y^m}$ at $Rf_!K$ equals $Rf_!\eta_{p_m}$ followed
by that composition isomorphism. Applying $R\Gamma_c(Y,-)$ and the
composition laws, which are coherent ([fix-lem-exchanges], items (2)
and (4)), gives
$$
c_{f'_m}\circ R\Gamma_c(Y,\operatorname{Ex}_!)\circ(\Phi_Y^m)^\sharp_L
=(p_m)^\sharp_K\circ c_f,
$$
with $c_{f'_m}:R\Gamma_c(Y,Rf'_{m!}-)\simeq R\Gamma_c(X'_m,-)$.

*(1).* By [def-trf-weil-shriek-pushforward], $\theta_{f,m}$ is
$\operatorname{Ex}_!$, then $Rf'_{m!}(\eta_{r_m})$, then the
identifications $Rf'_{m!}Rr_{m*}\simeq Rf_!$ and
$Lr_m^*Lp_m^*\simeq L\Phi_X^{m*}$; here $r_m$ is finite by
[i-relative-frob]. Under $c_{f'_m}$ and $c_f$, the second and third arrows
become $(r_m)^\sharp_{Lp_m^*K}$, by the definition of $\sharp$ and the
associativity of the composition law. Hence, by (β) and then (α) for
$p_mr_m=\Phi_X^m$,
$$
c_f\circ R\Gamma_c(Y,\theta_{f,m})\circ(\Phi_Y^m)^\sharp_L
=(r_m)^\sharp\circ(p_m)^\sharp_K\circ c_f=(\Phi_X^m)^\sharp_K\circ c_f .
$$
Naturality of $c_f$ gives
$c_f\circ R\Gamma_c(Y,Rf_!u_m)=R\Gamma_c(X,u_m)\circ c_f$. Composing,
$c_f\circ F_{c,m}(\psi)=R\Gamma_c(X,u_m)\circ(\Phi_X^m)^\sharp_K\circ c_f
=F_{c,m}(u)\circ c_f$.

*(2).* The identification $X_{\bar y}=X_{0,y}\times_{\mathbf F_{q^m}}k$
holds because both are $X_0\times_{Y_0}\operatorname{Spec}k$, with
$\operatorname{Spec}k\to Y_0$ the composite of $\bar y$ and the
projection. Since $y$ is rational over $\mathbf F_{q^m}$, the absolute
$q^m$-power Frobenius of $Y_0$ fixes it, so $\Phi_Y^m\bar y=\bar y$, and
$f\Phi_X^m=\Phi_Y^mf$ shows that $\Phi_X^m$ maps $X_{\bar y}$ to itself.
The restriction is the base change to $k$ of the absolute $q^m$-power
Frobenius of $X_{0,y}$, which is the $q^m$-power scheme Frobenius of the
$\mathbf F_{q^m}$-scheme $X_{0,y}$ of [def-trf-scheme-frobenius]. Hence
$u_m|_{\bar y}$ is a morphism of the required shape.

Pull the Cartesian square of [d-relative-frob] back along
$\bar y$ through $f'_m$. Because $\Phi_Y^m\bar y=\bar y$, its fibre is
$(X'_m)_{\bar y}=\operatorname{Spec}k\times_{\bar y,Y,f}X=X_{\bar y}$,
the base change of $p_m$ is $i_{\bar y}$, and since $r_m$ is a morphism
over $Y$ ($f'_mr_m=f$) with $p_mr_m=\Phi_X^m$, its base change is
$\Phi_{X_{\bar y}}$. By the pasting law for $\operatorname{Ex}_!$
([fix-lem-exchanges], item (2)), $\bar y^*\operatorname{Ex}_!$ for the
square of $f$ along $\Phi_Y^m$, followed by the base-change isomorphism
for $f'_m$ along $\bar y$, is the base-change isomorphism for $f$ along
$\Phi_Y^m\bar y=\bar y$, that is $\beta_{\bar y}$. The finite map $r_m$
satisfies proper base change, and its exchange
$\operatorname{Ex}_*$ along the fibre inclusion is compatible with the
units by the triangle identities, as in Step 2 of
[lem-trf-weil-shriek-iterates]; thus the base change of
$Rf'_{m!}(\eta_{r_m})$ along $\bar y$ is, under $\beta_{\bar y}$,
the map induced by the unit $\eta_{\Phi_{X_{\bar y}}}$, and the
remaining composition identifications become those defining
$(\Phi_{X_{\bar y}})^\sharp$. Hence
$\beta_{\bar y}\circ\bar y^*\theta_{f,m}=(\Phi_{X_{\bar y}})^\sharp_{K|_{\bar y}}\circ\beta_{\bar y}$
after the identification $\bar y^*L\Phi_Y^{m*}=\bar y^*$. By naturality
of the base-change isomorphism,
$\beta_{\bar y}\circ\bar y^*Rf_!u_m=R\Gamma_c(X_{\bar y},u_m|_{\bar y})\circ\beta_{\bar y}$.
Since $\psi_{m,\bar y}=\bar y^*Rf_!u_m\circ\bar y^*\theta_{f,m}$ under
$\bar y^*L\Phi_Y^{m*}=\bar y^*$, composing and using
[prop-trf-graph-operator] for $h=\Phi_{X_{\bar y}}$ gives
$\beta_{\bar y}\circ\psi_{m,\bar y}=F_{c,1}(u_m|_{\bar y})\circ\beta_{\bar y}$.

*(3).* An $\mathbf F_{q^m}$-point $x$ of $X_0$ lies over the
$\mathbf F_{q^m}$-point $y=f_0\circ x$ of $Y_0$, and the points of
$X_0$ over $y$ are exactly the $\mathbf F_{q^m}$-points of the fibre
$X_{0,y}$; this gives the disjoint union. The stalk of
$Li_{\bar y}^*M$ at $\bar x\in X_{\bar y}$ is $M_{\bar x}$, compatibly
with pullback identifications, so the stalk of $u_m|_{\bar y}$ at
$\bar x$ is $u_{m,\bar x}$.
