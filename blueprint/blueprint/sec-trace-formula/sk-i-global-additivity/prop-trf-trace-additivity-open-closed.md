+++
id = "prop-trf-trace-additivity-open-closed"
kind = "theorem"
title = "Additivity of the Frobenius traces along an open–closed decomposition"
order = 2373
tags = ["latex:proposition"]
uses = ["def-exchange-projection", "def-trf-categorical-trace", "def-trf-frobenius-coefficient-morphism", "def-trf-frobenius-operators", "def-trf-iterated-weil-map", "def-trf-scheme-frobenius", "def-trf-strict-weil-complex", "def-trf-weil-extension-zero", "fix-lem-exchanges", "lem-trf-adjoint-mate", "lem-trf-frobenius-open-square", "lem-trf-frobenius-operator-compact-description", "lem-trf-open-square-exchange", "prop-functor-package", "prop-sf-open-closed-triangle-all-stages", "prop-trf-compact-support-perfectness", "prop-trf-graph-operator", "prop-trf-trace-formal-laws", "prop-weil-open-closed-recollement-adjunctions", "thm-sf-ctf-stability"]
+++
Fix the global finite-field datum
and the coefficient conventions, $A=A_{E,n}$. Let $X_0$ be a
separated finite-type $k_0$-scheme, let $i_0:Z_0\hookrightarrow X_0$
be a closed immersion with complementary open immersion
$j_0:U_0\hookrightarrow X_0$, and let $i:Z\hookrightarrow X$,
$j:U\hookrightarrow X$ be their base changes to $k$. Let
$(K,\varphi)\in D^b_{ctf,\mathrm W}(X,A)$ be a strict Weil complex
of [def-trf-strict-weil-complex].

1. For $h\in\{i,j\}$ with source $W\in\{Z,U\}$, one has
$h\,g_W=g_X\,h$, and the composite
$$
h^*\varphi:\;
Lg_W^*Lh^*K\xrightarrow{\ \sim\ }Lh^*Lg_X^*K
\xrightarrow{\ Lh^*\varphi\ }Lh^*K
$$
of the canonical pullback identification with $Lh^*\varphi$ makes
$(Lh^*K,h^*\varphi)$ a strict Weil complex on $W$; its iterates of
[def-trf-iterated-weil-map] are
$(h^*\varphi)^{[m]}=Lh^*\varphi^{[m]}\circ c_{h,m}$, with
$c_{h,m}:Lg_W^{m*}Lh^*\xrightarrow{\sim}Lh^*Lg_X^{m*}$ the canonical
identification.
1. For every $m\geq1$, with $F_{c,-}^{\,m}$ the global geometric
Frobenius operators of [def-trf-frobenius-operators] for these
Weil structures,
$$
\operatorname{tr}_A\bigl(F_{c,K}^{\,m}\mid R\Gamma_c(X,K)\bigr)
=
\operatorname{tr}_A\bigl(F_{c,j^*K}^{\,m}\mid R\Gamma_c(U,j^*K)\bigr)
+
\operatorname{tr}_A\bigl(F_{c,i^*K}^{\,m}\mid R\Gamma_c(Z,i^*K)\bigr)
$$
in $A$. These are categorical traces of perfect complexes in the
sense of [def-trf-categorical-trace]; no trace of an individual
cohomology module occurs.
1. *(Frobenius coefficient morphisms.)* Let instead
$K\in D^b_{ctf}(X,A)$ carry an arbitrary Frobenius coefficient
morphism $\psi:L\Phi_X^*K\to K$ of
[def-trf-frobenius-coefficient-morphism], with no Weil structure and no
invertibility. For $h\in\{i,j\}$ with source $W$ one has
$h\,\Phi_W=\Phi_X\,h$, the composite
$h^*\psi:L\Phi_W^*Lh^*K\xrightarrow{\sim}Lh^*L\Phi_X^*K
\xrightarrow{Lh^*\psi}Lh^*K$ is a Frobenius coefficient morphism on
$W$ with iterates $(h^*\psi)_m=Lh^*\psi_m\circ c'_{h,m}$, where
$c'_{h,m}:L\Phi_W^{m*}Lh^*\xrightarrow{\sim}Lh^*L\Phi_X^{m*}$ is the
canonical identification, and for every $m\geq1$ the global operators
$F_{c,m}$ of [def-trf-frobenius-coefficient-morphism] satisfy
$$
\operatorname{tr}_A\bigl(F_{c,m}(\psi)\mid R\Gamma_c(X,K)\bigr)
=
\operatorname{tr}_A\bigl(F_{c,m}(j^*\psi)\mid R\Gamma_c(U,j^*K)\bigr)
+
\operatorname{tr}_A\bigl(F_{c,m}(i^*\psi)\mid R\Gamma_c(Z,i^*K)\bigr).
$$

The proof below uses the Weil maps only as morphisms: the
invertibility of $\varphi$ is used only to stay inside the category
$D^b_{ctf,\mathrm W}$ on which $F_{c,-}^{\,m}$ is defined.

## Proof

*Step 1: restricted Weil structures.* Write
$g_X=\operatorname{id}_{X_0}\times\operatorname{Spec}(\gamma)$ and
likewise for $U,Z$. The automorphism $g_X$ maps $U=U_0\times_{k_0}k$
and $Z=Z_0\times_{k_0}k$ onto themselves, with restrictions $g_U$ and
$g_Z$. For the open square this is
[lem-trf-frobenius-open-square]; for the closed square the same
argument applies, since the inverse image of the closed subscheme
$Z$ under the isomorphism $g_X$ is the closed subscheme
$Z_0\times_{k_0}k$ with its restricted structure sheaf. Hence
$h\,g_W=g_X\,h$ and both squares are Cartesian. The complexes
$Lh^*K$ lie in $D^b_{ctf}(W,A)$ by [thm-sf-ctf-stability](i),
and $h^*\varphi$ is a composite of two isomorphisms, so
$(Lh^*K,h^*\varphi)$ is a strict Weil complex. The iterate formula
follows by induction on $m$ from the product formula of
[def-trf-iterated-weil-map]: the inductive step is naturality of
the pullback identifications in the coefficient together with their
cocycle law for the composite $g_X^{m+1}=g_X\circ g_X^m$.

*Step 2: the triangle is Frobenius-compatible.* Fix $m\geq1$, write
$g=g_X^m$ and $\psi_K=\varphi^{[m]}:Lg^*K\to K$. For the other two
vertices of the open–closed triangle of
[prop-sf-open-closed-triangle-all-stages],

$$
j_!j^*K\xrightarrow{\ \varepsilon\ }K\xrightarrow{\ \eta\ }
i_*i^*K\xrightarrow{\ \delta\ }j_!j^*K[1],
$$

put
$\psi_U=j_!(j^*\varphi)^{[m]}\circ b_g:Lg^*j_!j^*K\to j_!j^*K$ (the $m$-th iterate of the Weil extension by zero [def-trf-weil-extension-zero] of $(j^*K,j^*\varphi)$), with
$b_g$ the open-square exchange of [lem-trf-open-square-exchange],
and $\psi_Z=i_*(i^*\varphi)^{[m]}\circ e_g:Lg^*i_*i^*K\to i_*i^*K$,
with $e_g:Lg^*i_*\xrightarrow{\sim}i_*Lg_Z^{m*}$ the proper
base-change isomorphism for the closed immersion $i$
([prop-functor-package], clause (4)).

(a) $\varepsilon\circ\psi_U=\psi_K\circ Lg^*\varepsilon$. Both sides
are maps $Lg^*j_!j^*K\cong j_!Lg_U^{m*}j^*K\to K$, the identification
being $b_g$. By the adjunction $j_!\dashv j^*$ of
[prop-weil-open-closed-recollement-adjunctions] it suffices to
compare their restrictions to $U$. There $b_g$ is the identity
([lem-trf-open-square-exchange]) and $j^*\varepsilon$ is the
identity after the unit identification, so both restrictions equal
$j^*\varphi^{[m]}\circ c_{j,m}=(j^*\varphi)^{[m]}$, by Step 1.

(b) $\psi_Z\circ Lg^*\eta=\eta\circ\psi_K$. Both sides are maps
$Lg^*K\to i_*i^*K$. By the adjunction $i^*\dashv i_*$ of
[prop-weil-open-closed-recollement-adjunctions] it suffices to
compare the adjoint maps $i^*Lg^*K\to i^*K$. Since $e_g$ is the
exchange of the Cartesian closed square, its adjoint is the
canonical identification $c_{i,m}$, and the counit $i^*i_*\to\mathrm{id}$
is an isomorphism; both adjoints therefore equal
$i^*\varphi^{[m]}\circ c_{i,m}=(i^*\varphi)^{[m]}$, by Step 1.

(c) $\psi_U[1]\circ Lg^*\delta=\delta\circ\psi_Z$. The functor
$Lg^*$ is exact, so the image of the triangle under $Lg^*$ is
distinguished. By (a) and (b), the pair $(\psi_U,\psi_K)$ is
compatible with the first arrows; by the axiom of morphisms of
triangles there is $\psi':Lg^*i_*i^*K\to i_*i^*K$ with
$\psi'\circ Lg^*\eta=\eta\circ\psi_K$ and
$\delta\circ\psi'=\psi_U[1]\circ Lg^*\delta$. Then
$(\psi'-\psi_Z)\circ Lg^*\eta=0$ by (b), so $\psi'-\psi_Z$ factors
as $d\circ Lg^*\delta$ with $d:Lg^*j_!j^*K[1]\to i_*i^*K$. Via
$b_g$ the source of $d$ is $j_!N[1]$ with $N=Lg_U^{m*}j^*K$, and
$\operatorname{Hom}(j_!N[1],i_*i^*K)=\operatorname{Hom}(N[1],j^*i_*i^*K)=0$
since $j^*i_*=0$ ([prop-weil-open-closed-recollement-adjunctions],
as in the Hom vanishing of
[prop-sf-open-closed-triangle-all-stages]). Hence $\psi'=\psi_Z$,
proving (c). Invertibility of the $\psi$ was not used.

*Step 3: an endomorphism of a triangle of perfect complexes.* By
[lem-trf-frobenius-operator-compact-description],
$F_{c,K}^{\,m}=R\Gamma_c(X,\psi_K)\circ g_{\gamma,c}^{m,*}$, where
$g_{\gamma,c}^{m,*}:R\Gamma_c(X,-)\to R\Gamma_c(X,Lg^*-)$ is the
compact-support base change along the automorphism $g$ of the
Cartesian square over $g_s^m$. This exchange is a natural
transformation between exact functors, natural in the coefficient
([fix-lem-exchanges], (1)), and it commutes with the connecting
morphisms because it is built from units, counits and pullback
identifications of exact functors. Applying the exact functor
$R\Gamma_c(X,-)$ to the triangle and using Step 2, the three
endomorphisms

$$
E_V=R\Gamma_c(X,\psi_V)\circ g_{\gamma,c}^{m,*},
\qquad V\in\{j_!j^*K,\;K,\;i_*i^*K\},
$$

(with $\psi_{j_!j^*K}=\psi_U$, $\psi_{i_*i^*K}=\psi_Z$) form an
endomorphism of the distinguished triangle

$$
R\Gamma_c(X,j_!j^*K)\to R\Gamma_c(X,K)\to R\Gamma_c(X,i_*i^*K)\to .
$$

More precisely, they form an endomorphism of this triangle *of filtered
origin*: the open–closed triangle is the cofibre sequence of the inclusion
$j_!j^*K\to K$, a two-step filtered object with graded pieces $j_!j^*K$ and
$i_*i^*K$; the maps $\psi_U,\psi_K,\psi_Z$ are the components of one
endomorphism of this filtered object (Step 2 exhibits $\psi_U$ as the
restriction of $\psi_K$ to the subobject and $\psi_Z$ as the induced map on
the quotient, with the identifications $b_g$, $e_g$ natural in the
coefficient); and $R\Gamma_c(X,-)\circ g^{m,*}_{\gamma,c}$ is a natural
transformation of exact functors, so it carries this filtered endomorphism
to an endomorphism of the two-step filtered perfect complex
$R\Gamma_c(X,j_!j^*K)\subset R\Gamma_c(X,K)$ in the filtered derived
category $DF(A)$. This filtered origin is what Step 5 uses; an endomorphism
of the distinguished triangle in the plain derived category, with its three
squares commuting only up to unspecified homotopies, would not suffice
([prop-trf-trace-formal-laws], item (2)).

*Step 4: identification with the operators on $U$ and $Z$.* By the
composition law and $Ri_!=Ri_*$ for the proper $i$
([prop-functor-package], clause (3)),
$R\Gamma_c(X,j_!-)\cong R\Gamma_c(U,-)$ and
$R\Gamma_c(X,i_*-)\cong R\Gamma_c(Z,-)$. Under these identifications
the compact-support base change $g_{\gamma,c}^{m,*}$ on $X$, followed
by $b_g$ resp. $e_g$, is the compact-support base change on $U$
resp. $Z$ along $g_U^m$ resp. $g_Z^m$: this is the pasting law of
[fix-lem-exchanges], (2), for the Cartesian squares
$W\to X\to\operatorname{Spec}k$ over $g_W^m,g,g_s^m$, together with
its compatibility with the composition law, [fix-lem-exchanges], (4);
for $j$ the exchange of the inner square is $b_g$ by construction of
$\operatorname{Ex}_!$ via extension by zero, for $i$ it is $e_g$
because $i$ is proper. Hence, by
[lem-trf-frobenius-operator-compact-description] on $U$ and $Z$ and
Step 1, $E_{j_!j^*K}$ is conjugate to $F_{c,j^*K}^{\,m}$ and
$E_{i_*i^*K}$ to $F_{c,i^*K}^{\,m}$, and $E_K=F_{c,K}^{\,m}$.

*Step 5: traces.* All three complexes are perfect by
[prop-trf-compact-support-perfectness], applied to
$K$, $j^*K$ and $i^*K$, which lie in $D^b_{ctf}$ by Step 1.
Filtered additivity [prop-trf-trace-formal-laws](2) applied to
the filtered endomorphism of Step 3 gives
$\operatorname{tr}_A(E_K)=\operatorname{tr}_A(E_{j_!j^*K})+\operatorname{tr}_A(E_{i_*i^*K})$,
and conjugacy invariance [prop-trf-trace-formal-laws](1) together
with Step 4 converts the right-hand side to the traces on
$R\Gamma_c(U,j^*K)$ and $R\Gamma_c(Z,i^*K)$. This is the asserted
identity.

*Step 6: Frobenius coefficient morphisms (item 3).* Repeat Steps 1–5
with the automorphism $g=g_X^m$ replaced by the finite morphism
$\Phi=\Phi_X^m$ and $\psi_K=\varphi^{[m]}$ replaced by the iterate
$\psi_m$, with the following changes. In Step 1, $\Phi_X$ is the base
change of the absolute Frobenius of $X_0$ ([def-trf-scheme-frobenius]),
which commutes with every morphism, so $h\Phi_W=\Phi_Xh$; the formula
for the iterates of $h^*\psi$ follows by induction on $m$ from the
recursion of [def-trf-frobenius-coefficient-morphism], exactly as the
iterate formula of Step 1. The open square is Cartesian by
[lem-trf-frobenius-open-square]. The closed square $i\Phi_Z^m=\Phi i$
need not be Cartesian, since $\Phi^{-1}(Z)$ may be a nilpotent
thickening of $Z$; in Step 2 replace $e_g$ by the ordinary base-change
morphism $e:L\Phi^*Ri_*\to Ri_*L\Phi_Z^{m*}$ of this commutative square
(unit of $L\Phi_Z^{m*}\dashv R\Phi^m_{Z*}$ followed by the counit of
$i^*\dashv Ri_*$, as in [def-exchange-projection]). Its adjoint is again
the canonical identification $c'_{i,m}$, and it is an isomorphism on
every geometric stalk: $\Phi$ is a universal homeomorphism with
$\Phi^{-1}(Z)=Z$ as sets, so both sides have stalk $N_{\Phi(\bar z)}$ at
$\bar z\in Z$ and stalk $0$ off $Z$. With these substitutions the
arguments (a)–(c) of Step 2 apply verbatim, and invertibility of
$\psi$ is not used.

In Steps 3 and 4, replace [lem-trf-frobenius-operator-compact-description]
by [prop-trf-graph-operator]: $F_{c,m}(\psi)=R\Gamma_c(X,\psi_m)\circ\Phi^\sharp$,
where
$\Phi^\sharp:R\Gamma_c(X,-)\to R\Gamma_c(X,L\Phi^*-)$ is induced by the
unit of $L\Phi^*\dashv R\Phi_*$, the identification
$R\Phi_*\simeq R\Phi_!$ for the finite $\Phi$ and the composition law
for $a_X\Phi=a_X$ ([prop-functor-package], clause (3)). It is a natural
transformation between exact functors, built from units and
identifications, so it commutes with the connecting morphisms and
Step 3 applies. For Step 4, the unit of the composite adjunction for
$\Phi h=h\Phi_W^m$ can be computed in either order, and $b_g$ (for $j$,
now the open-square exchange $b$ of [lem-trf-open-square-exchange]
for $\Phi$) and $e$ are the mates of the resulting equality
$h^*R\Phi_*=R\Phi^m_{W*}h^*$ on the open, respectively the
adjoint description on the closed, piece; the unit compatibility of
mates ([lem-trf-adjoint-mate], item (2)) therefore identifies
$\Phi^\sharp$ on $R\Gamma_c(X,h_!-)\cong R\Gamma_c(W,-)$, followed by
$b$ or $e$, with $(\Phi_W^m)^\sharp$ on $W$, compatibly with the
composition law ([fix-lem-exchanges], (2) and (4)). By
[prop-trf-graph-operator] on $U$ and $Z$ the three endomorphisms of
Step 3 are then conjugate to $F_{c,m}(\psi)$, $F_{c,m}(j^*\psi)$ and
$F_{c,m}(i^*\psi)$. Step 5 applies without change, the complexes being
perfect by [prop-trf-compact-support-perfectness]. This proves item 3.
