+++
id = "def-trf-global-operator"
kind = "definition"
title = "Global operator of a correspondence"
order = 2288
uses = ["def-compact-support-direct-image-detailed", "def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-weil-derived-direct-image", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties", "prop-functor-package"]
+++
In the setting of [def-trf-correspondence], assume that the
ordinary leg $c_2$ is
proper. The
*global operator* of a correspondence $u$ is

$$
T_c(u):R\Gamma_c(X,K)\longrightarrow R\Gamma_c(X,K),
$$

the composite

$$
\begin{aligned}
R\Gamma_c(X,K)&\xrightarrow{\eta^*_{c_2}}
R\Gamma_c(X,Rc_{2*}Lc_2^*K)
\xrightarrow{\ \sim\ }R\Gamma_c(C,Lc_2^*K)\\
&\xrightarrow{R\Gamma_c(C,u)}
R\Gamma_c(C,Rc_1^!K)
\xrightarrow{\ \sim\ }R\Gamma_c(X,Rc_{1!}Rc_1^!K)\\
&\xrightarrow{R\Gamma_c(X,\varepsilon_{c_1})}R\Gamma_c(X,K),
\end{aligned}
$$

where $R\Gamma_c$ is the compact-support cohomology of the
coefficient conventions
(computed with the
compact-support direct
image, and:

1. the first arrow is the unit of the adjunction
$Lc_2^*\dashv Rc_{2*}$ of the
derived direct image, applied
to $K$ on $X$: this is the canonical arrow $K\to Rc_{2*}Lc_2^*K$;
1. the first isomorphism is the identification $Rc_{2*}\simeq Rc_{2!}$ for the
proper $c_2$ (the
proper-coincidence clause of the six-operations package,
[prop-functor-package], item (3)), applied to $Lc_2^*K$ and
composed with the identity naturality of the compact-support
construction;
1. the second isomorphism is the *composition law* of the
compact-support direct image for the composite
$a_X\circ c_1=a_C$ ([prop-functor-package], item (3)),
$$
Ra_{X!}Rc_{1!}\xrightarrow{\ \sim\ }R(a_X\circ c_1)_!=Ra_{C!},
$$
which is correctly an isomorphism of functors with the associativity
compatibility: this arrow transports the compact-support cohomology of
$C$ to that of $X$ along the exceptional leg (it is *not* the
projection formula; the projection formula is not used here, and the
coinage of the terminology in earlier drafts was a slip);
1. the last arrow is the counit
$\varepsilon_{c_1}:Rc_{1!}Rc_1^!\to\operatorname{id}$ of the
adjunction $Rc_{1!}\dashv Rc_1^!$ of [def-trf-admissibility],
applied to $K$ and then to
$R\Gamma_c(X,-)$ (exact, so it maps the counit to an arrow in the
derived category).

The composite is a morphism of $D^b_{\mathrm{fin}}(A)$
by [lem-trf-global-operator-perfect], and
