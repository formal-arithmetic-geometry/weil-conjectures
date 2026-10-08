+++
id = "lem-trf-adjoint-mate"
kind = "lemma"
title = "Mates along an isomorphism of left adjoints"
order = 2299
uses = ["rem-trf-classical-framework"]
+++
Let $(\mathcal C_i,\mathcal T_i)$ be triangulated categories with
$T_i:\mathcal C_i\to\mathcal C_i$ the shifts, and let
$F_i:\mathcal C_1\to\mathcal C_2$, $G_i:\mathcal C_2\to\mathcal C_1$
be exact functors with adjunctions
$F_1\dashv G_1$ (unit $\eta_1$, counit $\varepsilon_1$) and
$F_2\dashv G_2$ (unit $\eta_2$, counit $\varepsilon_2$), and let
$\alpha:F_1\xrightarrow{\ \sim\ }F_2$ be a natural isomorphism.

1. There is a unique natural isomorphism
$\beta:G_1\xrightarrow{\ \sim\ }G_2$ compatible with the adjunctions,
given explicitly by the composite
$$
\beta:\quad G_1
\xrightarrow{\ \eta_2G_1\ }
G_2F_2G_1
\xrightarrow{\ G_2\alpha^{-1}G_1\ }
G_2F_1G_1
\xrightarrow{\ G_2\varepsilon_1\ }
G_2
$$
and its inverse
$$
\beta^{-1}:\quad G_2
\xrightarrow{\ \eta_1G_2\ }
G_1F_1G_2
\xrightarrow{\ G_1\alpha G_2\ }
G_1F_2G_2
\xrightarrow{\ G_1\varepsilon_2\ }
G_1.
$$
1. The units and counits are carried to each other: the two
composite morphisms
$$
\operatorname{id}\xrightarrow{\ \eta_1\ }G_1F_1
\xrightarrow{\ \beta F_1\ }G_2F_1
\xrightarrow{\ G_2\alpha\ }G_2F_2,
\qquad
\operatorname{id}\xrightarrow{\ \eta_2\ }G_2F_2,
$$
are equal, and the two composites
$$
F_1G_1\xrightarrow{\ F_1\beta\ }F_1G_2
\xrightarrow{\ \alpha G_2\ }F_2G_2
\xrightarrow{\ \varepsilon_2\ }\operatorname{id},
\qquad
F_1G_1\xrightarrow{\ \varepsilon_1\ }\operatorname{id},
$$
are equal; the analogous identities hold with the roles of the two
adjunctions exchanged. In particular the unit-compatibility reads
$$
G_2\alpha\circ\beta F_1\circ\eta_1=\eta_2,
$$
as morphisms $\operatorname{id}\to G_2F_2$ after the canonical
identification $G_2F_1\xrightarrow{G_2\alpha}G_2F_2$.
1. *Uniqueness.* Any natural isomorphism
$\beta':G_1\xrightarrow{\sim}G_2$ satisfying the unit compatibility
of (2) together with its counit analogue is equal to $\beta$; in
particular the identification of $G_1$ with $G_2$ is canonical
once $\alpha$ is.

All functors and natural transformations are in the
classical framework.

## Proof

In the framework of [rem-trf-classical-framework], for every
$x\in\mathcal C_1$, $y\in\mathcal C_2$, the adjunctions give
natural bijections

$$
\begin{aligned}
\operatorname{Hom}(x,G_1y)
&\simeq\operatorname{Hom}(F_1x,y)\\
&\xrightarrow{\ h\mapsto h\circ\alpha_x^{-1}\ }
\operatorname{Hom}(F_2x,y)
\simeq\operatorname{Hom}(x,G_2y).
\end{aligned}
$$

Yoneda gives a unique natural isomorphism $\beta:G_1\to G_2$.
Applying the bijection to $x=G_1y$ and
$\operatorname{id}_{G_1y}$ gives exactly the formula for $\beta_y$
in (1). Replacing $\alpha^{-1}$ with $\alpha$ in the reversed
bijection gives the displayed formula for $\beta^{-1}$; these maps
are inverse because the two Hom-bijections are inverse.

The unit $\eta_{1,x}$ corresponds to
$\operatorname{id}_{F_1x}$. The displayed bijection sends it to the
adjoint of $\alpha_x^{-1}:F_2x\to F_1x$, namely
$G_2(\alpha_x^{-1})\eta_{2,x}$.
Consequently $\beta_{F_1x}\eta_{1,x} =G_2(\alpha_x^{-1})\eta_{2,x}$, which proves the unit formula.
The counit corresponds to the identity of $G_1y$. Hence
$\beta_y$ is adjoint to
$\varepsilon_{1,y}\alpha_{G_1y}^{-1}$, giving

$$
\varepsilon_{2,y}F_2(\beta_y)
=\varepsilon_{1,y}\alpha_{G_1y}^{-1}.
$$

Precompose with $\alpha_{G_1y}$ and use naturality of $\alpha$ to
obtain
$\varepsilon_{2,y}\alpha_{G_2y}F_1(\beta_y)=\varepsilon_{1,y}$,
the counit formula of (2). The reversed bijections give the analogous
identities for the inverse. Finally, either adjunction compatibility
forces the displayed Hom-bijection, so Yoneda proves uniqueness.
