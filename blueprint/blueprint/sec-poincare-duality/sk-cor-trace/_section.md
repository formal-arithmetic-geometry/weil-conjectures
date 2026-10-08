+++
id = "sk-cor-trace"
kind = "section"
title = "The trace isomorphism"
order = 2442
uses = ["sk-def-trace-cup", "sk-lem-finite", "sk-prop-an", "sk-thm-purity-transport", "sk-thm-regular", "sk-thm-sf-identification", "sk-thm-smooth-purity"]
+++
*Corollary (sketch).*

In the setting of [sk-def-pairing] with $X_0$ in addition
*proper*, for the constant sheaf $K=\Lambda_X$,

$$
\operatorname{tr}^{(-d)}_X:H^{2d}(X,\Lambda)\xrightarrow{\ \sim\ }
\Lambda(-d)
$$

is an isomorphism, and it is the map produced by the duality at $i=0$;
its twist $\operatorname{tr}^{(-d)}_X(d):H^{2d}(X,\Lambda(d))\to\Lambda$
sends the class of a $k$-point $x\in X(k)$ (the image in
$H^{2d}(X,\Lambda(d))$ of the fundamental class $[x\subset X]$ of
[sk-thm-regular], $c=d$) to $1$. This is not an independent
convention: it follows from [sk-thm-regular](c), which identifies the
fundamental class with the isomorphism assembled from smooth purity of
$a_X$ and of $a_{\Spec k}=\mathrm{id}$, together with the compatibility
of smooth purity and of the counits with composition
([sk-thm-smooth-purity], [sk-thm-purity-transport]). Here
$[x\subset X]$ is defined at $\Lambda=A_{E,n}$; at $\Oe$ it means the
compatible system of the finite-level classes, and at $E$, $\Qlb$ its
image under scalar extension. (Blueprint 13, cor:sf-trace; 15,
cor:pod-constant-coefficients, thm:pod-trace-isomorphism.)

## Proof

Take $K=\Lambda_X$ in the proper case of [sk-thm-sf-identification]
and $i=0$: the
degreewise form reads $H^0_c(X,\Lambda)^\vee\cong H^{2d}(X,\Lambda)(d)$.
(At $\Lambda\in\{A_{E,n},E,\Qlb\}$ this is the degreewise clause. At
$\Lambda=\Oe$ the derived form gives
$H^{2d}(X,\Oe)(d)\cong\operatorname{Hom}(H^0,\Oe)\oplus\operatorname{Ext}^1(H^1,\Oe)$,
and the Ext term vanishes: $H^1(X,\Oe)$ is torsion-free, since
$H^0(X,\Oe)\to H^0(X,A_{E,1})$ is surjective, $X$ being connected.)
Since $X$ is proper, $Ra_{X!}\cong Ra_{X*}$ by [sk-def-ops] and hence
$H^0_c=H^0$; since $X$ is geometrically connected, $H^0(X,\Lambda)\cong \Lambda$ with the geometric Frobenius acting as the identity, which is the
$H^0$-clause of the finiteness interface
prop:cohomological-finiteness. Therefore
$\Lambda^\vee\cong H^{2d}(X,\Lambda)(d)$, i.e. $H^{2d}(X,\Lambda)\cong\Lambda(-d)$. The isomorphism produced this way is
the composite of the counit $\varepsilon_{a_X}$ of
$Ra_{X!}\dashv Ra_X^!$ with the orientation
$\gamma:\Lambda_X(d)[2d]\cong\omega_{X,\Lambda}$ of
[sk-thm-smooth-purity] and [sk-thm-purity-transport], which is exactly
the map $\operatorname{tr}^{(-d)}_X$ of [sk-def-trace-cup].

*Normalization at finite level.* Let $\Lambda=A_{E,n}$ and
$x\in X(k)$. Since $X$ is smooth over the algebraically closed field
$k$, the point $x:\Spec k\hookrightarrow X$ is a regular closed immersion
of codimension $d$ with $a_X\circ x=\mathrm{id}_{\Spec k}$, and
$\Spec k$ is regular, so [sk-thm-regular] applies with $c=d$. The
image of $[x\subset X]\in H^0(\Spec k,Rx^!\Lambda_X(d)[2d])
=H^{2d}_x(X,\Lambda(d))$ in $H^{2d}(X,\Lambda(d))$ is obtained by
forgetting supports, i.e. by applying $Ra_{X*}$ to the counit
$\varepsilon_x:Rx_*Rx^!\to\mathrm{id}$ of $Rx_!=Rx_*\dashv Rx^!$
([sk-def-ops]). By [sk-thm-regular](c), $[x\subset X]=
\operatorname{cl}_x(1)$ is the image of $1$ under the isomorphism
$\Phi_x:\Lambda\cong Rx^!\Lambda_X(d)[2d]$ assembled, in Steps 1–2 of
[sk-thm-regular], from the orientations of $a_X$ and of
$a_{\Spec k}=\mathrm{id}$ through the composition law
$Rx^!Ra_X^!\Lambda\cong R(a_X\circ x)^!\Lambda=\Lambda$; and the
orientation of the identity is the identity of $\Lambda$, by the
compatibility with composition in [sk-thm-smooth-purity] applied to
$\mathrm{id}=\mathrm{id}\circ\mathrm{id}$. Hence, transported along
$\gamma$, the class $[x\subset X]$ corresponds to
$1\in\Lambda=H^0(Rx^!Ra_X^!\Lambda)$, and
$\operatorname{tr}^{(-d)}_X(d)[x\subset X]$ is the image of $1$ under

$$
\Lambda=R(a_X\circ x)_!R(a_X\circ x)^!\Lambda
\cong Ra_{X!}Rx_!Rx^!Ra_X^!\Lambda
\xrightarrow{\ Ra_{X!}(\varepsilon_x)\ }Ra_{X!}Ra_X^!\Lambda
\xrightarrow{\ \varepsilon_{a_X}\ }\Lambda .
$$

The composition isomorphism for $(-)^!$ is the adjoint of
$Ra_{X!}Rx_!\cong R(a_X\circ x)_!$, so this composite is the counit
$\varepsilon_{a_X\circ x}=\varepsilon_{\mathrm{id}}=\mathrm{id}_\Lambda$;
therefore $\operatorname{tr}^{(-d)}_X(d)[x\subset X]=1$. (This is the
sense in which the trace is normalized by the fundamental class of
[sk-prop-an]: étale locally at $x$, $[x\subset X]$ is the frame class
$\partial\kappa(t_1)\cup\dots\cup\partial\kappa(t_d)$ of
[sk-thm-regular](b).)

*The other coefficient stages.* The frame classes of
[sk-thm-regular] are built from Kummer classes, boundaries and cup
products, which reduce to their counterparts under $A_{E,n}\to A_{E,m}$;
so $([x\subset X]_n)_n$ is a compatible system, which defines
$[x\subset X]$ over $\Oe$, and its images define it over $E$ and
$\Qlb$. At these stages $\operatorname{tr}^{(-d)}_X$ is the transported
counit read through the transported orientation, compatibly with the finite
reductions and with scalar extension ([sk-thm-purity-transport]). Hence
$\operatorname{tr}^{(-d)}_X(d)[x\subset X]\in\Oe$ reduces to $1$ at
every level, so it equals $1$, and the $E$- and $\Qlb$-statements
follow by scalar extension.

Uses: [sk-def-trace-cup], [sk-lem-finite], [sk-thm-sf-identification]
