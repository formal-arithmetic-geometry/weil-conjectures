+++
id = "sk-def-bc"
kind = "section"
title = "The recorded base-change property"
order = 1364
lean = ["AlgebraicGeometry.Etale.BaseChangeProperty", "AlgebraicGeometry.Etale.baseChangeHomologyMap"]
+++
*Definition (sketch).*

For a morphism $f:X\to S$, an integer $n$ invertible on $S$, and
$q\ge0$, write $\mathrm{BC}(f,n,q)$ for: for every
quasi-compact quasi-separated $g:T\to S$, every
$\Z/n\Z$-sheaf $\mathcal F$ on $T_{\Et}$, and the Cartesian square

$$
\begin{array}{ccc}
X & \xleftarrow{\;h\;} & Y=X\times_ST\\
f\downarrow & & \downarrow e\\
S & \xleftarrow{\;g\;} & T,
\end{array}
$$

the base-change map
$f^{-1}R^qg_*\mathcal F\longrightarrow R^qh_*e^{-1}\mathcal F$
is an isomorphism. The *base-change map* is defined in the
usual way (adjunction and pullback of the exchange); it is compatible
with étale localization and composition of squares.

This tests only the fixed morphism $f$ and the single degree $q$.
The reduction lemmas below use the *cumulative universal*
property, written $\mathrm{UBC}^{\le q}(f,n)$ (it is the property
$BC(f,n,q)$ of Stacks Project, Tag `0F02`): for every
morphism $S'\to S$, every quasi-compact quasi-separated $g:T\to S'$,
every $\Z/n\Z$-sheaf $\mathcal F$ on $T_{\Et}$ and every
$0\le r\le q$, the base-change map
$(f_{S'})^{-1}R^rg_*\mathcal F\to R^rh_*e^{-1}\mathcal F$ of the
square of $f_{S'}:X\times_SS'\to S'$ along $g$ is an isomorphism;
that is, $\mathrm{BC}(f_{S'},n,r)$ for every $S'\to S$ and every
$r\le q$ ($n$ is invertible on $S'$ because it is on $S$). We say
that $\mathrm{BC}(f,n,q)$ *holds universally* if
$\mathrm{BC}(f_{S'},n,q)$ holds for every $S'\to S$. The preliminary
base change is not a formality: $\mathrm{BC}(f,n,q)$ at the fixed
base does not in general imply $\mathrm{BC}(f_{S'},n,q)$ (already
for $q=0$ there are flat, finitely presented $f$ with geometrically
connected fibres satisfying $\mathrm{BC}(f,n,0)$ but not
$\mathrm{BC}(f_{\Aaf^1_S},n,0)$), and the closed–open step of
[sk-lem-failure-field] applies the lower-degree property to a base
change of $f$. For smooth $f$ the distinction disappears: smoothness
is stable under base change, and the induction on $q$ in
[sk-thm-smooth-base-change] produces $\mathrm{UBC}^{\le q}(f,n)$
directly, so the lower degrees are not an independent requirement.
