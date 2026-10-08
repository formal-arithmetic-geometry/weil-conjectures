+++
id = "sk-thm-smooth-base-change"
kind = "section"
title = "Smooth base change"
order = 1416
uses = ["sk-def-bc", "sk-def-smooth", "sk-lem-induction", "sk-prop-deg0", "sk-prop-input-spreading", "sk-prop-input-torsors"]
lean = ["AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth"]
+++
*Theorem (sketch).*

(Stacks Project, Étale Cohomology, Theorem 59.89.2, Tag
`0EYU`; the chapter follows the *second, shorter proof*.)
Let

$$
\begin{array}{ccc}
X & \xleftarrow{\;h\;} & Y\\
f\downarrow & & \downarrow e\\
S & \xleftarrow{\;g\;} & T
\end{array}
$$

be Cartesian with $f$ smooth and $g$ quasi-compact
quasi-separated. Then for every $q$ and every abelian sheaf
$\mathcal F$ on $T_{\Et}$ all of whose geometric stalks are torsion
of orders invertible on $S$,

$$
f^{-1}R^qg_*\mathcal F\ \xrightarrow{\ \sim\ }\ R^qh_*e^{-1}\mathcal F,
$$

the map being the base-change map of [sk-def-bc].

## Proof

*Degree zero*: [sk-prop-deg0] (smooth is flat, of finite
presentation, with geometrically reduced fibres).
*Filtered torsion*: $\mathcal F=\varinjlim_n\mathcal F[n]$
over $n$ invertible on $S$; inverse images are left adjoints and
$R^qg_*$, $R^qh_*$ commute with filtered colimits for qcqs $g,h$;
so it suffices to handle sheaves annihilated by a single $n$
invertible on $S$.
*Reduction to relative dimension one*: the assertion is
étale local on $X$ and $S$; by [sk-prop-normal-form] one may
assume $X$ and $S$
affine and $X\to S$ factoring through $\Aaf^d_S$; writing $X\to \Aaf^{d-1}_S\to\cdots\to\Aaf^1_S\to S$ and using the composition
compatibility of the base-change map, it suffices to prove the
assertion for affine smooth $X\to S$ of relative dimension one.
*Induction on $q$*: for $q\ge1$ with the theorem known in
degrees $<q$, that theorem applied to every base change $f_{S'}$ of
$f$ (again affine smooth of relative dimension one) and every qcqs
$T\to S'$ is exactly $\mathrm{UBC}^{\le q-1}(f,n)$, the hypothesis of
[sk-lem-induction]; the lemma gives $\mathrm{BC}(f,n,q)$ (indeed
universally); running the filtered colimit back over $n$
finishes the degree-$q$ case. Induction on $q$ concludes.

Uses: [sk-def-bc], [sk-def-smooth], [sk-lem-induction], [sk-prop-deg0], [sk-prop-input-spreading], [sk-prop-input-torsors]
