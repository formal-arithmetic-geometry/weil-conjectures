+++
id = "def-a1-constituent-nonexceptional"
kind = "definition"
title = "Nonexceptional irreducible lisse sheaf (constituent form)"
order = 2752
uses = ["def-fd-artin-schreier-sheaf", "def-wf-fundamental-representation", "rem-dl-a1-conventions"]
lean = ["AlgebraicGeometry.WeilSheaf.IsNonexceptional"]
+++
In the conventions of [rem-dl-a1-conventions], let
$j:U_0\hookrightarrow A_0=\mathbf A^1_{k_0}$ be a dense open immersion
and let $\mathcal M$ be a nonzero irreducible lisse Weil sheaf on
$U_0$, with geometric fundamental representation
$\rho_{\mathrm{geom}}:\pi_1(U,\bar\eta)\to\operatorname{GL}(V)$,
$V=\mathcal M_{\bar\eta}$, as in
[def-wf-fundamental-representation]. The *geometric irreducible
constituents* of $\mathcal M$ are the Jordan–Hölder constituents of
the $\pi_1(U,\bar\eta)$-module $V$, viewed as irreducible lisse sheaves
on $U=U_0\otimes k$.

$\mathcal M$ is *constituent-nonexceptional* if none of its geometric
irreducible constituents is isomorphic to the restriction
$\mathcal L_{\psi(ax)}|_U$ of the Artin–Schreier sheaf of
[def-fd-artin-schreier-sheaf] for any $a\in k$, the value $a=0$
included; for $a=0$ the excluded constituent is the trivial rank-one
sheaf $\overline{\mathbf Q}_\ell$.
