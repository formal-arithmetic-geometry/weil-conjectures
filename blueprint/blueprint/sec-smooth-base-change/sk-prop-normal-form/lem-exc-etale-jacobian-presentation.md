+++
id = "lem-exc-etale-jacobian-presentation"
kind = "lemma"
title = "Jacobian presentations for etale algebras"
order = 1399
uses = ["def-exc-jacobian-presentation", "def-weil-pbc-scheme-conventions"]
+++
An algebra is etale of finite presentation if and only if it admits a square
Jacobian presentation [def-exc-jacobian-presentation].

## Proof

We spell out the finite-presentation algebra step. Write $B=P/J$,
$P=R[x_1,\ldots,x_n]$, with $J$ finitely generated. The infinitesimal
criterion for etaleness, equivalent to the definition fixed by the scheme
conventions, gives the conormal isomorphism
$$
 J/J^2\xrightarrow{d}\bigoplus_{a=1}^n B\,dx_a.
$$
Here the conormal sequence is split injective at the left by formal
smoothness, and its cokernel $\Omega_{B/R}$ is zero by formal
unramifiedness. These are the ordinary module criteria for infinitesimal
lifting of ring maps. Choose $f_1,\ldots,f_n\in J$ whose classes map to a
basis. Then $J=(f_1,\ldots,f_n)+J^2$, and their Jacobian determinant is a
unit modulo $J$.

Apply the determinant form of Nakayama's lemma to the finitely generated
$P$-module $J/(f_1,\ldots,f_n)$. Since $J$ times this module is the whole
module, there is $g\in1+J$ with $gJ\subset(f_1,\ldots,f_n)$. Consequently
$$
 B\simeq (P/(f_1,\ldots,f_n))_g
   =R[x_1,\ldots,x_n,t]/(f_1,\ldots,f_n,gt-1).
$$
The enlarged Jacobian matrix is block triangular, with determinant
$g\det(\partial f_i/\partial x_j)$, a unit in $B$. This is the presentation
in [def-exc-jacobian-presentation]. Conversely its invertible Jacobian
solves, uniquely, the linear correction equations for a square-zero
thickening. Thus the finitely presented algebra is formally etale, and the
infinitesimal criterion makes it etale. The presentation calculation is also
recorded in [Stacks Project, Tag
00U9](https://stacks.math.columbia.edu/tag/00U9) and [Tag
07CF](https://stacks.math.columbia.edu/tag/07CF).
