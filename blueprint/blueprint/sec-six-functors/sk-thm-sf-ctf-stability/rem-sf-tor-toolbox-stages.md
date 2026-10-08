+++
id = "rem-sf-tor-toolbox-stages"
kind = "remark"
title = "The four coefficient stages"
order = 2203
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-rationalization-karoubi", "lem-sf-flat-model", "lem-sf-pullback-tor-amplitude", "lem-sf-tensor-ctf", "lem-sf-tor-sheaf-constructible", "lem-weil-pbc-pullback-preserves-bounded-constructible", "thm-dg-finite-type-constructibility"]
+++
The statements [lem-sf-flat-model], [lem-sf-tor-sheaf-constructible], [lem-sf-tensor-ctf], [lem-sf-pullback-tor-amplitude]
are formulated at the finite stages $A=A_{E,n}$. At the other three
stages of [def-weil-finite-tor-amplitude] they read as follows.
*Field stages:* $D^b_{ctf}(-,\Lambda)=D^b_c(-,\Lambda)$ for
$\Lambda\in\{E,\Qlb\}$ *by definition*, so the finite-Tor cells
there are the bounded-constructible cells of
[lem-sf-tensor-ctf], [thm-dg-finite-type-constructibility] and
[lem-weil-pbc-pullback-preserves-bounded-constructible].
*Integral stage:* for $K\in D^b_c(Y,\mathcal O_E)$ the definition
asks that every reduction $K\otimes_{\mathcal O_E}^LA_{E,j}$ have finite
Tor amplitude with one interval independent of $j$; pullback commutes with
these reductions, $(Lf^*K)\otimes_{\mathcal O_E}^LA_{E,j}\cong Lf^*(K\otimes_{\mathcal O_E}^LA_{E,j})$, because $Lf^*$ is monoidal and
carries the constant coefficient sheaf to the constant coefficient sheaf
([def-weil-derived-pullback-tensor-hom]), so
[lem-sf-pullback-tor-amplitude] gives the integral form of clause (i),
with the same interval, as soon as the reduction isomorphism
$Lf^*K\otimes_{\mathcal O_E}^LA_{E,j}\cong Lf^*(K\otimes_{\mathcal O_E}^LA_{E,j})$ and the derived completeness of
$Lf^*K$ are available; both are instances of the finite-reduction clause
proved for pullback in [lem-fix-operation-reduction]; clause (vii) of
the finite-Tor preservation summary is a later summary of this computation.
