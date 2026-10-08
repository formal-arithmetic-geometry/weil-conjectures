+++
id = "rem-sf-constant-tower-trivial-model"
kind = "remark"
title = "The trivial coefficient case, in one line"
order = 2204
uses = ["def-weil-pbc-bounded-constructible-tower"]
+++
If the complex $M_0$ of
*Stage-independent local models for a constant tower* is itself a bounded complex of
finite locally constant $A_T$-modules concentrated in degrees $[a,b]$,
then no construction is needed: putting $L=M_0$ exhibits the tower as the
reduction tower of one bounded complex of finite locally constant
$A_T$-modules,

$$
M_n=M_0\otimes^L_{\mathcal O_E}A_{E,n}
=L\otimes^L_{A_T}(P_n)_T,
$$

which is the uniformity clause of
[def-weil-pbc-bounded-constructible-tower] verbatim, with the identity
cover. This is the ``trivial coefficient'' case: the constant local system
at every coefficient stage, and every bounded complex of finite locally
constant sheaves whose stages are its reductions; in particular a bounded
flat model of $M_0$ whose terms are finite locally constant may be taken
as the stage-independent model and base changed to every stage. The point
of *Stage-independent local models for a constant tower* is that the same conclusion
holds under the weaker hypothesis that the *stages* are lisse with one
Tor amplitude bound, no single finite locally constant model of $M_0$
being assumed.
