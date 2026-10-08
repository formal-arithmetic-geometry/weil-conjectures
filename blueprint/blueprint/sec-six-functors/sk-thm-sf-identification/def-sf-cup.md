+++
id = "def-sf-cup"
kind = "definition"
title = "Mixed-support cup product"
order = 2184
uses = ["def-sf-datum", "def-weil-derived-tensor"]
+++
In the setting of [def-sf-datum], let $K,L\in D^b_{ctf}(X,\Lambda)$.
The *mixed-support cup product* is the composite

$$
\smile_c:R\Gamma_c(X,K)\otimes^L_\Lambda R\Gamma(X,L)\longrightarrow
R\Gamma_c\bigl(X,K\otimes^L_{\Lambda_X}L\bigr)
$$

of the projection transformation for $Ra_{X!}$ applied to the pair $(K,L)$
and the map induced by the counit $La_X^*Ra_{X*}L\to L$; the same
construction at the other coefficient stages is obtained by levelwise
application and transport, and it is associative, unital and
graded-commutative.
