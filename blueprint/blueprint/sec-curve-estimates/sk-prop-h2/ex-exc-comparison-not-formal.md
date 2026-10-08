+++
id = "ex-exc-comparison-not-formal"
kind = "remark"
title = "Full faithfulness does not identify ambient right adjoints"
order = 986
tags = ["latex:example"]
uses = ["def-weil-pbc-derived-categories"]
+++
In ordinary derived
categories, even full faithfulness of the comparison functors and
agreement of the left adjoints on their images do not suffice to make
the right-adjoint comparison invertible.

## Proof

Let $k$ be a field and write $D(k)$ for the ordinary derived
category, in the sense of [def-weil-pbc-derived-categories], of
$k$-vector spaces. Take the etale-side source and target both to
be $D(k)$, with $F_{\mathrm{et}}=G_{\mathrm{et}}=\mathrm{id}$.
Take the other source to be $D(k)\times D(k)$, its target to be
$D(k)$, and set

$$
v_X(M)=(M,0),\quad v_Y=\mathrm{id},\quad
F_{\mathrm{proet}}(M,N)=M\oplus N.
$$

Both comparison functors are fully faithful and
$F_{\mathrm{proet}}v_X=\mathrm{id}$. But
$G_{\mathrm{proet}}(K)=(K,K)$, as follows by applying the Hom
universal property of a finite direct sum. The comparison is
$(K,0)\to(K,K)$; it fails to be an isomorphism for every nonzero
$K$. This is an abstract counterexample to the proposed inference,
not a counterexample concerning schemes.
