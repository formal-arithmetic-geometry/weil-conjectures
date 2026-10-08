+++
id = "def-sp-kinjective-bridge"
kind = "definition"
title = "The K-injective bridge"
order = 517
uses = ["def-sp-grothendieck-abelian", "def-sp-left-exact-additive"]
+++
A *K-injective resolution* of a complex $K$ is a quasi-isomorphism $K\to I$
with $I$ K-injective: for every acyclic complex $A$ the complex
$\operatorname{Hom}(A,I)$ is acyclic. In a Grothendieck abelian category
[def-sp-grothendieck-abelian] every bounded-below complex admits a
K-injective resolution.

This is what carries a left exact additive functor
[def-sp-left-exact-additive] from objects to complexes, and it is the bridge
the name refers to. For $v:\mathcal A\to\mathcal B$ left exact additive and
$K\in\operatorname{Ch}^+(\mathcal A)$, choose a K-injective resolution $K\to
I$ and set

$$
 RvK:=v(I),\qquad R^pv(K):=\mathcal H^p(RvK).
$$

That the choice of resolution does not matter, and that for an object $X$
placed in degree zero this agrees with the derived functors $R^pv(X)$ defined
by injective resolutions, is [lem-sp-kinjective-computes]; until that lemma
the notation is read as depending on the chosen resolution. This is the only
meaning $Rv$ has on complexes anywhere in the chapter.

**Status.** The source defines $Rv$ only on objects, in
[def-sp-left-exact-additive], and then uses $RvK$ for complexes in the
truncation couple, in the shift rule and in both hypercohomology spectral
sequences without ever saying what it is. Each of the two statements that
could have fixed it — the Cartan--Eilenberg theorem [thm-sp-if-e1] and the
comparison lemma [lem-sp-kinjective-computes] — was left appealing to the
other, which is what made their proofs circular. The definition is stated
here instead, and both proofs now rest on it.
