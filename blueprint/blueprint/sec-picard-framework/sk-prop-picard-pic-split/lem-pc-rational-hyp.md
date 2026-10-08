+++
id = "lem-pc-rational-hyp"
kind = "lemma"
title = "Curves with a rational point satisfy the hypotheses"
order = 816
uses = ["def-pc-rational-point", "def-pc-smooth-projective-curve", "lem-pc-flat-base-change-cohom", "lem-pc-flat-field", "lem-pc-h0-proper-variety", "lem-pc-structure-pushforward", "thm-pc-pic-split"]
+++
(Picard Schemes of Curves, Lemma 44.6.1, Tag
[0B9U](https://stacks.math.columbia.edu/tag/0B9U).)
Let $k$ be a field and let $X$ be a
smooth projective curve over
$k$ which has a $k$-rational point $\sigma$. Then the hypotheses of
[thm-pc-pic-split] (with $S=\operatorname{Spec}(k)$, $f:X\to\operatorname{Spec}(k)$) are
satisfied: $f$ has the section $\sigma$, and
$\mathcal{O}_T\to f_{T,*}\mathcal{O}_{X_T}$ is an isomorphism for every
$T\in\operatorname{Ob}((\mathit{Sch}/k)_{fppf})$.

## Proof

The section $\sigma$ verifies the first condition. By
[lem-pc-h0-proper-variety] (1) (or the first part of Varieties,
Lemma 33.26.2), $k':=H^0(X,\mathcal{O}_X)$ is a finite field extension of $k$;
the $k$-rational point induces a $k$-algebra homomorphism $k'\to k$, and
a field homomorphism over $k$ is injective, so $k'=k$. Hence
$f_*\mathcal{O}_X=\mathcal{O}_k$, and for $T\in(\mathit{Sch}/k)_{fppf}$: the structure morphism
$T\to\operatorname{Spec}(k)$ is flat ([lem-pc-flat-field]), so by
[lem-pc-flat-base-change-cohom] applied to $f:X\to\operatorname{Spec} k$ and
Flat $\mathcal{F}=\mathcal{O}_X$,

$$
f_{T,*}\mathcal{O}_{X_T}=g^*f_*\mathcal{O}_X=g^*\mathcal{O}_k=\mathcal{O}_T
$$

where $g:T\to\operatorname{Spec}(k)$; this is [lem-pc-structure-pushforward], as $H^0(X,\mathcal{O}_X)=k$. This proves the claim.
