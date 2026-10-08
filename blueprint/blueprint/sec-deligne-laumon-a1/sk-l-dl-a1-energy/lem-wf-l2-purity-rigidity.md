+++
id = "lem-wf-l2-purity-rigidity"
kind = "lemma"
title = "The $L^2$-weight of a punctually pure lisse sheaf equals its weight"
order = 2766
uses = ["def-weil-punctual-weights", "def-wf-constant-weil-twist", "def-wf-iota-real", "def-wf-l2-norm", "def-wf-normalized-real-envelope", "lem-tw-dual-negation", "lem-wf-constant-twist-weight", "lem-wf-envelope-real", "lem-wf-l2-upper", "thm-wf-l2-dictionary"]
+++
Let $X_0$ be a smooth geometrically connected affine curve over
$k_0=\mathbf F_q$, and let $\mathcal G$ be a nonzero lisse Weil sheaf
on $X_0$, punctually
$\iota$-pure of weight $w$. Then, in the $L^2$-weight parameter
$\|\cdot\|$ of [def-wf-l2-norm],

$$
\|\mathcal G\|=w .
$$

Thus the $L^2$-rigidity [thm-wf-l2-dictionary] does not in fact
need its hypothesis of $\iota$-reality: punctual purity of the weight
alone suffices, and in particular the rigidity applies to the
$\iota$-realizable sheaves of
[def-wf-iota-real].

## Proof

Write $\mathcal G^0=\mathcal G\otimes\mathcal B_b$ for the normalizing
twist of [def-wf-normalized-real-envelope], so that
$b=\iota^{-1}(q^{-w/2})$, i.e. $2\log_q|\iota(b)|=-w$; by
[lem-wf-constant-twist-weight] the sheaf $\mathcal G^0$ is
punctually $\iota$-pure of
weight $0$.

Step 1 (the twist shifts the $L^2$-weight by $w$). At a closed point
$y$ of degree $m$ the constant Weil twist
[def-wf-constant-weil-twist] has trace $t_{\mathcal B_b}(y)=b^m$,
so $t_{\mathcal G^0}(y)=b^{m}t_{\mathcal G}(y)$ and therefore
$\|f_{\mathcal G^0}\|_m^2=q^{-mw}\|f_{\mathcal G}\|_m^2$ for every
$m\ge1$. Substituting this into the defining ratio of
[def-wf-l2-norm], the ratio of $\mathcal G^0$ at the parameter
$\beta$ equals the ratio of $\mathcal G$ at the parameter
$\beta+w$; the two limit superiors are therefore positive for the same
parameters, and

$$
\|\mathcal G^0\|=\|\mathcal G\|-w .
$$

Step 2 (the envelope has $L^2$-weight zero). The envelope

$$
\mathcal E:=\operatorname{Env}_\iota(\mathcal G;b)
=\mathcal G^0\oplus\bigl(\mathcal G^0\bigr)^\vee
$$

of [def-wf-normalized-real-envelope] is $\iota$-real by
[lem-wf-envelope-real], and it is punctually $\iota$-pure of
weight $0$: the summand $\mathcal G^0$ is, and its linear dual is
too, because the dual of a weight-$0$ pure sheaf has the eigenvalues
$\alpha^{-1}$ with $|\iota(\alpha^{-1})|=1$, by
[lem-tw-dual-negation] read at weight $0$, while a direct sum of
two weight-$0$ pure sheaves is weight-$0$ pure. Since $\mathcal G$
is nonzero so is $\mathcal E$, and the dictionary
[thm-wf-l2-dictionary] applies to $\mathcal E$ with $w=0$:

$$
\|\mathcal E\|=0 .
$$

Step 3 (comparison with the envelope). By the eigenvalue computation in
the proof of [lem-wf-envelope-real], an eigenvalue $\beta_j$ of
$F_y$ on $\mathcal G^0_{\bar y}$ has $|\iota(\beta_j)|=1$, so the
eigenvalues of the dual summand are
$\iota(\beta_j^{-1})=\overline{\iota(\beta_j)}$; the trace of the
envelope at $y$ is therefore

$$
t_{\mathcal E}(y)=t_{\mathcal G^0}(y)+t_{(\mathcal G^0)^\vee}(y)
=2\operatorname{Re}\bigl(t_{\mathcal G^0}(y)\bigr).
$$

The elementary inequality
$|\operatorname{Re}z|^2\le|z|^2$ gives
$|t_{\mathcal E}(y)|^2\le4\,|t_{\mathcal G^0}(y)|^2$ at every closed
point, hence $\|f_{\mathcal E}\|_m^2\le4\|f_{\mathcal G^0}\|_m^2$ for
every $m$. In the defining ratio of [def-wf-l2-norm] this means
that a positive limit superior for $\mathcal E$ at a parameter
$\beta$ forces a positive limit superior for $\mathcal G^0$ at the
same parameter, so

$$
\|\mathcal E\|\le\|\mathcal G^0\| .
$$

With Step 2 this yields $\|\mathcal G^0\|\ge0$, while
[lem-wf-l2-upper] —applied to the punctually weight-$0$ mixed
sheaf $\mathcal G^0$ —yields $\|\mathcal G^0\|\le0$. Hence
$\|\mathcal G^0\|=0$, and Step 1 gives $\|\mathcal G\|=w$.
