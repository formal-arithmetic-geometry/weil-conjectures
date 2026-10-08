+++
id = "lem-weil-pbc-reconstruction-uniform-tower"
kind = "lemma"
title = "Reconstruction of a uniform local tower"
order = 1251
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-bounded-constructible-tower", "def-weil-pbc-derived-inverse-limit", "def-weil-pbc-intrinsic-completion", "lem-weil-pbc-finite-reduction-reconstruction", "prop-weil-pbc-koszul-reconstruction"]
+++
Let $M_\bullet$ be a uniformly bounded constructible adic tower in the sense
of [def-weil-pbc-bounded-constructible-tower] and put $M=\Rlim M_\bullet$.
For every local model in [def-weil-pbc-bounded-constructible-tower],
restriction of the derived-limit projections gives a functorial isomorphism

$$
 L_{\alpha j}\xrightarrow{\sim}M|_{U_{\alpha j}}.
$$

Consequently $M$ is derived $I$-complete, the canonical maps

$$
 M\otimes_A^LP_n\xrightarrow{\sim}M_n
$$

are isomorphisms compatible with normalization, and $M$ has no cohomology
outside $[d_0,d_1]$. No finiteness assertion about the groups of sections on
$U_{\alpha j}$ is required.

That a derived limit of such a tower is derived $I$-complete is the criterion
of Stacks Project, Lemma 61.20.1 (Tag
[099M](https://stacks.math.columbia.edu/tag/099M), Section 61.20, Tag
[099L](https://stacks.math.columbia.edu/tag/099L)): the Stacks entry assumes
a Noetherian ring $\Lambda$ with an ideal $I$ and states the criterion
$K=\Rlim(K\otimes^L_\Lambda\underline{\Lambda/I^n})$ for a single object,
whereas the form used here reconstructs a uniform local tower from its models
$L_{\alpha j}$. The corresponding statement for the derived category is
Stacks Project, Proposition 61.29.7 (Tag
[09C7](https://stacks.math.columbia.edu/tag/09C7), Section 61.29, Tag
[09C0](https://stacks.math.columbia.edu/tag/09C0)): there an object of
$D_{cons}(X,\Lambda)$ on a Noetherian scheme is adic constructible. The
Stacks entry assumes a Noetherian ring $\Lambda$ with an ideal $I$ and a
Noetherian scheme, whereas the form used here is the tower-level local model
$L_{\alpha j}$, a bounded complex of finite locally constant $A_T$-modules.

## Proof

Restricted to the local model $U_{\alpha j}$ of
[def-weil-pbc-bounded-constructible-tower], the tower $M_\bullet$ is the
reduction tower $L_{\alpha j}\otimes^L(P_n)_T|_{U_{\alpha j}}$ of the local
finite-free model $L_{\alpha j}$ with the quotient transition maps; its
derived limit (in the sense of [def-weil-pbc-derived-inverse-limit]) is
$L_{\alpha j}\otimes^L_{A_T}\Rlim(P_n)_T|_{U_{\alpha j}} =L_{\alpha j}$,
since $L_{\alpha j}$ is a bounded complex of finite locally free modules and
$\Rlim(P_n)_T=A_T$ by [def-weil-pbc-adic-coefficient-datum]; the
derived-limit projections realize the displayed isomorphism $L_{\alpha
j}\xrightarrow{\sim}M|_{U_{\alpha j}}$. Applying
[prop-weil-pbc-koszul-reconstruction] to the tower $M_\bullet$ gives that $M$
is derived $I$-complete in the sense of
[def-weil-pbc-intrinsic-completion], and
[lem-weil-pbc-finite-reduction-reconstruction] applied to the local towers
gives the isomorphisms $M\otimes_A^LP_n\xrightarrow{\sim}M_n$, compatible
with the normalization maps; the bounds $[d_0,d_1]$ and the absence of any
finiteness assertion on section groups are properties of the local models.
