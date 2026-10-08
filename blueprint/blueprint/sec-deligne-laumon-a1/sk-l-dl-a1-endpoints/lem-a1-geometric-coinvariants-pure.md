+++
id = "lem-a1-geometric-coinvariants-pure"
kind = "lemma"
title = "Purity of the geometric coinvariants"
order = 2730
uses = ["def-weil-frobenius-module-weights", "def-weil-punctual-weights", "def-wf-fundamental-representation", "p-linear-filtration"]
+++
Let $U_0$ be a nonempty smooth geometrically connected curve over
$k_0=\mathbf F_q$, and let $\mathcal F$ be a lisse Weil sheaf on $U_0$
which is punctually $\iota$-pure of weight $w$. For its geometric
fundamental representation $V$ ([def-wf-fundamental-representation]),
the coinvariant quotient $W=V_{\pi_1(U)}$ — the maximal geometrically
constant quotient of $\mathcal F$ — with its induced Frobenius $F_W$ is
$\iota$-pure of weight $w$ (possibly $W=0$).

## Proof

The geometric subgroup $\pi_1(U)$ of the Weil group of
[def-wf-fundamental-representation] is normal, so the subspace of $V$
spanned by the vectors $gv-v$, $g\in\pi_1(U)$, is stable under the Weil
group and $V\twoheadrightarrow W$ is a quotient Weil representation. On
$W$ the geometric subgroup acts trivially, so the action of any element
of degree one of the Weil group on $W$ is a single operator $F_W$,
independent of the chosen lift; an element of degree $d$ acts by
$F_W^d$.

Choose a closed point $x\in U_0$ (a maximal ideal of the coordinate
ring of a nonempty affine open; its residue field is finite over
$\mathbf F_q$) and put $d=[\kappa(x):\mathbf F_q]$. A local Frobenius
at $x$ is an element of degree $d$ of the Weil group, and under the
identification of $V$ with the stalk $\mathcal F_{\bar x}$ it acts as
the operator $F_x$ of [def-weil-punctual-weights]. Hence
$V\twoheadrightarrow W$ is an $F_x$-equivariant quotient onto
$(W,F_W^d)$. In a basis of $V$ extending a basis of the kernel, the
matrix of $F_x$ is block upper triangular ([p-linear-filtration]), so
every eigenvalue of $F_W^d$ is an eigenvalue of $F_x$ on
$\mathcal F_{\bar x}$, and has $\iota$-modulus
$|\kappa(x)|^{w/2}=q^{dw/2}$ by punctual purity
([def-weil-punctual-weights]). If $\lambda$ is an eigenvalue of $F_W$,
then $\lambda^d$ is an eigenvalue of $F_W^d$, so
$|\iota(\lambda)|^d=q^{dw/2}$ and $|\iota(\lambda)|=q^{w/2}$. Thus
$(W,F_W)$ is $\iota$-pure of weight $w$ in the sense of
[def-weil-frobenius-module-weights].
