+++
id = "lem-trf-compactification-graph-operator"
kind = "lemma"
title = "Extension by zero of a Frobenius coefficient morphism"
order = 2378
uses = ["def-trf-frobenius-coefficient-morphism", "def-trf-global-operator", "def-trf-graph-correspondence", "def-trf-scheme-frobenius", "def-weil-extension-by-zero", "lem-trf-adjoint-mate", "lem-trf-compactification-cohomology", "lem-trf-frobenius-open-square", "lem-trf-open-ctf", "lem-trf-open-square-exchange", "lem-weil-pbc-comparison-pullback", "prop-compactification-coherence-detailed", "prop-functor-package", "prop-trf-graph-operator"]
+++
Fix the global finite-field datum and the coefficient ring
$A=A_{E,n}$. Let $j_0:X_0\hookrightarrow\bar X_0$ be a
compactification over $k_0$ of a separated finite-type $k_0$-scheme,
with base change $j:X\hookrightarrow\bar X$ to $k$, and write
$\Phi=\Phi_X$, $\bar\Phi=\Phi_{\bar X}$ for the $q$-power scheme
Frobenii of [def-trf-scheme-frobenius]. For $m\geq0$ let

$$
b_m:L\bar\Phi^{m*}j_!\xrightarrow{\ \sim\ }j_!L\Phi^{m*}
$$

be the comparison isomorphism of [lem-trf-open-square-exchange] for the
Cartesian square of [lem-trf-frobenius-open-square] with
$(h,\bar h)=(\Phi^m,\bar\Phi^m)$. Let $K\in D^b_{ctf}(X,A)$ carry an
explicit etale-origin witness.

1. *Extension of coefficient morphisms.* For every morphism
$v:L\Phi^{m*}K\to K$ put
$$
\bar v=j_!v\circ b_m:\;L\bar\Phi^{m*}j_!K\longrightarrow j_!K .
$$
If $\psi:L\Phi^*K\to K$ is a Frobenius coefficient morphism of
[def-trf-frobenius-coefficient-morphism] (no invertibility assumed),
then $\bar\psi$ is a Frobenius coefficient morphism on
$j_!K\in D^b_{ctf}(\bar X,A)$, and its iterates are the extensions of
the iterates of $\psi$:
$$
(\bar\psi)_m=\overline{\psi_m}=j_!\psi_m\circ b_m\qquad(m\geq1).
$$
1. *Stalks.* Let $\bar y$ be a geometric point of $\bar X$ with
$\bar\Phi^m\bar y=\bar y$, and let $\bar v_{\bar y}$, $v_{\bar y}$ be
the induced stalk endomorphisms (through
$(L\bar\Phi^{m*}M)_{\bar y}\cong M_{\bar y}$). If $\bar y$ lies in
$X$, then $(j_!K)_{\bar y}=K_{\bar y}$ and $\bar v_{\bar y}=v_{\bar y}$;
otherwise $(j_!K)_{\bar y}=0$.
1. *Global operators.* For the graph correspondences
$c=(\operatorname{id}_X,\Phi^m)$ and
$\bar c=(\operatorname{id}_{\bar X},\bar\Phi^m)$ of
[def-trf-graph-correspondence], the comparison
$C_{j,K}:R\Gamma_c(X,K)\xrightarrow{\sim}R\Gamma(\bar X,j_!K)$ of
[lem-trf-compactification-cohomology] intertwines the global
operators of [def-trf-global-operator]:
$$
C_{j,K}\circ T_c(v)=T_{\bar c}(\bar v)\circ C_{j,K}.
$$

## Proof

*(1).* The complex $j_!K$ lies in $D^b_{ctf}(\bar X,A)$ by
[lem-trf-open-ctf], so $\bar\psi$ is a Frobenius coefficient morphism
on it. For the iterates, argue by induction on $m$, the case $m=1$
being the definition. The squares of [lem-trf-frobenius-open-square]
for $\bar\Phi$ and $\bar\Phi^{m-1}$ paste to the square for
$\bar\Phi^m$, so by the pasting clause of
[lem-trf-open-square-exchange], after the pullback composition
identifications,
$b_m=b_{1,L\Phi^{(m-1)*}K}\circ L\bar\Phi^*b_{m-1}$. Using the
recursion of [def-trf-frobenius-coefficient-morphism], the induction
hypothesis, and the naturality of $b_1$,

$$
(\bar\psi)_m=\bar\psi\circ L\bar\Phi^*(\bar\psi)_{m-1}
=j_!\psi\circ b_1\circ L\bar\Phi^*j_!\psi_{m-1}\circ
L\bar\Phi^*b_{m-1}
=j_!\psi\circ j_!L\Phi^*\psi_{m-1}\circ b_{1}\circ L\bar\Phi^*b_{m-1}
=j_!\psi_m\circ b_m .
$$

*(2).* Stalks of $j_!K$ are $K_{\bar y}$ on $X$ and $0$ off $X$ by
[def-weil-extension-by-zero]. For $\bar y$ in $X$ the stalk functor
factors through restriction to the open $X$; there
$j^*j_!=\operatorname{id}$ and $j^*b_m$ is the identity after the
pullback identifications (the normalization clause of
[lem-trf-open-square-exchange]), so $j^*\bar v=v$ and hence
$\bar v_{\bar y}=v_{\bar y}$.

*(3).* Write $M=L\Phi^{m*}K$, which again carries an explicit
etale-origin witness by [lem-weil-pbc-comparison-pullback], so that
$C_{j,M}$ is defined. By [prop-trf-graph-operator],

$$
T_c(v)=R\Gamma_c(X,v)\circ\iota_X\circ R\Gamma_c(X,\eta),\qquad
T_{\bar c}(\bar v)=R\Gamma(\bar X,\bar v)\circ\iota_{\bar X}\circ
R\Gamma(\bar X,\bar\eta),
$$

where $\eta:K\to R\Phi^m_*M$ and
$\bar\eta:j_!K\to R\bar\Phi^m_*L\bar\Phi^{m*}j_!K$ are the units, and
$\iota_X$, $\iota_{\bar X}$ are the identifications
$R\Phi^m_*\simeq R\Phi^m_!$ followed by the composition law for
$a_X\Phi^m=a_X$, respectively $a_{\bar X}\bar\Phi^m=a_{\bar X}$ (the
scheme Frobenius is a $k$-morphism). Let
$\gamma:j_!R\Phi^m_*M\xrightarrow{\sim}R\bar\Phi^m_*j_!M$ be the
composition isomorphism of the compact-support direct image for
$j\Phi^m=\bar\Phi^mj$ ([prop-functor-package], item (3), with
$R\Phi^m_*=R\Phi^m_!$ for the finite maps $\Phi^m$, $\bar\Phi^m$).

*Step A: the units.* We claim
$$
\gamma\circ j_!\eta=R\bar\Phi^m_*b_m\circ\bar\eta:\quad
j_!K\longrightarrow R\bar\Phi^m_*j_!M .
$$
By the adjunction $j_!\dashv j^*$ of [def-weil-extension-by-zero] it
suffices to compare the adjoint maps
$K\to j^*R\bar\Phi^m_*j_!M$. By the proof of
[lem-trf-open-square-exchange], $j^*R\bar\Phi^m_*=R\Phi^m_*j^*$ with
the comparison given by the identity on sections, and
$j^*j_!=\operatorname{id}$; under these identifications $j^*\gamma$ is
the identity of $R\Phi^m_*M$, both sides being computed by the same
section formula over objects of the site of $X$. Hence the adjoint
of the left-hand side is $\eta$. On the other hand, $b_m$ is, by its
construction in [lem-trf-open-square-exchange], the left-adjoint mate
of the equality $j^*R\bar\Phi^m_*=R\Phi^m_*j^*$ for the composite
adjunctions $L\bar\Phi^{m*}j_!\dashv j^*R\bar\Phi^m_*$ and
$j_!L\Phi^{m*}\dashv R\Phi^m_*j^*$; the unit compatibility of
[lem-trf-adjoint-mate], item (2), for this pair of adjunctions says
exactly that the adjoint of the right-hand side is also $\eta$. This
proves the claim.

*Step B: transport to cohomology.* The comparisons $C_{j,-}$ are
natural in the witnessed complex ([lem-trf-compactification-cohomology]),
so $C_{j,K}\circ R\Gamma_c(X,v)=R\Gamma(\bar X,j_!v)\circ C_{j,M}$.
They are compatible with the composition law of the compact-support
direct image ([prop-compactification-coherence-detailed]: the
comparison with the candidate $R\bar a_*j_!$ respects composition), which
gives
$$
C_{j,M}\circ\iota_X\circ R\Gamma_c(X,\eta)
=\iota_{\bar X}\circ R\Gamma(\bar X,\gamma\circ j_!\eta)\circ C_{j,K}.
$$
Substituting Step A and $j_!v\circ b_m=\bar v$ (naturality of
$\iota_{\bar X}$ moves $R\bar\Phi^m_*b_m$ past it), one obtains
$C_{j,K}\circ T_c(v)=R\Gamma(\bar X,\bar v)\circ\iota_{\bar X}\circ
R\Gamma(\bar X,\bar\eta)\circ C_{j,K}=T_{\bar c}(\bar v)\circ C_{j,K}$.
No invertibility of $v$ is used anywhere.
