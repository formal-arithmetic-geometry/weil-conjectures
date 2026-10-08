+++
id = "def-fd-additive-character"
kind = "definition"
title = "Additive characters"
order = 2672
lean = ["AddChar.FiniteField.primitiveChar"]
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $k$ be a finite field or an algebraic closure of one, and let
$p=\operatorname{char}k$. A *nondegenerate additive character*
of $k$ is a nontrivial homomorphism

$$
\psi:(k,+)\longrightarrow\overline{\mathbf Q}_\ell^\times.
$$

For a finite field $k_0=\mathbf F_q$ with trace
$\operatorname{Tr}:k_0\to\mathbf F_p$, the character
$\psi(x)=\Psi(\operatorname{Tr}(x))$, for a fixed nontrivial
$\Psi:\mathbf F_p\to\overline{\mathbf Q}_\ell^\times$, is called
*the* nondegenerate additive character. For $a\in k_0^\times$ the scalings
$\psi_a(x)=\psi(ax)$ are again nondegenerate characters.

*Recorded in advance* from chapter *Fourier–Deligne transform* of the source.
