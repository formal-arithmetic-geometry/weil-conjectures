+++
id = "lem-pc-universal-adjoint-section"
kind = "lemma"
title = "The adjoint section of the normalized universal module"
order = 830
uses = ["def-pc-genus", "def-pc-hilb-functor", "def-pc-rational-point", "def-pc-separably-closed", "def-pc-zero-scheme", "def-sc-effective-cartier-divisor", "lem-pc-universal-divisor", "lem-pc-zero-scheme-recd"]
+++
Let $k$ be a separably closed field,
let $X$ be a smooth projective curve of genus $g$ over $k$ with a
$k$-rational point $\sigma$, let $H=\underline{\operatorname{Hilb}}^g_{X/k}$ and let
$D_{\mathrm{univ}}\subset H\times X$ be the universal divisor of
[lem-pc-universal-divisor]. On $W_0:=H$ the sheaf
$\mathcal{N}_H:=f_{H,*}\mathcal{O}(D_{\mathrm{univ}})$ is a quasi-coherent
$\mathcal{O}_H$-module, and the canonical section $1$ of
$\mathcal{O}(D_{\mathrm{univ}})\otimes f_H^*\mathcal{N}_H^{-1}$ (which is canonically
isomorphic to
$\mathcal{L}_H\otimes f_H^*\mathcal{N}_H^{-1}$, where
$\mathcal{L}_H=\mathcal{O}(D_{\mathrm{univ}})\otimes\mathrm{pr}_H^*\sigma_H^*\mathcal{O}(D_{\mathrm{univ}})^{-1}$,
because the $\sigma$-terms cancel) has zero scheme
$Z(1)=D_{\mathrm{univ}}\subset H\times X$; moreover this section is the
adjoint section of $\mathcal{L}_H$ for the module $\mathcal{N}_H$, i.e. it corresponds
under the adjunction of [lem-pc-zero-scheme-recd] on the open
$W\subseteq H$ where $\mathcal{N}_H$ is invertible.

## Proof

$\mathcal{O}(D_{\mathrm{univ}})$ is invertible on $H\times X$, and its canonical
global section $1\in H^0(H\times X,\mathcal{O}(D_{\mathrm{univ}}))$ is defined as
the generator $1$ of the ideal sheaf $\mathcal{I}_{D_{\mathrm{univ}}}$ viewed as a
section of $\mathcal{O}(D_{\mathrm{univ}})=\mathcal{I}_{D_{\mathrm{univ}}}^\vee$; by
definition of the zero scheme
([def-pc-zero-scheme]), $Z(1)=D_{\mathrm{univ}}$. The canonical
isomorphism

$$
\begin{gathered}
\mathcal{L}_H\otimes f_H^*\mathcal{N}_H^{-1}\\
=\mathcal{O}(D_{\mathrm{univ}})\otimes f_H^*\sigma_H^*\mathcal{O}(D_{\mathrm{univ}})^{-1}\\
\otimes f_H^*\bigl(f_{H,*}\mathcal{O}(D_{\mathrm{univ}})\otimes
\sigma_H^*\mathcal{O}(D_{\mathrm{univ}})^{-1}\bigr)^{-1}\\
\cong\mathcal{O}(D_{\mathrm{univ}})\otimes f_H^*\bigl(f_{H,*}\mathcal{O}(D_{\mathrm{univ}})\bigr)^{-1}
\end{gathered}
$$

shows that the section $1\otimes 1$ of the right-hand side corresponds to
the canonical section with zero scheme $D_{\mathrm{univ}}$ (tensoring by
the unit section $1$ of the extra factor does not change the zero
scheme), and the adjunction of [lem-pc-zero-scheme-recd] identifies
$H^0(H\times X,\;\mathcal{L}_H\otimes f_H^*\mathcal{N}_H^{-1})$ with
$\Hom_{\mathcal{O}_H}(\mathcal{N}_H,f_{H,*}\mathcal{L}_H)$; the section $1\otimes 1$ is the image
of the canonical map, which is exactly the identification induced by the
universal property. Hence it is the adjoint section; its restriction to
any open $W\subseteq H$ over which $\mathcal{N}_H$ is invertible is the adjoint
section of $\mathcal{L}_H|_W$ in the sense of [lem-pc-zero-scheme-recd].
