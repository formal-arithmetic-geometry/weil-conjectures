+++
id = "lem-sc-kernel-subgroup"
kind = "lemma"
title = "Kernels are closed subgroup schemes"
lean = ["CategoryTheory.GrpObj.ker"]
order = 425
uses = ["def-sc-group-scheme", "def-sc-group-scheme-subgroup", "def-weil-pbc-scheme-conventions"]
+++
Let $f:G\to H$ be a homomorphism of
group schemes over a field $k$, and let $e_H$ be the unit
section of $H$. Then

$$
N:=G\times_{H,f,e_H}\Spec k,
$$

the kernel of $f$ in the sense of [def-sc-group-scheme], is a
group scheme over $k$ with $N(R)=\ker\bigl(f(R)\bigr)$ for every
$k$-algebra $R$, and the projection $N\to G$ exhibits $N$ as a
closed subgroup scheme of
$G$.

## Proof

First, every $k$-rational point $s:\Spec k\to X$ of a
$k$-scheme $X$ is a closed immersion (in the sense of
[def-weil-pbc-scheme-conventions]). Let $x$ be the image point of
$s$. For an affine open $U=\Spec B\subseteq X$ containing $x$, the
morphism $s$ corresponds to a $k$-algebra map $B\to k$, which is
surjective because it is $k$-linear and sends $1$ to $1$; so
$s^{-1}(U)=\Spec k\to U$ is a closed immersion and $x$ is closed in
$U$ (its prime is the kernel of $B\to k$, a maximal ideal). The point
$x$ is closed in $X$: if $y\in\overline{\{x\}}$ and $V$ is an affine
open containing $y$, then $V$ meets $\{x\}$, so $x\in V$ and $y$ lies
in the closure of $x$ in $V$, which is $\{x\}$. Hence for an affine
open $U$ not containing $x$ we have $s^{-1}(U)=\emptyset$, and $s$ is
affine and locally induced by surjective ring maps, i.e. a closed
immersion. Applying this to $e_H:\Spec k\to H$, the unit section is a
closed immersion, and its base change $N\to G$ is a closed immersion.
(In particular no separatedness hypothesis on $H$ is needed.)

For a $k$-algebra $R$, the $R$-points of $N$ are the pairs
$(\varphi,\psi)$ with $\varphi:\Spec R\to G$,
$\psi:\Spec R\to\Spec k$ and $f\circ\varphi=e_H\circ\psi$; the
second component is unique, so $N(R)=\{g\in G(R):f(R)(g)=e_H\}$.
Since $f$ is a
homomorphism of group schemes, $f(R)$
is a homomorphism of groups ([def-sc-group-scheme]), so $N(R)$
is a subgroup of $G(R)$ and $N(R)\to G(R)$ is injective.

It remains to see that $N$ carries a group scheme structure. Let
$R$ be a $k$-algebra and let $\varphi,\psi:\Spec R\to N$ be
$R$-points, with images $g,g'\in N(R)\subseteq G(R)$. The composite
$\Spec R\xrightarrow{(\varphi,\psi)}N\times_kN\to G\times_kG \xrightarrow{m_G}G$ is a morphism $t:\Spec R\to G$ with

$$
f\circ t=m_H\circ(f\circ\varphi,f\circ\psi)
=m_H\circ(e_H,e_H)=e_H,
$$

the last equality being the unit axiom for the group scheme $H$. By
the universal property of the fibre product $N$, the morphism $t$
factors uniquely through $N\to G$; this defines
$m_N:N\times_kN\to N$ with $j\circ m_N=m_G\circ(j\times j)$, where
$j:N\to G$ is the closed immersion. The same argument applied to
$i_G$ and $e_G$ (using $i_H\circ e_H=e_H$ and
$m_H\circ(e_H,e_H)=e_H$) defines $i_N:N\to N$ and
$e_N:\Spec k\to N$ with $j\circ i_N=i_G\circ j$ and
$j\circ e_N=e_G$. The associativity, unit and inverse axioms for
$(m_N,i_N,e_N)$ follow from those of $G$ after composing with the
monomorphism $j$; hence $N$ is a group scheme
([def-sc-group-scheme]) and $j$ is a homomorphism, so $N$ is a
closed subgroup scheme of
$G$, that is, a subgroup scheme of $G$ in the sense of
[def-sc-group-scheme-subgroup] whose structure morphism is a closed
immersion.
