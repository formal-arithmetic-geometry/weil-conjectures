+++
id = "def-tate-module-abelian-group"
kind = "definition"
title = "Tate module of an abelian group"
lean = ["AddCommGroup.tateModule", "AddCommGroup.rationalTateModule"]
order = 468
+++
For the prime $\ell$ and an abelian group $M$, put

$$
M[\ell^n]=\{x:\ell^nx=0\},\qquad
T_\ell M=\{(t_n)_{n\ge1}:t_n\in M[\ell^n],\ \ell t_{n+1}=t_n\}.
$$

The ring $\Zell$ consists of compatible residues
$c_n\in\mathbf Z/\ell^n\mathbf Z$ under reduction.
It acts by $(ct)_n=c_nt_n$, independently of the integer representative
of $c_n$. Define $\Qell=\Zell[1/\ell]$ and
$V_\ell M=T_\ell M[1/\ell]$. A fraction is written $\ell^{-b}t$;
the equality of fractions $\ell^{-b}t=\ell^{-c}u$ means that
$\ell^d(\ell^ct-\ell^bu)=0$ for some $d\ge0$.
An automorphism $s$ of $M$ acts coordinatewise and on fractions, and
$(V_\ell M)^s$ denotes its fixed submodule.
