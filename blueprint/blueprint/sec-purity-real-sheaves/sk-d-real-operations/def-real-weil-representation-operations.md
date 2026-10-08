+++
id = "def-real-weil-representation-operations"
kind = "definition"
title = "Operations on Weil representations"
order = 2586
uses = ["def-mg-determinant-line", "def-mg-weil-composition-series", "def-mg-weil-semisimplification", "def-wf-fundamental-representation", "def-wf-weil-group"]
+++
Let $X_0$ be as in [def-wf-fundamental-representation], with Weil group
$W=W(X_0)$ and degree map $\deg:W\to\mathbf Z$ of [def-wf-weil-group]. A
*Weil representation* is a finite-dimensional $\Qlb$-vector space $V$ with a
homomorphism $\rho:W\to\operatorname{GL}(V)$ whose restriction to the
geometric subgroup $\pi_1(X)$ is continuous; the Weil fundamental
representation of [def-wf-fundamental-representation] is one. For Weil
representations $V,V'$:

- the *direct sum* $V\oplus V'$ and the *tensor product* $V\otimes V'$
  carry the actions $g(v,v')=(gv,gv')$ and $g(v\otimes v')=gv\otimes gv'$;
- the *exterior power* $\bigwedge^rV$ carries
  $g(v_1\wedge\cdots\wedge v_r)=gv_1\wedge\cdots\wedge gv_r$; the top
  exterior power is the determinant line $\det V$ of [def-mg-determinant-line];
- the *dual* $V^\vee=\operatorname{Hom}(V,\Qlb)$ carries
  $(g\lambda)(v)=\lambda(g^{-1}v)$.

A Weil representation is *irreducible* if it is simple in the sense of
[def-mg-weil-composition-series]. Its *constituents* are the composition
factors of a composition series of [def-mg-weil-composition-series], counted
with multiplicity, and their direct sum is the semisimplification $V^{\mathrm{ss}}$
of [def-mg-weil-semisimplification]. For a
subgroup $I\subseteq W$ the *invariants* and *coinvariants* are

$$
V^I=\{v\in V:gv=v\text{ for all }g\in I\},\qquad
V_I=V/\langle gv-v:g\in I,\ v\in V\rangle .
$$

Uses: [def-mg-determinant-line], [def-mg-weil-composition-series], [def-mg-weil-semisimplification], [def-wf-fundamental-representation], [def-wf-weil-group]
