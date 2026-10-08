+++
id = "def-weil-frobenius-coefficient-twists"
kind = "definition"
title = "Frobenius on coefficient twists"
order = 1888
uses = ["def-coefficient-twists-detailed", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-scheme-morphism-properties"]
+++
Fix the finite-field datum [def-weil-finite-field-fiber] $p,a,q,k_0,k$, where
$q=p^a$, and a prime $\ell\neq p$. Write $\Ql=\mathbf Q_\ell$, choose an
algebraic closure $\Qlb$ of $\Ql$, and choose a finite extension $E/\Ql$
contained in $\Qlb$. On $\Spec k_0$ and its geometric fiber
[def-weil-scheme-morphism-properties], use the Tate-twist construction
[def-coefficient-twists-detailed]; its natural Weil isomorphism is induced by
the geometric Frobenius convention [def-weil-frobenius-detailed]. Geometric
Frobenius acts on $E(1)$ by $q^{-1}$, on $E(m)$ by $q^{-m}$, and on $E(-m)$
by $q^m$, for every $m\in\mathbf Z_{\geq0}$. These actions commute with
finite reduction and scalar extension to $\Qlb$; in particular, the action on
$E(-d)$ is multiplication by $q^d$ for every $d\in\mathbf Z_{\geq0}$.
