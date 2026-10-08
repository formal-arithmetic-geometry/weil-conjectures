+++
id = "sk-thm-poincare-duality"
kind = "section"
title = "Poincaré duality"
order = 2452
uses = ["sk-cor-trace", "sk-def-pairing", "sk-def-set", "sk-def-sf-operations", "sk-def-trace-cup", "sk-def-weil", "sk-lem-finite", "sk-prop-sf-biduality-general", "sk-prop-sf-dualizable-biduality", "sk-thm-derived-duality", "sk-thm-frobenius", "sk-thm-purity-transport", "sk-thm-sf-global-duality", "sk-thm-sf-identification", "sk-thm-sf-kunneth-relative", "sk-thm-sf-package", "sk-thm-sf-tensor-hom", "sk-thm-sf-verdier-exchange", "sk-thm-transport"]
+++
*Theorem (sketch).*

Let $p$ be prime, $a\ge1$, $q=p^a$, $k_0=\Fq$, $k=\overline{\mathbf F}_q$, $\ell\ne p$. Let $X_0/k_0$ be smooth, proper and geometrically
connected of pure dimension $d$, and put $X=X_0\times_{k_0}k$ with
structure morphism $a_X:X\to\Spec k$ (no admissibility hypothesis: the
exceptional adjoint used is the unconditional one of
[sk-def-sf-operations](vi), [sk-def-set]). Let
$K_X=(\Ql)_X$ with its canonical Weil structure, $F$ the geometric
Frobenius on $\RGamma(X,K_X)$ and on the $H^i(X,\Ql)$, and
$\langle-,-\rangle_i$ the trace–cup pairing with values in $\Ql(-d)$.
Then:

1. **(1)** *Trace.*
$\operatorname{tr}^{(-d)}_X:H^{2d}(X,\Ql)\xrightarrow{\sim}\Ql(-d)$ is an
isomorphism;
1. **(2)** *Finiteness.* $H^i(X,\Ql)$ is
finite-dimensional for all $i$ and vanishes for $i\notin[0,2d]$;
1. **(3)** *Pairing.* $H^i(X,\Ql)\times H^{2d-i}(X,\Ql)\to\Ql(-d)$ is perfect for every $0\le i\le 2d$, and
$\langle y,x\rangle_{2d-i}=(-1)^i\langle x,y\rangle_i$;
1. **(4)** *Frobenius similitudine.* $F$ acts on
$\Ql(-d)$ by $q^d$ and
$\langle Fx,Fy\rangle_i=q^d\langle x,y\rangle_i$;
1. **(5)** *Reciprocity.*
$H^{2d-i}(X,\Ql)\cong H^i(X,\Ql)^\vee(-d)$ Frobenius-equivariantly, with
eigenvalues $q^d/\alpha$ on the left for the eigenvalues $\alpha$ of
$F$ on the right, with multiplicity;
1. **(6)** *Base change.* For every finite extension
$k_0'/k_0$ contained in $k$ with $r=[k_0':k_0]$, the geometric
Frobenius of $k_0'$ is $F^r$, the pairings remain perfect and
$\langle F^rx,F^ry\rangle_i=(q^r)^d\langle x,y\rangle_i$.

(Blueprint 15, thm:pod-poincare-duality; the interface record is
thm:weil-poincare-duality, and prop:poincare-pairing adds the
graded-commutativity form of (3).)

## Proof

Item (1) is [sk-cor-trace] at the stage $\Qlb$: the degreewise duality
of [sk-thm-derived-duality] with $K=K_X$ and $i=0$, together with
$H^0(X,\Ql)\cong\Ql$ and properness ($R\Gamma_c=R\Gamma$), gives
$H^{2d}(X,\Ql)\cong\Ql(-d)$. Item (2): the vanishing outside $[0,2d]$ and
the finite-dimensionality are the constant-sheaf and finiteness clauses of
[sk-lem-finite] — at the algebraic closure the dimension bound is
fin4-lem-fibrewise-cohomological-dimension — transported to the
$\Qlb$-stage by [sk-thm-transport]. Item (3): the degreewise form of
[sk-thm-derived-duality] with $K=K_X$ gives the perfectness of each
$\langle-,-\rangle_i$ after that transport, and the graded-commutativity
clause $\langle y,x\rangle_{2d-i}=(-1)^i\langle x,y\rangle_i$ is the
graded-commutativity of the cup product entering the definition of the
pairing ([sk-def-trace-cup]). Items (4) and (5) are [sk-thm-frobenius]
at the field stage $\Qlb$: the similitude is its untwisted clause (a), and
the eigenvalue statement is clause (b), the
conjugation of $F_{K^\vee}$ with $q^d(F_{c,K}^{-1})^{\mathsf t}$ together
with the invariance of the characteristic polynomial under transposition.
Item (6): if $k_0'/k_0$ has degree $r$, then the geometric Frobenius of
$k_0'$ is the $r$-th iterate of $F$, by the Frobenius-operator
convention of [sk-def-weil]; the pairings remain perfect because
$\beta_K$ is built from base change along the structure morphism and the
orientation, both stable under the finite extension $k_0'/k_0$; and the
similitude clause of [sk-thm-frobenius] applied to $F^r$ in place of
$F$ gives $\langle F^rx,F^ry\rangle_i=(q^r)^d\langle x,y\rangle_i$.

Uses: [sk-cor-trace], [sk-def-pairing], [sk-def-set], [sk-def-trace-cup], [sk-def-weil], [sk-lem-finite], [sk-prop-sf-biduality-general], [sk-prop-sf-dualizable-biduality], [sk-thm-derived-duality], [sk-thm-frobenius], [sk-thm-purity-transport], [sk-thm-sf-global-duality], [sk-thm-sf-identification], [sk-thm-sf-kunneth-relative], [sk-thm-sf-package], [sk-thm-sf-tensor-hom], [sk-thm-sf-verdier-exchange], [sk-thm-transport]
