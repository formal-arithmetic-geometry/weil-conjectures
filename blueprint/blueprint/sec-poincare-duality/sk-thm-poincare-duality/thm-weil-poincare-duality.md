+++
id = "thm-weil-poincare-duality"
kind = "theorem"
title = "Poincare duality for smooth proper schemes"
order = 2453
uses = ["cor-pod-reciprocal-eigenvalues", "cor-pod-untwisted-similitude", "def-coefficient-twists-detailed", "def-pod-dual-tate-datum", "def-trf-frobenius-operators", "def-weil-algebraically-closed-coefficients", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-frobenius-coefficient-twists", "def-weil-frobenius-detailed", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-ordinary-compact-cohomology", "def-weil-poincare-trace-cup", "def-weil-weil-sheaf-complex", "lem-fix-weil-operations", "prop-cohomological-finiteness", "thm-pod-degreewise-perfectness-over-a-field", "thm-pod-proper-poincare-duality", "thm-pod-qbar-coefficient-pairing", "thm-pod-trace-isomorphism"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, put $q=p^a$, and set
$k_0=\Fq$, and let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Fix a prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and choose an
algebraic closure $\Qlb$ of $\Ql$. Let $X_0/k_0$
be smooth, proper, geometrically
connected of pure dimension $d\in\mathbf Z_{\geq0}$, and put
$X=X_0\times_{k_0}k$. Let $a_X:X\to\Spec k$ be the structure
morphism and assume it is
exceptional-adjoint
admissible at $\Ql$. Let $Ra_X^!$ denote the
exceptional inverse image, and
choose an orientation isomorphism

$$
\eta_X:Ra_X^!\Ql\xrightarrow{\sim}(\Ql)_X(d)[2d]
$$

and let $K_X=(\Ql)_X$ with its
canonical Weil structure. Let $F$ be
the endomorphism of $R\Gamma(X,K_X)$ induced by the
global geometric Frobenius
with the normalization in the geometric
Frobenius convention; write $F$ for its induced automorphisms on every
$H^i(X,\Ql)$. Here $H^i$ and $H_c^i$ denote the
ordinary and compactly
supported cohomology groups, $\Ql(m)$ denotes the
Tate twist, and geometric Frobenius acts on
it by the specified twist
normalization. Then the Poincare duality interface holds: the trace
map

$$
\operatorname{tr}^{(-d)}_X:H^{2d}(X,\Ql)\xrightarrow{\sim}\Ql(-d)
$$

is an isomorphism, the groups $H^i(X,\Ql)$ are finite-dimensional
and vanish for $i\notin[0,2d]$, the
trace–cup-product pairings
$\langle-,-\rangle_i$ with values in $\Ql(-d)$ are perfect for
every $0\leq i\leq2d$ and satisfy

$$
\langle Fx,Fy\rangle_i=q^d\langle x,y\rangle_i
\qquad
(x\in H^i(X,\Ql),\ y\in H^{2d-i}(X,\Ql)),
$$

there is a Frobenius-equivariant duality isomorphism
$H^{2d-i}(X,\Ql)\simeq H^i(X,\Ql)^\vee(-d)$, under which the
eigenvalues of $F$ on $H^{2d-i}(X,\Ql)$ are the $q^d/\alpha$, with
multiplicity, for the eigenvalues $\alpha$ of $F$ on $H^i(X,\Ql)$, and
the base-change clause holds: for every finite extension $k_0'/k_0$
contained in $k$, with $r=[k_0':k_0]$ (so $\#k_0'=q^r$), the geometric
Frobenius of $k_0'$ acting on $H^i(X,\Ql)$, via the canonical
identification of $X_0\times_{k_0}k_0'$ base-changed to $k$ with $X$,
is $F^r$, the pairings $\langle-,-\rangle_i$ remain perfect, and

$$
\langle F^rx,F^ry\rangle_i=(q^r)^d\langle x,y\rangle_i
\qquad
(x\in H^i(X,\Ql),\ y\in H^{2d-i}(X,\Ql)).
$$

These six clauses are the items (Trace), (Finiteness), (Pairing),
(Frobenius similitudine), (Reciprocity) and (Base change) of the
detailed form below, read in the conventions fixed here; the
graded-commutativity part of (Pairing) is deduced from this theorem
in the following proposition on the Poincare pairing.

## Proof

The interface statement is the smooth-proper-geometrically-connected
case of the Poincare duality theorem of the Poincare-duality chapter,
[thm-weil-poincare-duality], whose six items (trace
isomorphism, finiteness, perfect pairings, Frobenius similitudine,
reciprocity, and base change) are the six clauses of the interface:
the trace map is the trace of [def-weil-poincare-trace-cup], the
finiteness item is the constant-sheaf case of
[prop-cohomological-finiteness], the Frobenius items use the
global operator of [def-weil-global-geometric-frobenius] with the
twist normalization of [def-weil-frobenius-coefficient-twists]
and the untwisted Frobenius similitude of
[cor-pod-untwisted-similitude], and the reciprocity and base
change are [cor-pod-reciprocal-eigenvalues] and the
Frobenius-operator convention of [def-trf-frobenius-operators]
together with $\operatorname{Frob}_{q^r}=\operatorname{Frob}_q^r$ from
[def-weil-frobenius-detailed]: the Frobenius of $k_0'$ is $F^r$, the
pairings are unchanged under the canonical identification of geometric
fibres (hence still perfect), and iterating the similitude $r$ times gives
$\langle F^rx,F^ry\rangle_i=q^{rd}\langle x,y\rangle_i=(q^r)^d\langle x,y\rangle_i$.
Both the
interface and [thm-weil-poincare-duality] are expressed in the
ordinary and compact-support conventions of
[def-weil-ordinary-compact-cohomology] and the Tate twist
conventions of [def-coefficient-twists-detailed], with the orientation
datum specified in the interface statement entering only through the
identification $\eta_X$ recorded there; the two statements therefore
agree clause by clause.

## Detailed form

Let $p$ be prime, let $a\in \mathbf Z_{\geq 1}$, put $q=p^a$, and set $k_0=\mathbf F_q$, and let $k=\overline{\mathbf F}_q$ be the fixed algebraic closure of $k_0$. Fix a prime $\ell \neq p$, write $\mathbf Q_{\ell }=\mathbf Q_\ell$, and choose an algebraic closure $\overline{\mathbf Q}_{\ell }$ of $\mathbf Q_{\ell }$. Let $X_0/k_0$ be smooth, proper, geometrically connected of pure dimension $d\in \mathbf Z_{\geq 0}$, and put $X=X_0\times _{k_0}k$. Let $a_X:X\to \operatorname{Spec}k$ be the structure morphism; no admissibility hypothesis is imposed on it, its exceptional inverse image $Ra_X^!$ being the constructible one of [def-weil-exceptional-inverse-image], which exists for every separated finite-type morphism (the ambient datum of [def-weil-exceptional-adjoint-admissibility], which fails for smooth proper curves, is not used). Let $K_X=(\mathbf Q_{\ell })_X$ be the constant Weil sheaf with its canonical structure, and let $F$ be the global geometric Frobenius endomorphism of $R\Gamma (X,K_X)$ in the geometric-Frobenius convention; write $F$ also for its automorphisms of the cohomology groups, and let $\langle -,-\rangle _i$ be the trace–cup-product pairing with values in the Tate twist $\mathbf Q_{\ell }(-d)$. Then:

*Trace.* The trace map

$$
\operatorname {tr}^{(-d)}_X:H^{2d}(X,\mathbf Q_{\ell })\xrightarrow {\  \sim \  }\mathbf Q_{\ell }(-d)
$$

is an isomorphism (Theorem 9.27).

*Finiteness.* For every integer $i$, $H^i(X,\mathbf Q_{\ell })$ is finite-dimensional, and it is zero for $i\notin [0,2d]$ (Proposition 1.58).

*Pairing.* The pairing

$$
H^i(X,\mathbf Q_{\ell })\times H^{2d-i}(X,\mathbf Q_{\ell })\longrightarrow \mathbf Q_{\ell }(-d)
$$

is perfect for every $0\leq i\leq 2d$ (Theorem 9.26 with $K=(\mathbf Q_{\ell })_X$, $\Lambda =\overline{\mathbf Q}_{\ell }$, via Theorem 9.35 for the $\overline{\mathbf Q}_{\ell }$-stage).

*Frobenius similitudine.* Geometric Frobenius acts on $\mathbf Q_{\ell }(-d)$ by $q^d$, and

$$
\langle Fx,Fy\rangle _i=q^d\langle x,y\rangle _i \qquad (x\in H^i(X,\mathbf Q_{\ell }),\  y\in H^{2d-i}(X,\mathbf Q_{\ell })),
$$

for every $0\leq i\leq 2d$ (Corollary 9.31 for the constant sheaf).

*Reciprocity.* For every finite-dimensional $\mathbf Q_{\ell }$-vector space $V$, write $V^\vee =\operatorname {Hom}_{\mathbf Q_{\ell }}(V,\mathbf Q_{\ell })$; then

$$
H^{2d-i}(X,\mathbf Q_{\ell })\simeq H^i(X,\mathbf Q_{\ell })^\vee (-d),
$$

Frobenius-equivariantly, and the eigenvalues of $F$ on $H^{2d-i}(X,\mathbf Q_{\ell })$ are the $q^d/\alpha$, with multiplicity, for the eigenvalues $\alpha$ of $F$ on $H^i(X,\mathbf Q_{\ell })$ (Theorem 9.26 and Corollary 9.32).

*Base change.* For every finite extension $k_0'/k_0$ contained in $k$, put

$$
r=[k_0':k_0],\qquad q'=\# k_0'=q^r,\qquad X_0'=X_0\times _{k_0}k_0', \qquad X'=X_0'\times _{k_0'}k,
$$

and identify $X'$ with $X$ by the canonical geometric-fiber identification; the base-change map is the pullback induced by $X'\to X$ on the complexes $R\Gamma (X,(\mathbf Q_{\ell })_X)$ and $R\Gamma (X',(\mathbf Q_{\ell })_{X'})$. Under this identification the geometric Frobenius for $k_0'$ is $F'=F^r$ (Definition 7.7), the pairings remain perfect, and

$$
\langle F^r x,F^r y\rangle _i=(q^r)^d\langle x,y\rangle _i
$$

for $x\in H^i(X,\mathbf Q_{\ell })$ and $y\in H^{2d-i}(X,\mathbf Q_{\ell })$.

## Proof

The coefficient stage is $\Lambda =\overline{\mathbf Q}_{\ell }$, the common-stage coefficients of [def-weil-algebraically-closed-coefficients], with the canonical datum. Item (1) is the proper clause of [thm-pod-trace-isomorphism] at $\Lambda =\overline{\mathbf Q}_{\ell }$ ($X_0$ being proper by hypothesis, so $H_c^{2d}=H^{2d}$); item (2) is [prop-cohomological-finiteness], whose statement in the smooth-proper-geometrically-connected case gives the vanishing outside $[0,2d]$ and the finite-dimensionality. Item (3): by [thm-pod-proper-poincare-duality] (applicable since $X_0$ is proper) with $K=(\mathbf Q_{\ell })_X$ and the $\overline{\mathbf Q}_{\ell }$-transport of [thm-pod-qbar-coefficient-pairing], the degreewise pairings $H^i(X,\mathbf Q_{\ell })\times H^{2d-i}(X,\mathbf Q_{\ell }(d))\to \mathbf Q_{\ell }$ are perfect, and eliminating the twist gives the line-valued perfect pairings with values in $\mathbf Q_{\ell }(-d)$, the definition of $\langle -,-\rangle _i$ in [def-weil-poincare-trace-cup] (the cup product of the master is the mixed-support cup product on a proper scheme, and the trace is the normalized smooth trace of the purity chapter restricted to the constant coefficients). Item (4): the constant sheaf $K_X$ with its canonical datum is self-dual in the canonical way; the datum on the dual is the canonical datum, and the Frobenius similitude $\langle Fx,Fy\rangle _i=q^d\langle x,y\rangle _i$ is the untwisted similitude of [cor-pod-untwisted-similitude] for $K=K_X$. Item (5): the duality isomorphism of [thm-pod-proper-poincare-duality] together with the degreewise isomorphism of [thm-pod-degreewise-perfectness-over-a-field] gives (transported to $\overline{\mathbf Q}_{\ell }$ via [thm-pod-qbar-coefficient-pairing]) $H^{2d-i}(X,\mathbf Q_{\ell })\cong H^i(X,\mathbf Q_{\ell })^\vee (-d)$, the equivariance being the duality-isomorphism compatibility of [def-pod-dual-tate-datum] and of [lem-fix-weil-operations], and the eigenvalue reciprocity is [cor-pod-reciprocal-eigenvalues]. Item (6): the base change consists in the identification of the geometric Frobenius $\operatorname {Frob}_{q'}=\operatorname {Frob}_q^r$ (the definition of the geometric-Frobenius convention, [def-weil-frobenius-detailed], and its incarnation on the geometric fiber via the canonical identification $X'=X$), the associated operator being the $r$-th iterate $F^r$ of [def-trf-frobenius-operators]; the pairings are the ones transported along the canonical identification of $X'$ with $X$, hence perfect, and the similitude is the $r$-fold iteration of item (4), whose $r$-th power acts by $q^{rd}=(q^r)^d$.
