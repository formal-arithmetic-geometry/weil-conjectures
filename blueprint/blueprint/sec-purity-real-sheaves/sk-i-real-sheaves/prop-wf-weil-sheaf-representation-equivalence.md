+++
id = "prop-wf-weil-sheaf-representation-equivalence"
kind = "theorem"
title = "The lisse sheaf–representation equivalence"
order = 2584
uses = ["cor-galois-lisse-representations", "d-real-setup", "def-wf-fundamental-representation", "def-wf-weil-group", "lem-wf-weil-fundamental-representation"]
tags = ["latex:proposition"]
+++
Throughout, $C_0$ is the curve and $C$ its base
change to $k$; $P=\pi_1(C)$ is the geometric fundamental group, $W(C_0)$ the
Weil group with degree map and chosen degree-one lift $\gamma$, and
$E\subset\Qlb$ a finite coefficient field with valuation ring
$\mathcal O_E$ and maximal ideal $\mathfrak m_E$, all as in
[def-wf-weil-group]. A lisse Weil sheaf $\mathcal F$ on $C_0$ has geometric
generic stalk $\mathcal F_{\bar\eta}$.

The functor $\mathcal F\mapsto(V,\rho)=(\mathcal F_{\bar\eta}, \rho_{\mathcal F})$, the representation of [def-wf-fundamental-representation] (continuous by [lem-wf-weil-fundamental-representation]), is an exact tensor equivalence between lisse Weil sheaves
on $C_0$ and the representations of [def-wf-weil-group]: a short exact
sequence $0\to\mathcal F'\to\mathcal F\to\mathcal F''\to0$ corresponds to
$0\to V'\to V\to V''\to0$. Subobjects, quotients and subquotients therefore
match on the two sides, in both directions.

## Proof

*Finite level.* Each $\mathcal O_E/\mathfrak m_E^n$ is a finite ring, so
[cor-galois-lisse-representations] identifies locally constant sheaves of finite free
$\mathcal O_E/\mathfrak m_E^n$-modules on $C$ with finite free modules over
that ring carrying a continuous $P$-action. Rank is a property of the stalk
and is constant because $C$ is connected.

*Integral and rational levels.* A lisse adic model has surjective
transition maps, so the stalks $M_n$ form a surjective system whose limit is
finite free over $\mathcal O_E$, with continuous action because the
$\mathfrak m_E$-adic topology is the limit of the discrete quotient
topologies; levelwise reduction inverts the construction. Morphism groups
are the limits of their finite-level counterparts,
$\Hom_{\mathcal O_E[P]}(M,N)=\varprojlim_n\Hom_P(M_n,N_n)$: a map of adic
systems is by definition a compatible family of finite-level maps, while
$\Hom_{\mathcal O_E}(M,N)$ is finite free with reductions $\Hom(M_n,N_n)$
and $P$-invariants commute with inverse limits. The transition maps of
this tower need not be surjective (for $E=\mathbf Q_3(\zeta_3)$,
$\pi=\zeta_3-1$, a trivial lattice and the lattice of a cubic Kummer
character agree modulo $\pi$, but every equivariant map between them modulo
$\pi^2$ satisfies $\pi a=0$ and reduces to zero), but each
$\Hom_P(M_n,N_n)$ is a finite group, so the tower is Mittag–Leffler and
$\varprojlim^1$ vanishes; this is all the inverse-limit argument needs: a
compatible family of finite-level maps has a unique lift, and two maps
agreeing at every level are equal. Hence the functor is fully faithful.
Inverting the uniformizer on morphisms and passing to the filtered colimit
over the finite $E\subset\Qlb$ are each given by a universal property and are
performed the same way on both sides, so the equivalence descends to the
coefficients of [d-real-setup].

*Frobenius descent.* Geometric Frobenius is an automorphism of the
scheme $C$, so $\Frob^*$ is an autoequivalence of lisse sheaves on $C$;
comparing the stalks at $\bar\eta$ and $\Frob(\bar\eta)$ along the
degree-one lift $\gamma$ turns it into a twist of $\rho$ by the conjugation
$c_\gamma(g)=\gamma g\gamma^{-1}$ of $P$, and the comparison is oriented
so that the twist is $\rho\mapsto\rho\circ c_\gamma^{-1}$,
$g\mapsto\rho(\gamma^{-1}g\gamma)$ (the opposite orientation amounts to
replacing $\gamma$ by the degree $-1$ lift $\gamma^{-1}$). A Weil
structure $\varphi:\Frob^*\mathcal F\to\mathcal F$ is therefore an
automorphism $\Phi$ of $V$ with
$\Phi\,\rho(g)\,\Phi^{-1}=\rho(\gamma g\gamma^{-1})$ for $g\in P$, which is
exactly the relation making $g\gamma^{n}\mapsto\rho(g)\Phi^{n}$
multiplicative; since every element of $W(C_0)$ is uniquely $g\gamma^{n}$
by [def-wf-weil-group], setting $\rho(\gamma)=\Phi$ extends $\rho$ to
$W(C_0)$. (With the relation written as
$\Phi\,\rho(\gamma g\gamma^{-1})\,\Phi^{-1}=\rho(g)$ one would be forced to
set $\rho(\gamma)=\Phi^{-1}$ instead.) The choice $\rho(\gamma)=\Phi$ is
the geometric Frobenius normalization of [def-wf-weil-group]: at a closed
point $x$ with $k(x)=\Fq$ the operator induced by $\varphi$ on
$\mathcal F_{\bar x}$ is the geometric Frobenius $F_x$, because $\Frob$
composed with the arithmetic Frobenius of $k$ is the absolute Frobenius of
$C$, which acts trivially on etale sheaves, and $F_x$ has degree $+1$; so
the degree-one elements $g\gamma$ of $W(C_0)$ act through $\Phi$, not
$\Phi^{-1}$, in agreement with $F=\rho(\gamma)$ and with the Tate line
$\Qlb(1)=\mathcal B_{q^{-1}}$ (geometric Frobenius acts on $\Qlb(1)$ by
$q^{-1}$), in the notation of the constant Weil twist
[def-wf-constant-weil-twist]. Another lift changes
$\Phi$ by an element of $\rho(P)$ and gives an isomorphic representation. The
morphism condition $u\varphi=\psi\,\Frob^{*}u$ says on stalks that $u$
intertwines the two operators $\Phi$, which with $P$-equivariance is exactly
$W(C_0)$-equivariance; hence full faithfulness.

*Exactness.* Exactness and tensor products are levelwise for adic
systems and survive the localization and the filtered colimit, and Weil
kernels and cokernels are computed on the underlying sheaves. The matching
of subobjects, quotients and subquotients follows.
