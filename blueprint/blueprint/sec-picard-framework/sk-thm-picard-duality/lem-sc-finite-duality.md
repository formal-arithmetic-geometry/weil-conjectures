+++
id = "lem-sc-finite-duality"
kind = "lemma"
title = "Duality along a finite flat morphism of smooth curves"
order = 697
uses = ["def-sc-curves", "def-sc-invertible-module", "def-sc-kahler-differentials", "lem-sc-invertible-dual", "lem-sc-regular-dim1-dvr", "lem-sc-smooth-regular"]
+++
Let $k$ be an algebraically closed field, $C$ a smooth
connected curve over $k$, $f:C\to\mathbf P^1_k$
a finite flat morphism of smooth $k$-curves, and $\mathcal M$ a
finite locally free $\mathcal O_C$-module (a quasi-coherent module which
is Zariski-locally isomorphic to $\mathcal O_C^{\oplus r}$ for some
$r\ge0$), with dual
$\mathcal M^{\vee}:=\mathcal H om_{\mathcal O_C}(\mathcal M,\mathcal O_C)$.
Then there is a canonical isomorphism

$$
\operatorname{Hom}_{\mathcal O_{\mathbf P^1}}\bigl(f_*\mathcal M,\;
\omega_{\mathbf P^1}\bigr)\;\cong\;
H^0\bigl(C,\;\omega_C\otimes\mathcal M^{\vee}\bigr);
$$

in particular, for an invertible $\mathcal M$
([def-sc-invertible-module]) the right hand side is
$H^0(C,\omega_C\otimes\mathcal M^{-1})$. Here $\omega_{\mathbf P^1}:=\Omega^1_{\mathbf P^1_k/k}$ and
$\omega_C:=\Omega^1_{C/k}$
([def-sc-kahler-differentials]).
(*Source: the classical Grothendieck duality for finite
morphisms – the trace/fundamental-class isomorphism
$\mathcal H om_{\mathcal O_{\mathbf P^1}}(f_*\mathcal O_C, \omega_{\mathbf P^1})\cong f_*\omega_C$ attached to a finite flat
morphism, i.e. Hartshorne, *Algebraic Geometry*, III, (6.10),
(6.12); the local algebra is the classical computation of the
different/codifferent of a finite flat extension of discrete
valuation rings, Serre, *Local Fields*, Ch. II, $\S$4.*)

## Proof

For a finite morphism of schemes and quasi-coherent
$\mathcal F$ on $C$, $\mathcal G$ on $\mathbf P^1_k$, there is
the adjunction

$$
\operatorname{Hom}_{\mathcal O_{\mathbf P^1}}(f_*\mathcal F,\mathcal G)
\;\cong\;
\operatorname{Hom}_{\mathcal O_C}\bigl(\mathcal F,\;
\mathcal H om_{\mathcal O_{\mathbf P^1}}(f_*\mathcal O_C,\mathcal G)\bigr),
$$

the standard adjunction of restriction of scalars: over an affine
$U=\operatorname{Spec}R\subset\mathbf P^1_k$ with
$f^{-1}(U)=\operatorname{Spec}B$ ($B$ a finite $R$-algebra, by
finiteness of $f$), both sides become
$\operatorname{Hom}_R(M,N)$ and
$\operatorname{Hom}_B(M,\operatorname{Hom}_R(B,N))$ for the
$B$-module $M$ and the $R$-module $N$, which agree by
$\phi\mapsto(m\mapsto(b\mapsto\phi(bm)))$ – commutative algebra.
Next, the trace identification: there is a canonical isomorphism

$$
\mathcal H om_{\mathcal O_{\mathbf P^1}}(f_*\mathcal O_C,
\omega_{\mathbf P^1})\;\cong\;f_*\omega_C.
$$

Both sides are Zariski-local on $\mathbf P^1_k$, so fix
$y\in\mathbf P^1_k$ and put $R:=\mathcal O_{\mathbf P^1,y}$,
$B:=(f_*\mathcal O_C)_y$: the ring $R$ and the factors of $B$
are discrete valuation rings (for a closed point: regular local of
dimension one, [lem-sc-smooth-regular],
[lem-sc-regular-dim1-dvr], applied to the smooth curves
$\mathbf P^1_k$ and $C$; for the generic point: the fields
$k(t)\subseteq k(C)$), and $R\to B$ is finite flat. For such
$R\to B$ the local theorem of the codifferent (commutative
algebra, classical) gives the canonical isomorphism

$$
\operatorname{Hom}_R\bigl(B,\Omega^1_{R/k}\bigr)\;\cong\;\Omega^1_{B/k}.
$$

The identification is canonical and local: at the generic point it
is the perfect trace pairing of the finite separable extension
$k(C)\supset k(t)$,
$\operatorname{Hom}_{k(t)}(k(C),k(t))=k(C)$, together with the
base change of the Kähler differentials
$\Omega^1_{k(C)/k}=k(C)\otimes_{k(t)}\Omega^1_{k(t)/k}$ (the
Kähler sequence, exact on the left since $k(C)/k(t)$ is
separable); at a closed point, with uniformizers $u$ of $R$ and
$x$ of the relevant factor of $B$, and ramification $u=x^{e}$,
the $R$-dual of $B$ has the
dual-basis generator $x^{-(e-1)}/e$, and the two sides of the
isomorphism become $B\,du\cdot x^{-(e-1)}/e$ and $B\,dx$, which
agree since $du=ex^{e-1}dx$. Since the resulting isomorphisms are
canonical, they glue to the displayed trace identification.
Combining the adjunction with $\mathcal F=\mathcal M$,
$\mathcal G=\omega_{\mathbf P^1}$, and the trace identification:

$$
\begin{gathered}
\operatorname{Hom}_{\mathcal O_{\mathbf P^1}}(f_*\mathcal M,\omega_{\mathbf P^1})\\
\cong
\operatorname{Hom}_{\mathcal O_C}\bigl(\mathcal M,\;
\mathcal H om_{\mathcal O_{\mathbf P^1}}(f_*\mathcal O_C,\omega_{\mathbf P^1})\bigr)\\
\cong
\operatorname{Hom}_{\mathcal O_C}(\mathcal M,f_*\omega_C)\\
=H^0\bigl(C,\mathcal H om_{\mathcal O_C}(\mathcal M,\omega_C)\bigr).
\end{gathered}
$$

As $\mathcal M$ is finite locally free, the natural map
$\omega_C\otimes\mathcal M^{\vee}\to\mathcal H om_{\mathcal O_C}(\mathcal M,\omega_C)$,
$w\otimes\phi\mapsto(m\mapsto\phi(m)w)$, is an isomorphism
(it is compatible with restriction to opens, and on an open where
$\mathcal M\cong\mathcal O_C^{\oplus r}$ both sides are
$\omega_C^{\oplus r}$ and the map is the identity), and
$H^0(C,\ldots)$ is the right hand side of the claim. For invertible
$\mathcal M$ one has moreover $\mathcal M^{\vee}\cong\mathcal M^{-1}$
by [lem-sc-invertible-dual] (the evaluation
$\mathcal M\otimes\mathcal M^{\vee}\to\mathcal O_C$ is an
isomorphism), which gives the particular case. The composite isomorphism is
canonical (it does not depend on the choices made in the local
computations).
