+++
id = "thm-sc-serre-duality-curve"
kind = "theorem"
title = "Serre duality for smooth proper curves"
order = 702
uses = ["def-sc-curves", "def-sc-function-field", "def-sc-invertible-module", "def-sc-kahler-differentials", "lem-sc-canonical-sheaf", "lem-sc-deg-principal-zero", "lem-sc-finite-duality", "lem-sc-invertible-dual", "lem-sc-morphism-from-function", "lem-sc-p1-hi-vanishing", "lem-sc-smooth-regular", "lem-weil-pbc-finite-proper", "pqf-def-coherent", "pqf-lem-affine-vanishing", "pqf-lem-fff-vanishing", "pqf-lem-finite-qf", "pqf-lem-leray", "pqf-lem-leray-lowdegree", "pqf-lem-qf-finitefibres", "pqf-lem-sheaf-zero-stalks", "thm-pqf-finite-iff-proper-finite-fibres", "thm-sc-p1-duality"]
lean = ["AlgebraicGeometry.Scheme.serreDuality"]
+++
Let $k$ be an algebraically closed field, $C$ a
proper smooth connected curve over $k$ and
$\mathcal M$ a finite locally free $\mathcal O_C$-module (a
quasi-coherent module Zariski-locally isomorphic to
$\mathcal O_C^{\oplus r}$ for some $r\ge0$), with dual
$\mathcal M^{\vee}:=\mathcal H om_{\mathcal O_C}(\mathcal M,\mathcal O_C)$.
Put $n:=\dim C\in\{0,1\}$ and $\omega_C:=\Omega^n_{C/k}$, where
$\Omega^1_{C/k}$ is the sheaf of Kähler differentials of $C$
over $k$ ([def-sc-kahler-differentials]) and
$\Omega^0_{C/k}=\mathcal O_C$. Then all groups
$H^q(C,\mathcal M)$ and $H^q(C,\mathcal M^{\vee}\otimes\omega_C)$
are finite-dimensional $k$-vector spaces (coherent cohomology of a
proper scheme over a field is finite-dimensional: *Source:
Stacks Project, Cohomology of Schemes, Proposition 30.19.1,
[Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)*), and
for every $q\in\mathbf Z$ there is a canonical isomorphism

$$
H^q(C,\mathcal M)^{\vee}\;\cong\;
H^{n-q}\bigl(C,\;\mathcal M^{\vee}\otimes\omega_C\bigr)
$$

(both sides vanish unless $0\le q\le n$). In particular, for
$n=1$ and an invertible $\mathcal M$ ([def-sc-invertible-module],
so $\mathcal M^{\vee}\cong\mathcal M^{-1}$ by
[lem-sc-invertible-dual]):

$$
H^1(C,\mathcal M)^{\vee}\;\cong\;
H^0\bigl(C,\;\Omega^1_{C/k}\otimes\mathcal M^{-1}\bigr),
\qquad
H^0(C,\mathcal M)^{\vee}\;\cong\;
H^1\bigl(C,\;\Omega^1_{C/k}\otimes\mathcal M^{-1}\bigr).
$$

This is Serre duality $H^q(X,\mathcal F)^{\vee}\cong H^{n-q}(X,\mathcal F^{\vee}\otimes\omega_X)$
for a smooth proper $X$ of dimension $n\le1$ over an algebraically
closed field and a finite locally free $\mathcal F$. For a coherent
$\mathcal F$ which is not locally free the right hand side must be
replaced by $\operatorname{Ext}^{n-q}(\mathcal F,\omega_X)$, as in
[thm-sc-p1-duality]: e.g. for the skyscraper
$\mathcal F=\kappa(x)$ at a closed point $x$ of a curve,
$H^0(C,\mathcal F)^{\vee}=k$ but $\mathcal F^{\vee}=0$.

## Proof

The sheaf $\Omega^1_{C/k}$ is a line bundle
([lem-sc-canonical-sheaf]), so in both cases $\omega_C$ is a line
bundle and $\mathcal M^{\vee}\otimes\omega_C$ is again finite locally
free (on an open trivializing $\mathcal M$ and $\omega_C$ it is
$\mathcal O^{\oplus r}$). All modules below are finite locally free,
hence coherent on the Noetherian scheme $C$ ([pqf-def-coherent]),
which gives the finite-dimensionality.

*Reduction to $q=n$.* For finite locally free $\mathcal M$ the
canonical maps $\mathcal M\to\mathcal M^{\vee\vee}$ and
$\omega_C^{\vee}\otimes\omega_C\to\mathcal O_C$ are isomorphisms
(check on opens where the modules are free), so
$(\mathcal M^{\vee}\otimes\omega_C)^{\vee}\otimes\omega_C\cong\mathcal M$.
Hence, once the isomorphism
$H^n(C,\mathcal N)^{\vee}\cong H^0(C,\mathcal N^{\vee}\otimes\omega_C)$
is proved for every finite locally free $\mathcal N$, applying it to
$\mathcal N:=\mathcal M^{\vee}\otimes\omega_C$ gives
$H^n(C,\mathcal M^{\vee}\otimes\omega_C)^{\vee}\cong H^0(C,\mathcal M)$,
and dualizing (finite-dimensional spaces) gives the case $q=0$,
$H^0(C,\mathcal M)^{\vee}\cong H^n(C,\mathcal M^{\vee}\otimes\omega_C)$.
For $n=0$ the cases $q=0$ and $q=n$ coincide. It remains to show
the vanishing $H^q(C,\mathcal N)=0$ for $q\notin\{0,\dots,n\}$ and
every finite locally free $\mathcal N$ (for $q<0$ this is the
convention for derived functors), and the case $q=n$.

*Case $\dim C=0$.* The finite-type scheme $C$ has
finitely many points (it is Noetherian of dimension zero), so the
morphism $C\to\operatorname{Spec}k$ is proper with finite fibres,
hence finite by [thm-pqf-finite-iff-proper-finite-fibres]
(the quasi-finite chapter); thus $H^0(C,\mathcal O_C)$ is a
finite-dimensional
$k$-algebra, reduced because $C$ is smooth, and connected
because $C$ is connected, hence equal to $k$ (a reduced
finite-dimensional algebra over the algebraically closed field $k$
is a product of finitely many copies of $k$, and connectedness
leaves one factor). So $C=\operatorname{Spec}k$: then
$H^q(C,\mathcal N)=0$ for $q>0$ by [pqf-lem-affine-vanishing]
($\operatorname{Spec}k$ is affine, $\mathcal N$ quasi-coherent),
and a finite locally free $\mathcal N$ is the sheaf associated with
a finite-dimensional $k$-vector space $V=H^0(C,\mathcal N)$, with
$\mathcal N^{\vee}\otimes\omega_C=\mathcal N^{\vee}$ associated with
$\operatorname{Hom}_k(V,k)=V^{\vee}$; so
$H^0(C,\mathcal N)^{\vee}=V^{\vee}=H^0(C,\mathcal N^{\vee}\otimes\omega_C)$,
the case $q=n=0$. (Also $\Omega^1_{C/k}=0$: the module of
Kähler differentials of $k$ over $k$ is zero, the universal
derivation of the identity being $d=0$; this is why the sheaf
$\omega_C=\Omega^{\dim C}_{C/k}$ is $\mathcal O_C$ here.)

*Case $\dim C=1$.* The connected smooth curve $C$ is
integral: its local rings are domains ([lem-sc-smooth-regular]),
so its irreducible components are pairwise disjoint (a point
belonging to two components would have a local ring with two minimal
primes), and connectedness leaves a single component. The function
field $k(C)$
([def-sc-function-field]) has transcendence degree one over
$k$: for an integral scheme of finite type over a field,
$\dim X=\operatorname{trdeg}_k k(X)$, by Noether normalization
(*Source: Stacks Project, Commutative Algebra,
[Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)*; as in the
proof of [lem-sc-deg-principal-zero]). Choose
$t\in k(C)\setminus k$ (a transcendental element, since
$k\subset k(C)$ is a field extension and $k$ is algebraically
closed), and let $f:=\pi_t:C\to\mathbf P^1_k$ be the morphism of
[lem-sc-morphism-from-function]: finite, surjective and flat,
of degree $d:=[k(C):k(t)]$.

*Transfer of the cohomology.* The morphism $f$ is proper
(finite morphisms of schemes are proper,
[lem-weil-pbc-finite-proper] of the ambient-foundations chapter), and its fibres
are finite ([pqf-lem-finite-qf] and
[pqf-lem-qf-finitefibres] of the quasi-finite chapter); $\mathbf P^1_k$
is locally Noetherian (of finite type over the field $k$). Let
$\mathcal M$ be finite locally free. It is coherent (on the locally
Noetherian scheme $C$, a locally free module of finite type is
coherent: [pqf-def-coherent]), so [pqf-lem-fff-vanishing] gives
$(R^p f_*\mathcal M)_y=0$ for all $p>0$ and all
$y\in\mathbf P^1_k$, i.e. $R^pf_*\mathcal M=0$ for $p>0$
([pqf-lem-sheaf-zero-stalks]). The Leray spectral sequence
$E_2^{p,q}=H^p(\mathbf P^1_k,R^qf_*\mathcal M)\Rightarrow H^{p+q}(C,\mathcal M)$
([pqf-lem-leray]) is therefore concentrated on the row $q=0$ and
degenerates, giving $H^p(C,\mathcal M)\cong H^p(\mathbf P^1_k,f_*\mathcal M)$
for all $p$; in degree one this is the low-degree exact sequence of
[pqf-lem-leray-lowdegree]:

$$
H^1(C,\mathcal M)\cong H^1(\mathbf P^1_k,f_*\mathcal M),
\qquad
H^p(C,\mathcal M)\cong H^p(\mathbf P^1_k,f_*\mathcal M)=0\quad(p\ge2),
$$

the vanishing by [lem-sc-p1-hi-vanishing]. This is the vanishing
outside $\{0,1\}$ required in the reduction step.

Moreover $f_*\mathcal M$ is a finite locally free
$\mathcal O_{\mathbf P^1_k}$-module (of rank $d$): over an affine
open $U=\operatorname{Spec}R\subset\mathbf P^1_k$ the preimage
$f^{-1}(U)=\operatorname{Spec}B$ is affine with $B$ a finite
locally free $R$-algebra (finite flat), and
$f_*\mathcal M|_U$ is the finite locally free $R$-module
$\Gamma(f^{-1}(U),\mathcal M)$: the sections of a finite locally
free module on the affine scheme $\operatorname{Spec}B$ form a
finitely generated projective $B$-module, which is a finitely
generated projective $R$-module because $B$ is one (a direct summand
of $B^{\oplus m}$, and $B^{\oplus m}$ is finite projective over $R$);
if $\mathcal M$ has rank $r$, the generic rank is
$rd$, $d= \dim_{k(t)}k(C)$.

*Duality.* Since $f_*\mathcal M$ is finite locally free,
hence coherent, [thm-sc-p1-duality] gives

$$
H^1(\mathbf P^1_k,f_*\mathcal M)^{\vee}
\cong
\operatorname{Hom}_{\mathcal O_{\mathbf P^1}}
\bigl(f_*\mathcal M,\omega_{\mathbf P^1}\bigr),
$$

and since $f$ is finite flat, [lem-sc-finite-duality] gives

$$
\operatorname{Hom}_{\mathcal O_{\mathbf P^1}}
\bigl(f_*\mathcal M,\omega_{\mathbf P^1}\bigr)
\cong
H^0\bigl(C,\omega_C\otimes\mathcal M^{\vee}\bigr).
$$

Composing (the three isomorphisms are compatible with the
identification $\omega_C=\Omega^1_{C/k}$):

$$
H^1(C,\mathcal M)^{\vee}
\cong H^1(\mathbf P^1_k,f_*\mathcal M)^{\vee}
\cong \operatorname{Hom}_{\mathcal O_{\mathbf P^1}}
\bigl(f_*\mathcal M,\omega_{\mathbf P^1}\bigr)
\cong H^0\bigl(C,\mathcal M^{\vee}\otimes\Omega^1_{C/k}\bigr),
$$

which is the case $q=n=1$; by the reduction step this proves the
theorem. For invertible $\mathcal M$, [lem-sc-invertible-dual]
identifies $\mathcal M^{\vee}$ with $\mathcal M^{-1}$, which gives
the two displayed particular cases.
