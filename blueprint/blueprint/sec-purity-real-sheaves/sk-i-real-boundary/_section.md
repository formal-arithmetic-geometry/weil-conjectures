+++
id = "sk-i-real-boundary"
kind = "section"
title = "Boundary stalks and restriction to an open"
order = 2642
uses = ["sk-d-real-boundary", "sk-d-real-setup", "sk-d-real-weil"]
lean = ["AlgebraicGeometry.Scheme.isConstructibleSheaf_lowerStar", "AlgebraicGeometry.Scheme.isIso_unit_upperStarLowerStarAdjunction"]
+++
*Proposition (sketch).*

In the situation of [sk-d-real-boundary]: the sheaf $J=j_*\mathcal F$
is constructible, and $J_{\bar s}=V_s^{I_s}$ equivariantly for Frobenius.
If $\mathcal G$ is lisse on all of $C_0$, then
$\mathcal G\simeq j_*(\mathcal G|_{U_0})$. The map
$\pi_1(U)\to\pi_1(C)$ is surjective, and hence so is the Weil-group map
of [sk-d-real-weil].

## Proof

*Step 0 (normality).* $C_0$ is a smooth curve, hence normal and
integral, and a *quasi-compact* etale scheme $W$ over a normal
integral Noetherian scheme is a finite disjoint union of open-and-closed
normal integral schemes: $W$ is Noetherian, its local rings are normal
domains because normality ascends along etale ring maps
([Stacks `033C`](https://stacks.math.columbia.edu/tag/033C)),
so its finitely many irreducible components are pairwise disjoint (a point
on two of them would give two minimal primes of its local domain) and
hence open and closed. Quasi-compactness cannot be dropped:
$\coprod_{m\in\mathbf N}\operatorname{Spec}k\to\operatorname{Spec}k$ is
etale but not a finite disjoint union. Every etale scheme to which this is
applied below is quasi-compact: the finite etale covers of Steps 1 and 4
and the affine etale $W\to Y$ of Step 3.

*Step 1 (constructibility of $J$).* A lisse $\Qlb$-sheaf need not
be trivialized by any finite etale cover (on $\mathbf G_m$ the unipotent
Kummer extension, on which $\mathbf Z_\ell(1)$ acts by
$\left(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\right)$, has infinite
geometric monodromy), so the argument is made at the finite levels
$\mathcal F_n$ of an $\mathcal O_E$-model of $\mathcal F$, which are
locally constant sheaves of finite $\mathcal O_E/\mathfrak m_E^n$-modules.
Trivialize $\mathcal F_n$ by a
finite etale surjection $p:P\to U_0$, so that $p^*\mathcal F_n$ is constant
with finite fibre $M_a$ on each connected component $P_a$. The
adjunction unit $\mathcal F_n\to p_*p^*\mathcal F_n$ is injective, being a
diagonal into a nonempty finite product on stalks, so
$j_*\mathcal F_n\hookrightarrow\prod_a(jp_a)_*\underline{M_a}$. Extend $P_a$ to the
normalization $g_a:Y_a\to C_0$ in $k(P_a)$, which is finite and restricts
over $U_0$ to $P_a$; by Step 3 below applied on the normal integral
$Y_a$, the constant sheaf extends, so
$(jp_a)_*\underline{M_a}=g_{a,*}\underline{M_a}$, which is constructible
because $g_a$ is finite. A finite product of constructible sheaves is
constructible, and on a Noetherian scheme a subobject of a constructible
sheaf is constructible; hence $j_*\mathcal F_n$ is, for every $n$. For
$J$ itself no trivializing cover is needed: $J|_{U_0}=\mathcal F$ is
lisse, and at each of the finitely many boundary points $s$ the stalk
$J_{\bar s}=V_s^{I_s}$ of Step 2 is a finite-dimensional representation of
the residue Weil group, so $J$ is lisse on each stratum of
$U_0\sqcup(C_0\setminus U_0)$, i.e. constructible in the sense of
[sk-d-real-weil].

*Step 2 (the boundary stalk).* The stalk of $J$ at a geometric
boundary point $\bar s$ is computed on the punctured strict henselian
trait at $s$. The strict-henselization stalk formula is a statement
about torsion sheaves, so it is applied at each finite level: it
identifies $(j_*\mathcal F_n)_{\bar s}$ with the invariants $M_n^{I_s}$ of
the finite-level geometric generic stalk under the inertia group
$I_s=\Gal(\overline{K_s}/K_s^{\mathrm{sh}})$. The geometric stalk of the
adic sheaf $J$ is formed from these levels,
$J_{\bar s}=(\varprojlim_nM_n^{I_s})\otimes_{\mathcal O_E}E$; invariants
commute with inverse limits, so $\varprojlim_nM_n^{I_s}=M^{I_s}$ for the
lattice $M=\varprojlim_nM_n$ of $V_s$, and $M^{I_s}=M\cap V_s^{I_s}$ is
saturated in $M$, so $M^{I_s}\otimes_{\mathcal O_E}E=V_s^{I_s}$. (The
tower $(M_n^{I_s})_n$ need not be adic; only its limit enters.) Hence
$J_{\bar s}=V_s^{I_s}$,
where $K_s$ is the fraction field of the henselization as in
[sk-d-real-boundary] and $K_s^{\mathrm{sh}}\subset\overline{K_s}$ is
the fraction field of the strict henselization, the generic point of the
trait. Since $\Gal(K_s^{\mathrm{sh}}/K_s)=\Gal(\overline{k(s)}/k(s))$,
this is the kernel of
$\Gal(\overline{K_s}/K_s)\to\Gal(\overline{k(s)}/k(s))$ of
[sk-d-real-boundary], whereas $\Gal(\overline{K_s}/K_s)$ itself is the
decomposition group.
The Weil structures descend through the trait, so the identification is
equivariant for the residue Frobenius lift.

*Step 3 (lisse sheaves extend from a dense open).* For a finite
module $M$ on a normal integral Noetherian $Y$ and a nonempty open
$v:V\hookrightarrow Y$, the canonical map
$\underline M_Y\to v_*\underline M_V$ is an isomorphism: evaluate on an
affine etale $W\to Y$, decompose $W$ by Step 0, and note that each
component meets $W\times_YV$ because it is integral and $V$ is dense, so
a section over $W\times_YV$ is determined by, and extends to, a section
over $W$. For $\mathcal G$ lisse on $C_0$, trivialize each finite level
$\mathcal G_n$ as in Step 1 and apply this componentwise to get
$\mathcal G_n\simeq j_*(\mathcal G_n|_{U_0})$ for every $n$; these
isomorphisms are compatible in $n$ and $j_*$ of an adic sheaf is formed
levelwise, so $\mathcal G\simeq j_*(\mathcal G|_{U_0})$. (Equivalently,
Step 2 at $s\in C_0\setminus U_0$ gives
$J_{\bar s}=\mathcal G_{\bar s}^{I_s}=\mathcal G_{\bar s}$, inertia acting
trivially on the stalk of a sheaf lisse at $s$.)

*Step 4 (surjectivity on fundamental groups).* Let $W\to C$ be
connected finite etale. By Step 0 it is normal integral, hence its
restriction $W\times_CU$ is again integral, so connected: a connected
cover of $C$ stays connected over the nonempty open $U$. Equivalently
$\pi_1(U)\to\pi_1(C)$ is surjective. The Weil-group map of
[sk-d-real-weil] is the pullback of this one along the degree map to
$\mathbf Z$, so it is surjective too.

The detailed forms are Blueprint 07, `lem-fin-normal-open-lisse-image`
(Step 1), `lem-fin-normal-constant-open-image` (Step 3),
`lem-fin-etale-normal-components` (Steps 0 and 4),
`fin2-lem-lisse-trivialized-finite-etale` and
`lem-fin-normalization-extends-cover`; and Blueprint 12,
`lem-wf-boundary-stalk-invariants` (Step 2), resting on
Blueprint 02, `prop-weil-pbc-strict-henselization-stalk-formula`.

Uses: [sk-d-real-boundary], [sk-d-real-setup], [sk-d-real-weil]
