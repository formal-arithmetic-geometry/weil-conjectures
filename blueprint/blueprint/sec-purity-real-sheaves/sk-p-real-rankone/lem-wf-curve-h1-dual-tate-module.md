+++
id = "lem-wf-curve-h1-dual-tate-module"
kind = "lemma"
title = "Untwisted integral classes form the dual Tate module"
order = 2621
uses = ["def-sc-jacobian", "def-weil-pbc-etale-cohomology", "def-wf-abelian-tate-module", "lem-wf-curve-finite-level-pd", "lem-wf-curve-kummer-jacobian-tate-module", "lem-wf-geometric-jacobian-galois-action", "thm-av-final", "thm-pod-equivariance-of-the-twisted-pairing"]
+++
Let $C_0/k_0$ be a smooth projective geometrically connected curve,
let $C=C_0\times_{k_0}\overline{k}_0$, and let $J$ be its
Jacobian, equipped with the canonical semilinear
$\operatorname{Gal}(\overline{k}_0/k_0)$-action of
[lem-wf-geometric-jacobian-galois-action]. Put
$A_n=\mathbf Z/\ell^n\mathbf Z$. There is a natural Galois-equivariant
isomorphism

$$
\varprojlim_n H^1_{\mathrm{\acute et}}(C,A_n)
\xrightarrow{\sim}
\operatorname{Hom}_{\mathbf Z_\ell}(T_\ell J,\mathbf Z_\ell).
\tag{4.1}
$$

Here $\ell\ne\operatorname{char}k_0$, and the inverse limit uses the
reduction maps in the coefficient system.
The Tate module and etale cohomology are those of
[def-wf-abelian-tate-module], [def-weil-pbc-etale-cohomology].

## Proof

At level $n$, the finite-level pairing lemma
[lem-wf-curve-finite-level-pd] gives the adjoint isomorphism

$$
H^1(C,A_n)\xrightarrow{\sim}
\operatorname{Hom}_{A_n}\bigl(H^1(C,A_n(1)),A_n\bigr).
\tag{4.2}
$$

The equivariance and compatibility under reduction are those of
[thm-pod-equivariance-of-the-twisted-pairing]. By
[lem-wf-curve-kummer-jacobian-tate-module], the second factor is
$J[\ell^n](\overline{k}_0)$. Thus (4.2) gives natural compatible
Galois-equivariant isomorphisms

$$
H^1(C,A_n)\xrightarrow{\sim}
\operatorname{Hom}_{A_n}
\bigl(J[\ell^n](\overline{k}_0),A_n\bigr).
\tag{4.3}
$$

The transition maps
$J[\ell^{n+1}](\overline{k}_0)\xrightarrow{[\ell]} J[\ell^n](\overline{k}_0)$ are surjective by
[thm-av-final](d). We spell out the resulting quotient
description. Put $r=2\dim J$. By
[thm-av-final](c), the level-one group is
$(\mathbf Z/\ell\mathbf Z)^r$; choose a basis and lift its vectors
successively through the displayed surjections. At level $n$, the chosen
lifts form a basis of the free
$\mathbf Z/\ell^n\mathbf Z$-module $J[\ell^n](\overline{k}_0)$: their
reductions form a basis modulo $\ell$, so elementary Nakayama (or the
usual row-reduction over the local ring $\mathbf Z/\ell^n\mathbf Z$)
shows that they generate, and equality of the cardinalities
$\ell^{nr}$ makes the resulting surjection an isomorphism. The compatible
bases identify the whole inverse system with
$(\mathbf Z/\ell^n\mathbf Z)^r$ under reduction. Consequently
$T_\ell J\cong\mathbf Z_\ell^r$ ([thm-av-final](d)), every projection is surjective, and its
kernel is exactly $\ell^nT_\ell J$. Thus the projections give canonical
isomorphisms (independent of the bases used to prove them)

$$
J[\ell^n](\overline{k}_0)\cong T_\ell J/\ell^nT_\ell J.
$$

Consequently

$$
\varprojlim_n\operatorname{Hom}_{A_n}
(J[\ell^n](\overline{k}_0),A_n)
\cong
\varprojlim_n\operatorname{Hom}_{\mathbf Z_\ell}
(T_\ell J/\ell^nT_\ell J,\mathbf Z_\ell/\ell^n\mathbf Z)
\cong \operatorname{Hom}_{\mathbf Z_\ell}(T_\ell J,\mathbf Z_\ell).
$$

The last map sends a homomorphism to its reductions; it is bijective because
$T_\ell J$ is finite free over $\mathbf Z_\ell$, as just proved. Only
ordinary inverse limits are used here; no derived-limit comparison is being
invoked. Although bases were used to verify the quotient description, the
projections, pairings, and reduction maps themselves are canonical and
Galois equivariant. This proves (4.1) with its Galois action.
