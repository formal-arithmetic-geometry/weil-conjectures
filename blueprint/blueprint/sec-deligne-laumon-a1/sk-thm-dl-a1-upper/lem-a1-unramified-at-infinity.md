+++
id = "lem-a1-unramified-at-infinity"
kind = "lemma"
title = "Removing a regular point to arrange infinity"
order = 2800
uses = ["def-weil-open-closed-recollement", "def-weil-ordinary-compact-cohomology", "def-weil-pbc-scheme-conventions", "def-weil-punctual-weights", "def-wf-middle-extension", "lem-a1-finite-boundary-cohomology", "lem-wf-dense-open-pi1-surjective", "prop-sf-open-closed-triangle-all-stages"]
+++
Let $\mathcal F$ be a punctually pure lisse Weil sheaf of weight $w$
on a dense open $U_0\subset\mathbf A^1_{k_0}$.
After a finite constant-field extension, there are a dense open
$V_0\subset\mathbf A^1$ and a lisse sheaf $\mathcal E$ on $V_0$
of the same weight, with trivial local inertia at infinity, together
with a Frobenius-equivariant surjection

$$
H_c^1(V,\mathcal E)\twoheadrightarrow H_c^1(U,\mathcal F).
$$

Geometric irreducibility is preserved.

## Proof

Choose a geometric point $s\in U$, defined over a finite extension.
Over a further finite extension choose
$\tau\in\mathrm{PGL}_2$ with $\tau(s)=\infty$.
Set $V_0=\tau(U_0\setminus\{s\})\subset\mathbf A^1$ and let
$\mathcal E$ be the transported restriction.
It extends lisse across infinity, since $\mathcal F$ was lisse at
$s$; hence its inertia there is trivial.
Restriction to a dense open preserves geometric irreducibility:
the fundamental group of that open surjects onto the fundamental
group of the original smooth curve, by
[lem-wf-dense-open-pi1-surjective] (parts (1) and (4)).
The isomorphism $\tau$ and restriction preserve the local
weight condition of [def-weil-punctual-weights].

Open–closed recollement, [def-weil-open-closed-recollement], whose triangle exists for
$\Qlb$-Weil sheaves by [prop-sf-open-closed-triangle-all-stages],
and the vanishing of $H_c^1$ on the single point from
[lem-a1-finite-boundary-cohomology] give a surjection
$H_c^1(U\setminus\{s\},\mathcal F)\to H_c^1(U,\mathcal F)$.
Transport by $\tau$ gives the asserted map in the convention of
[def-weil-ordinary-compact-cohomology].
