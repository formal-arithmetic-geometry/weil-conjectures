+++
id = "sk-thm-sf-ctf-stability"
kind = "section"
title = "Stability of the constructible finite-Tor subcategories"
order = 2202
uses = ["sk-cor-sf-direct-image-ctf", "sk-def-sf-operations", "sk-def-sf-setting", "sk-prop-sf-comparison", "sk-prop-sf-rf-shriek-preservation", "sk-thm-sf-direct-image-tor-amplitude", "sk-thm-sf-hom-ctf"]
lean = ["AlgebraicGeometry.Etale.constructibleFiniteTor_leftDerivedUpperStar", "AlgebraicGeometry.Etale.constructibleFiniteTor_tensor", "AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar", "AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriek", "AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedUpperShriek"]
+++
*Theorem (sketch).*

For separated finite-type morphisms $f:X\to Y$ of finite-type $k$-schemes
($k=\overline{\mathbf F}_q$ as in [sk-def-sf-setting]; the dimension bounds
below are those of these schemes, which is what justifies the global
amplitude shifts) and complexes in the stated finite-Tor
domains, *each clause being a statement about the functor of
[sk-def-sf-operations] between the small categories written in it*:
(i) the functor $Lf^*:\Dctf(Y,\Lambda)\to\Dctf(X,\Lambda)$ is defined;
(ii) $-\otimes^L_\Lambda-:\Dctf(Y,\Lambda)\times\Dctf(Y,\Lambda)\to \Dctf(Y,\Lambda)$ and
$\RHom_\Lambda(-,-):\Dctf(Y,\Lambda)^{\mathrm{op}}\times\Dctf(Y,\Lambda)\to \Dctf(Y,\Lambda)$ are defined, with Tor amplitudes
$[a,b]+[c,d]\mapsto[a+c,b+d]$ and, for $\dim Y\le m$,
$[a,b],[c,d]\mapsto[c-b-2m,d-a+2m]$, sharpened to $[c-b,d-a]$ when the first
argument is site-perfect;
(iii) $Rf_*:\Dctf(X,\Lambda)\to\Dctf(Y,\Lambda)$ is defined;
(iv) $Rf_!:\Dctf(X,\Lambda)\to\Dctf(Y,\Lambda)$ is defined;
(v) $Rf^!:\Dctf(Y,\Lambda)\to\Dctf(X,\Lambda)$ is defined for every $f$,
with no admissibility hypothesis ([sk-def-sf-operations](vi),
[sk-prop-sf-rf-shriek-preservation]); (vi) $\mathbb D_X:\Dctf(X,\Lambda)\to \Dctf(X,\Lambda)$ is defined and is a contravariant anti-equivalence with
$\mathbb D_X\mathbb D_X\cong\mathrm{id}$; (vii) each of (i)–(vi) is compatible
with finite reduction and scalar extension, and (i)–(vi) with the pro-étale
realization.

## Proof

(i) pullback: the pullback of a flat model is flat, and pullback preserves
bounded constructibility (lem:weil-pbc-pullback-preserves-bounded-constructible);
the Tor clause is exactness of $Lf^*$ on a bounded flat model. (ii) tensor:
additivity
of Tor amplitude and the weak-Serre property of constructible sheaves
of Tor amplitudes; internal Hom: [sk-thm-sf-hom-ctf] on the étale
site, and on the pro-étale site the internal-Hom comparison of
the internal-Hom comparison across the sites, which is an isomorphism for
every
pair of bounded constructible étale complexes and therefore needs no
site-perfectness hypothesis. (iii) direct image: on the étale site
[sk-thm-sf-direct-image-tor-amplitude]; on the pro-étale site
[sk-cor-sf-direct-image-ctf]; for proper $f$ the same through
$Rf_!=Rf_*$. (iv) compact support: the open-immersion case
([sk-lem-sf-open-ctf]: extension by zero is exact and commutes with the
constant tensor) plus the proper case, assembled along a compactification
([sk-thm-nagata-compactification], the assembly being independent of the
choice by [sk-prop-sf-comp-coherence]), the proper case using the projection
formula of [sk-rem-sf-pf-done]. (v) prop:sf-rf-shriek-preservation.
(vi) $\mathbb D_X$ is $\RHom_X(-,\omega_X)$ with $\omega_X=Ra_X^!\Lambda\in \Dctf$ by (v) for the structure morphism, so (ii) applies; the anti-equivalence
is prop:sf-biduality-general. (vii) the amplitude intervals depend only on the
input intervals, on the dimension bound and on the coefficient-free torsion
bound, hence not on the stage; the finite-level comparison isomorphisms are
[sk-prop-sf-pf-reduction] for the projection formula and the recorded
clause of prop:functor-package otherwise.

*Conditional on* clause (vii) in the case of a reduction tower for which no single
finite étale cover trivialises all stages. Everything else in the theorem
is unconditional; in particular clauses (v) and (vi) carry no admissibility
hypothesis, the exceptional adjoint being the constructible one of
[sk-def-sf-operations] (vi) (the former residue "vanishing for pro-étale
module sheaves not of étale origin" concerned only the ambient
[sk-prop-sf-existence] (b), which is false in general and not used,
[sk-rem-sf-fullcd-scope]). The one residue is the reduction
towers with no uniform trivializing cover.
Uses: `\Cref{sk-cor-sf-direct-image-ctf}`, `\Cref{sk-prop-sf-comparison}`, `\Cref{sk-prop-sf-rf-shriek-preservation}`, `\Cref{thm-sf-direct-image-tor-amplitude}`, `\Cref{thm-sf-hom-ctf}`, `prop-functor-package`
