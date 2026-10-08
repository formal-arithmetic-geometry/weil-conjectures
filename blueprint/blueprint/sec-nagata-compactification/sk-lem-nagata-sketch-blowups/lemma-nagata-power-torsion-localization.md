+++
id = "lemma-nagata-power-torsion-localization"
kind = "lemma"
title = "Localization of power torsion"
order = 141
lean = ["Submodule.localized'_powTorsion"]
uses = ["def-nagata-power-torsion", "lemma-nagata-power-torsion-kernel-localization", "lemma-nagata-power-torsion-submodule"]
+++
Let $s\in R$. Under localization at $s$, the image of
$\Gamma_{(a)}(M)$ is
$\Gamma_{(a/1)}(M_s)$.

## Proof

Localize the kernel description in
[lemma-nagata-power-torsion-kernel-localization]. Localization is flat,
so it preserves this kernel. The iterated localization $(M_s)_{a/1}$ is
canonically $M_{sa}$.

## Detailed form

Let $R$ be a ring, $N$ an $R$-module, and $a,s\in R$. Under the canonical
localization map one has

$$
\operatorname{im}\!\left(\Gamma_{(a)}(N)\to N_s\right)
=\Gamma_{(a/1)}(N_s),
$$

and consequently a canonical isomorphism

$$
(N/\Gamma_{(a)}(N))_s
\;\xrightarrow{\sim}\;
N_s/\Gamma_{(a/1)}(N_s).
$$

These isomorphisms commute with successive localization at $s$ and $t$.

## Proof

The power-torsion submodule is the kernel of the map
$N\to N_a$ by
[lemma-nagata-power-torsion-kernel-localization]. Localization at
$s$ is flat, hence carries this kernel to the kernel of
$N_s\to (N_s)_{a/1}$. The latter kernel is
$\Gamma_{(a/1)}(N_s)$, proving the first equality. The universal property
of the quotient then gives the displayed map; it is an isomorphism because
localization is exact and the localized kernel is exactly the target
torsion submodule. For $s,t$, both composites are induced by the same map
$N\to N_{st}$ and therefore agree by quotient and localization
extensionality.
