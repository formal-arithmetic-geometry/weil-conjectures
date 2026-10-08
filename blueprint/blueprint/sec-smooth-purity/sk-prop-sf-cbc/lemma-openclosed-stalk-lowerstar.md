+++
id = "lemma-openclosed-stalk-lowerstar"
kind = "lemma"
title = "Stalks of $i_*$ on $Z$"
order = 1521
lean = ["AlgebraicGeometry.Etale.lowerStarCompSheafFiberIso", "AlgebraicGeometry.Scheme.initial_pointSmallEtaleElementsBaseChange"]
uses = ["def-kun-separably-closed", "lemma-openclosed-etale-lifts-locally"]
+++
Let $i\colon Z\to X$ be a closed immersion, let $\bar z$ be a geometric point
of $Z$ and write $\bar x:=i\circ\bar z$ for the corresponding geometric point
of $X$. Then the base-change functor

$$
\Phi\colon\mathrm N(\bar x)\to\mathrm N(\bar z),
\qquad(V,\bar v)\mapsto(V\times_XZ,\bar z),
$$

on the categories $\mathrm N(\bar x)$, $\mathrm N(\bar z)$ of pointed étale
neighbourhoods is initial. Consequently, for every
$\mathcal H\in\shv{\et Z}$,

$$
(i_*\mathcal H)_{\bar x}\cong\mathcal H_{\bar z},
$$

naturally in $\mathcal H$.

## Proof

Write $\mathrm N(\bar x)$ for the cofiltered category of étale
neighbourhoods $(V,\bar v)$ of $\bar x$ in $\et X$ and $\mathrm N(\bar z)$
for that of $\bar z$ in $\et Z$. By the formula for $i_*$,

$$
(i_*\mathcal H)_{\bar x}
=\colim_{(V,\bar v)\in\mathrm N(\bar x)^{\mathrm{op}}}(i_*\mathcal H)(V)
=\colim_{(V,\bar v)\in\mathrm N(\bar x)^{\mathrm{op}}}
\mathcal H(V\times_XZ),
$$

so the displayed isomorphism is the comparison of colimits induced by
$\Phi$, and it suffices to prove that $\Phi$ is initial.

No connectedness argument is written by hand. Both $\mathrm N(\bar x)$ and
$\mathrm N(\bar z)$ are cofiltered, being categories of étale
neighbourhoods of a point, and for a functor between cofiltered categories
initiality follows from the two conditions:

1. every object $d$ of $\mathrm N(\bar z)$ is dominated: there is an object
$c$ of $\mathrm N(\bar x)$ and a morphism $\Phi(c)\to d$;
1. any two morphisms $\sigma,\sigma'\colon\Phi(c)\to d$ are equalised
after precomposing with $\Phi(\tau)$ for some
$\tau\colon c'\to c$ in $\mathrm N(\bar x)$.

Only these two are proved.

*Domination.* This is [lemma-openclosed-etale-lifts-locally] in its
pointed form, applied to $W\to Z$ and $\bar w$ for $d=(W,\bar w)$: it produces
$V$ étale over $X$ and a $Z$-morphism $V\times_XZ\to W$ through which
$\bar w$ factors. The factorisation supplies the lift $\bar v$ of $\bar x$ to
$V$, so $c=(V,\bar v)$ is an object of $\mathrm N(\bar x)$ and the morphism is
one of pointed étale neighbourhoods $\Phi(c)\to d$.

*Equalisation.* Let $\sigma,\sigma'\colon\Phi(V,\bar v)=V\times_XZ\to W$
be two morphisms of pointed étale neighbourhoods; both send the marked point
$p$ of $V\times_XZ$ to the marked point of $W$, and both are morphisms over
$Z$. Now $W\to Z$ is étale, hence unramified, so its diagonal is an open
immersion and the locus in $V\times_XZ$ where two $Z$-morphisms into $W$ agree
is open; it contains $p$ because $\sigma$ and $\sigma'$ agree there. Finally
$V\times_XZ\to V$ is a closed immersion, hence inducing on the underlying
spaces, so that agreement locus is the trace of an open subscheme
$V_0\subseteq V$, which contains the marked point of $V$. Then
$c'=(V_0,\bar v)$ is again an object of $\mathrm N(\bar x)$ and the inclusion
$\tau\colon c'\to c$ has $\Phi(\tau)$ landing in the agreement locus, so
$\Phi(\tau)\circ\sigma=\Phi(\tau)\circ\sigma'$.

The second condition is precisely where the shrinking that
[rmk-openclosed-no-dense-subsite] says is unavailable to the
dense-subsite argument is harmless: in a colimit over neighbourhoods one is
allowed to pass to $V_0$. Note also that the fibre product $V_1\times_XV_2$ of
two neighbourhoods, which a hand-written connectedness argument would have to
construct, is exactly what the cofilteredness of $\mathrm N(\bar x)$ supplies.
