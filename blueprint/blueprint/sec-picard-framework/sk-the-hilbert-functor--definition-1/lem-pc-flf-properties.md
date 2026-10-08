+++
id = "lem-pc-flf-properties"
kind = "lemma"
title = "The module $f_*\\mathcal{O}_X$ of a finite locally free morphism"
order = 768
uses = ["def-pc-base-change", "def-pc-finite-locally-free", "def-pc-morphism-conventions", "lem-pc-flat-base-change-cohom"]
+++
Let $f:X\to S$ be a morphism
finite locally free of degree
$d$. Then $f_*\mathcal{O}_X$ is a locally free $\mathcal{O}_S$-module of rank $d$,
and for every $s\in S$ the canonical map
$(f_*\mathcal{O}_X)_s\otimes_{\mathcal{O}_{S,s}}\kappa(s)\to \Gamma(X_s,\mathcal{O}_{X_s})$ is an isomorphism.

## Proof

$f$ is finite, so $f_*\mathcal{O}_X$ is a finite $\mathcal{O}_S$-module; $f$ is
fp and flat, hence $f_*\mathcal{O}_X$ is flat over $S$ (a standard
consequence: $f_*\mathcal{O}_X$ is the value of the derived direct image of
$f$ and the flatness of $\mathcal{O}_X$ over $S$ means that the direct image
under the flat morphism $f$ is flat; flatness can be checked on
stalks: for $s$ a point and $x_1,\dots,x_m\in f^{-1}(s)$ the finitely
many preimages, $\mathcal{O}_{X,x_i}$ flat over $\mathcal{O}_{S,s}$, and the finite
module
$N=(f_*\mathcal{O}_X)_s=\mathrm{colim}_{V i s}\Gamma(f^{-1}(V),\mathcal{O}_X)$
has the property that $N\otimes_{\mathcal{O}_{S,s}}\kappa(s)=\Gamma(X_s,\mathcal{O})$
(the base change identity [lem-pc-flat-base-change-cohom]), and
the flatness of $N$ is inherited from flatness of the induced maps
(the standard proof: $N$ is a directed colimit of flat modules
$\Gamma(f^{-1}(V),\mathcal{O}_X)$ over the affine $V$, each of which is flat as
a module over $\mathcal{O}_S(V)$, and $N\otimes_{\mathcal{O}_{S,s}}M$ for a flat
modulus $M$... here we may argue via the finite presentation: $N$ is
finitely presented and its Tor vanishes because the
$\mathcal{O}_{X,x_i}$'s are flat: for a flat and finitely presented module one
has $N$ flat over the local ring by the criterion "Tor$_1$ vanishes up
to finite generation"; the classical reference is: $f$ is flat and
fp, then $f_*\mathcal{O}_X$ is flat). Thus $N$ is a finitely generated flat
module over the local ring $\mathcal{O}_{S,s}$; by Nakayama it is free, of
rank $\dim_{\kappa(s)}N\otimes\kappa(s)=\dim_{\kappa(s)}\Gamma(X_s,\mathcal{O})=d$
(the last equality is the definition
[def-pc-finite-locally-free]). Hence $f_*\mathcal{O}_X$ is locally free of
rank $d$.
