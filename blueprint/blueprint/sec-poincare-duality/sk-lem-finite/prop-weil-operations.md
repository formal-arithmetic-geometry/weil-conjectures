+++
id = "prop-weil-operations"
kind = "theorem"
title = "Six operations on Weil complexes"
order = 2435
tags = ["latex:proposition"]
uses = ["def-compact-support-direct-image-detailed", "def-exchange-projection", "def-weil-derived-cohomology-sheaves", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-frobenius-detailed", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex", "fix-cor-verdier-exchange", "lem-fix-weil-operations", "prop-constructible-truncations", "prop-pur-weil-equivariance-compatibilities", "thm-pod-equivariance-of-the-twisted-pairing", "thm-pur-weil-equivariance-of-purity-and-trace"]
+++
Fix the finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, and fix a prime $\ell\neq p$; write
$\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of $\Ql$, and
let $E/\Ql$ be finite and contained in $\Qlb$, and let
$\Lambda\in\{E,\Qlb\}$; use the
Weil-complex category, the
bounded constructible
coefficient categories and their
finite-Tor subcategories, the
separated finite-type
morphism conditions, and the
exceptional-adjoint
admissibility condition in its constructible form (the exceptional inverse
image of [def-weil-exceptional-inverse-image], defined for every separated
finite-type morphism; the ambient clause (1) of
[def-weil-exceptional-adjoint-admissibility] is not assumed, as it fails in
general). Use the
derived pullback, tensor, and
internal-Hom operations, the
derived direct-image and
compact-support direct image, the
exceptional inverse image, the
exchange/projection transformations, and
the standard truncation functors $\tau^{\leq m},\tau^{\geq m}$.
Let $X_0,Y_0$ be
finite-type $k_0$-schemes
and let $f_0:X_0\to Y_0$ be a
separated finite-type
$k_0$-morphism, and let
$X=X_0\times_{k_0}k$, $Y=Y_0\times_{k_0}k$, and let $f:X\to Y$ be
the geometric fiber of
$f_0$. For
$K\in D^b_{c,\mathrm W}(X,\Lambda)$, and, whenever a tensor or internal
Hom is used on a scheme $W\in\{X,Y\}$, for
$M\in D^b_{ctf}(W,\Lambda)$ and $N\in D^b_c(W,\Lambda)$, the exact functors

$$
Lf^*,\quad Rf_*,\quad Rf_!,\quad -\otimes^L-,\quad R\mathcal Hom
$$

lift to Weil complexes on every one of these domains on which their
underlying bounded constructibility has been proved. In particular, the
elementary internal-Hom preservation theorem applies when its first
argument is site-perfect. Equivariance itself supplies no preservation
theorem for a larger domain. Put

$$
g_X=\operatorname{id}_{X_0}\times\operatorname{Spec}(\operatorname{Frob}_q),
\qquad
g_Y=\operatorname{id}_{Y_0}\times\operatorname{Spec}(\operatorname{Frob}_q),
$$

using the geometric-Frobenius convention.
The constructible exceptional inverse image $Rf^!$ of
[def-weil-exceptional-inverse-image] — available for every separated
finite-type $f$, so that no admissibility hypothesis is needed — also has an
equivariant lift, with its Weil
isomorphism induced by the corresponding exchange and adjunction maps. For
example, the Weil isomorphism on $Rf_*K$ is

$$
Lg_Y^*Rf_*\operatorname{For}(K)
\xrightarrow{\operatorname{Ex}_*}
Rf_*Lg_X^*\operatorname{For}(K)
\xrightarrow{Rf_*(\theta_K)}Rf_*\operatorname{For}(K),
$$

and the compact-support construction uses $\operatorname{Ex}_!$.
For every $W\in\{X,Y\}$ and $m\in\mathbf Z$, let
$\tau^{\leq m},\tau^{\geq m}:D^b_c(W,\Lambda)\to D^b_c(W,\Lambda)$
be the truncation functors, characterized by vanishing of the
cohomology sheaves
$\mathcal H^r(\tau^{\leq m}K)=0$ for $r>m$ and
$\mathcal H^r(\tau^{\geq m}K)=0$ for $r<m$, together with their
standard truncation triangles. The
forgetful functor commutes with these lifted operations. Composition,
base change, projection, purity, and duality isomorphisms are morphisms of
Weil complexes and induce Frobenius-equivariant maps on
cohomology.

## Proof

The equivariant lifts of the operations, evaluations, adjunction maps,
exchanges and projection maps are [lem-fix-weil-operations].
Pullback by the Frobenius automorphism is exact, so it commutes with
the truncations of [prop-constructible-truncations].
The geometric orientation and trace are equivariant by
[thm-pur-weil-equivariance-of-purity-and-trace] and
[prop-pur-weil-equivariance-compatibilities].
The formal duality exchange of [fix-cor-verdier-exchange] is made
from the same evaluation and adjunction maps, hence is equivariant;
its smooth pairing form is
[thm-pod-equivariance-of-the-twisted-pairing].
This proves the assertion on the stated domains without appealing to
the later verification export.
