+++
id = "thm-sp-truncation-e2"
kind = "theorem"
title = "The truncation hypercohomology spectral sequence"
order = 1212
uses = ["def-sp-convergence", "def-sp-exact-couple", "def-sp-image-filtration", "def-sp-injective-resolutions", "def-sp-truncation-couple", "lem-sp-shift-identification", "lem-sp-truncation-couple-exact", "thm-sp-half-plane-convergence"]
+++
Let $K$ be as in [def-sp-truncation-couple]. The spectral sequence of the
truncation couple [def-sp-truncation-couple] has

$$
 E_2^{p,q}=R^pv\bigl(\mathcal H^q(K)\bigr)
 \Longrightarrow\mathcal H^{p+q}(RvK),
$$

the abutment $\mathcal H^n(RvK)$ carrying the image filtration
[def-sp-image-filtration] of the maps $\mathcal H^n(Rv\,\tau_{\leq q}K)\to
\mathcal H^n(RvK)$; in each degree $n$ only $a\leq q\leq n$ occurs, so the
couple is regular and complete and the convergence is unconditional
([def-sp-convergence]).

## Proof

The exact couple of [def-sp-truncation-couple] is an exact couple by
[lem-sp-truncation-couple-exact], and it is the couple of a t-structure
("heart") filtration, so by the spectral sequence of
[def-sp-exact-couple] the $E_2$-page is $E_2^{p,q}=R^pv(\mathcal H^qK)$, the
identification of the shifted cohomology being the shift rule
[lem-sp-shift-identification]. The abutment is $\mathcal H^{p+q}(RvK)$ with
the image filtration of [def-sp-image-filtration]. The $D$-terms vanish for
$q<a$ because $\tau_{\leq q}K=0$. The functor $Rv$ is left t-exact: an object
with no cohomology below $b$ has an injective resolution in the sense of
[def-sp-injective-resolutions] starting in degree $b$, and applying the left
exact functor does not introduce lower terms. Applied to $\tau_{>n}K$, this
shows $D^{0,n}=H^n(Rv\tau_{\leq n}K)=H^n(RvK)$. The hypotheses and the
abutment identification of [thm-sp-half-plane-convergence] therefore hold. In
particular the entries stabilize for $r>\max(q-a+1,p)$, and the stated finite
filtration is the one constructed there.
