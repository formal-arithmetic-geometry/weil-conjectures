+++
id = "lem-per-dual-lisse-tensor"
kind = "lemma"
title = "Dual of a lisse tensor"
order = 2740
uses = ["def-trf-dualizing-complex", "def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions", "def-wf-tate-twist", "fin2-lem-lisse-trivialized-finite-etale", "fix-lem-tensor-adjunction"]
+++
Let $X$ be
smooth of pure dimension
$d$, let $K\in D^b_c(X,\overline{\mathbf Q}_\ell)$ and let
$\mathcal L$ be lisse
of finite rank on $X$. Then the Verdier dual satisfies

$$
D_X\bigl(K\otimes^L\mathcal L\bigr)\;\cong\;
D_XK\otimes^L\mathcal L^\vee,
$$

the linear dual $\mathcal L^\vee$ of $\mathcal L$.

## Proof

By [def-trf-dualizing-complex] and the derived tensor–Hom adjunction
of [fix-lem-tensor-adjunction] of the framework chapter,

$$
D_X\bigl(K\otimes^L\mathcal L\bigr)
=R\mathcal Hom_{\overline{\mathbf Q}_\ell}\bigl(K\otimes^L\mathcal L,
\omega_X\bigr)
\cong R\mathcal Hom_{\overline{\mathbf Q}_\ell}\bigl(K,
R\mathcal Hom_{\overline{\mathbf Q}_\ell}(\mathcal L,\omega_X)\bigr).
$$

For the lisse sheaf $\mathcal L$, étale-locally constant of finite
rank by [fin2-lem-lisse-trivialized-finite-etale] of the smooth-base-change chapter, the internal Hom into $\omega_X$ is the tensor with the linear
dual: on an étale neighborhood where
$\mathcal L\cong\overline{\mathbf Q}_\ell^{\,r}$ one has
$R\mathcal Hom(\mathcal L,\omega_X)\cong\omega_X^{\,r} \cong\mathcal L^\vee\otimes\omega_X$, and the identification is
canonical and local, hence assembled into the global isomorphism

$$
R\mathcal Hom_{\overline{\mathbf Q}_\ell}(\mathcal L,\omega_X)
\cong\mathcal L^\vee\otimes\omega_X.
$$

Inserting this, and using once more that the internal Hom with a
lisse sheaf commutes with the lisse tensor (the same étale-local
argument applied to the second variable, with the identification
$R\mathcal Hom(K,\mathcal L^\vee\otimes\omega_X)\cong R\mathcal Hom(K,\omega_X)\otimes^L\mathcal L^\vee$),

$$
D_X\bigl(K\otimes^L\mathcal L\bigr)
\cong R\mathcal Hom\bigl(K,\omega_X\bigr)\otimes^L\mathcal L^\vee
=D_XK\otimes^L\mathcal L^\vee,
$$

which is the asserted isomorphism.
