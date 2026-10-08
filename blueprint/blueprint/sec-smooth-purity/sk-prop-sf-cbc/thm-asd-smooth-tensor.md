+++
id = "thm-asd-smooth-tensor"
kind = "theorem"
title = "Smooth cohomological duality without a chosen orientation"
order = 1575
uses = ["cor-amb-affine-space-adjunction", "def-asd-compactifiable", "def-sbc-smooth-morphisms", "def-weil-derived-tensor", "def-weil-pbc-derived-categories", "def-weil-pbc-inverse-image", "lem-amb-etale-adjoint-locality", "lem-amb-proper-coproducts-projection", "lemma-weil-pbc-geometric-stalk-conservative", "sbc-thm-etale-local-normal-form", "thm-amb-etale-exceptional-adjoint"]
+++
Let $f:X\to S$ be smooth, separated, compactifiable,
and of pure relative dimension $d$, with Noetherian base.
Put $\omega_f=f^\times A_S$, using the ambient right
adjoint. Then $\omega_f[-2d]$ is a locally constant
sheaf of free rank-one $A$-modules. For every complex
$K$ on $S$, the canonical tensor morphism is an
isomorphism

$$
f^*K\otimes_A^L\omega_f\xrightarrow{\sim}f^\times K.
$$

The notation refers to inverse images.

## Proof

Construct the tensor morphism by transposing

$$
Rf_!(f^*K\otimes_A^L\omega_f)
\cong K\otimes_A^LRf_!\omega_f
\longrightarrow K\otimes_A^LA_S=K
$$

under [thm-amb-etale-exceptional-adjoint].
The displayed projection formula follows from
[lem-amb-proper-coproducts-projection] on a compactification:
extension by zero commutes with tensoring a pulled-back
complex, as its stalk is either that complex or zero.

By [sbc-thm-etale-local-normal-form], every point of
$X$ has an etale neighbourhood $u:U\to X$ such
that $fu=p_de$, where $e:U\to\mathbf A^d_S$
is etale (one may restrict the base to an open neighbourhood).
The adjunctions in
[lem-amb-etale-adjoint-locality], [cor-amb-affine-space-adjunction]
identify

$$
u^*f^\times K\cong e^*p_d^*K(d)[2d],\qquad
u^*\omega_f\cong A_U(d)[2d].
$$

By its definition as the transpose of the projection formula
and counit, the tensor map restricts under these identifications
to the canonical reassociation
$(fu)^*K\otimes_A^LA_U(d)[2d]\cong(fu)^*K(d)[2d]$.
To check this assertion, transpose on $U$: both maps
become the projection formula followed by the composite of
the etale counit with the $d$ affine-line counits. The
uniqueness in the adjunction bijection therefore identifies
them. In particular it is an isomorphism locally on $X$,
hence globally by
[lemma-weil-pbc-geometric-stalk-conservative].

The same local calculation shows that all cohomology sheaves
of $\omega_f$ except $\mathcal H^{-2d}$ vanish,
and that $\mathcal H^{-2d}(\omega_f)$ is etale locally
free of rank one. The canonical truncation isomorphism
$\omega_f\cong\mathcal H^{-2d}(\omega_f)[2d]$
gives the stated conclusion. No complexes or morphisms were
glued in a derived category: the adjoint and tensor morphism
were constructed globally, and geometric stalks only tested
their properties.
