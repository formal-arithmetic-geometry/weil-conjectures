+++
id = "thm-nagata-blowup-universal-property"
kind = "theorem"
title = "[stacks-project]"
order = 110
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_blowup", "AlgebraicGeometry.Scheme.IdealSheafData.hom_ext_of_isInvertible_comap"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-invertible-ideal", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-relative-proj", "def-nagata-sheaf-rees-algebra", "lemma-nagata-chart-extended-ideal-principal", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-invertible-ideal-tensor-power", "lemma-nagata-localization-ideal-pow", "lemma-nagata-proj-chart-ring-cocycle", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "lemma-nagata-relative-proj-base-change-arbitrary", "lemma-nagata-relative-proj-invertible-tensor-powers", "prop-nagata-affine-blowup-chart", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded"]
+++
Under the data of [thm-nagata-blowup-universal-property], the constructed
map $\widetilde f$ is the unique $X$-morphism from $Y$ to
$\operatorname{Bl}_{\mathcal I}(X)$ inducing the chosen invertible
quotient. Thus the blow-up is final among such $X$-schemes.

## Proof

Existence is [thm-nagata-blowup-universal-property], and uniqueness
among $X$-morphisms inducing the specified quotient is
[thm-nagata-blowup-universal-property]. Together these are exactly the
asserted final-object property.

## Graded map induced by an invertible quotient

Let $f\colon Y\to X$, let $\mathcal I\subseteq\mathcal O_X$ be a
quasi-coherent ideal, and let
$\mathcal L\hookrightarrow\mathcal O_Y$ be an invertible ideal together with
a surjection $q\colon f^*\mathcal I\twoheadrightarrow\mathcal L$ such that
the composite $\mathcal L\hookrightarrow\mathcal O_Y$ after $q$ is the
canonical map whose image is the extended ideal
$\mathcal I\mathcal O_Y$ of
[def-nagata-extended-ideal]. Define $\alpha_f$ degreewise by the
tensor powers of this quotient:

$$
\alpha_f\colon
f^*\Bigl(\bigoplus_{n\geq0}\mathcal I^n\Bigr)
\longrightarrow\bigoplus_{n\geq0}\mathcal L^{\otimes n}.
$$

## The quotient construction is a graded algebra map

The degreewise map $\alpha_f$ respects the unit and multiplication and is a
graded algebra morphism.

*Proof.*
In degree $n$, tensor $q$ $n$ times. Let
$\mu_{\mathcal I}\colon(f^*\mathcal I)^{\otimes n}\to f^*(\mathcal I^n)$ be multiplication. The composite of $q^{\otimes n}$
with
multiplication isomorphism
$\mathcal L^{\otimes n}\cong\mathcal L^n$ from
[lemma-nagata-invertible-ideal-tensor-power] and the injection
$\mathcal L^n\hookrightarrow\mathcal O_Y$ is ordinary $n$-fold
multiplication. It therefore kills $\ker(\mu_{\mathcal I})$; injectivity
of $\mathcal L^n\hookrightarrow\mathcal O_Y$ shows that $q^{\otimes n}$
itself kills this kernel. Hence it factors uniquely through
$f^*(\mathcal I^n)$. These factorizations commute with multiplication by
associativity and with the degree-zero unit, giving the graded algebra map.
Associativity of tensor products and the multiplication maps for ideal
powers show that these degreewise maps preserve the unit and multiplication.

## Universal lift construction

Under the data of
[thm-nagata-blowup-universal-property], use the inverse of the canonical isomorphism in
[lemma-nagata-relative-proj-invertible-tensor-powers], apply the
contravariant relative-Proj map induced by $\alpha_f$. Then use the
arbitrary base-change comparison in
[lemma-nagata-relative-proj-base-change-arbitrary] to identify the
resulting target with $Y\times_X\operatorname{Bl}_{\mathcal I}(X)$. Here
$\operatorname{Proj}_X(\mathcal R_X(\mathcal I))$ is identified with
[def-nagata-global-blowup]: both are obtained by gluing the same affine
Rees-algebra Proj schemes, and the comparison respects the restriction
cocycles. Compose
the resulting map with the second projection
$Y\times_X\operatorname{Bl}_{\mathcal I}(X)\to \operatorname{Bl}_{\mathcal I}(X)$, and
define

$$
\widetilde f\colon Y\longrightarrow\operatorname{Bl}_{\mathcal I}(X)
$$

to be the resulting composite. The affine maps and their gluing data are
part of the relative-Proj interface; no identification of $Y$ with a Proj
is left implicit.

## Uniqueness of the universal lift

Under the data of [thm-nagata-blowup-universal-property], every $X$-morphism
$h\colon Y\to\operatorname{Bl}_{\mathcal I}(X)$ inducing the chosen
invertible quotient equals the constructed map $\widetilde f$.

*Proof.*
On each affine open of $X$, let $D_+(f)$ range over the standard opens
indexed by the degree-one elements $f\in\mathcal I$; these opens cover the
blow-up Proj. The inverse image of each chart
under $h$ is determined by the degree-zero map obtained from the given
quotient $f^*\mathcal I\twoheadrightarrow\mathcal L$: on a representative
$x/f_i^n$ it is the coefficient of the corresponding quotient fraction in
$\mathcal O_Y$. The constructed lift uses exactly the same degreewise maps,
by definition of $\alpha_f$ and the tensor-power identification, so $h$ and
$\widetilde f$ agree on each inverse-image chart. These equalities are
compatible on chart overlaps because both maps send a localized fraction to
its further localization; the localization cocycle gives literal equality.
The standard charts cover the target, hence their inverse images cover $Y$,
and equality of morphisms on this cover implies $h=\widetilde f$.

## The constructed lift lies over $X$

Under the data of [thm-nagata-blowup-universal-property], the constructed
map $\widetilde f$ is an $X$-morphism: its composite with
$b_{X,\mathcal I}$ is $f$.

*Proof.*
On each standard chart, the degree-zero component of
[thm-nagata-blowup-universal-property] is the canonical map to
$\mathcal O_Y$, hence the composite with the blow-up structure map is $f$.
The chart maps agree on overlaps by functoriality of localization, and the
glued equality is therefore the specified equality over $X$.
