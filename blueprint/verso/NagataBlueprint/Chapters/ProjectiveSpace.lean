import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Relative projective space and the quasi-affine base case" =>

:::group "grp:projective"
Relative projective space over an arbitrary base, its properness, the standard affine
chart, and the base case of the whole induction: a quasi-compact morphism locally of finite
type with quasi-affine source is compactifiable.
:::

# Relative projective space

Let $`\sigma` be an index type. The polynomial ring
$`\mathbb{Z}[T_i : i \in \sigma \sqcup \{\ast\}]` carries its total-degree grading.

:::definition "def:relative-projective-space" (parent := "grp:projective") (lean := "AlgebraicGeometry.ProjectiveSpaceInt, AlgebraicGeometry.RelativeProjectiveSpace, AlgebraicGeometry.RelativeProjectiveSpace.toProjectiveSpaceInt")
*Relative projective space.*
The _integral model_ is $`\Pj^{\sigma}_{\mathbb{Z}} = \Proj \mathbb{Z}[T_i]` for the
total-degree grading. For a scheme $`S`, the _relative projective space_ is the base change
$$`\Pj(\sigma; S) \;=\; \Pj^{\sigma}_{\mathbb{Z}} \times_{\Spec \mathbb{Z}} S,`
with its structure morphism $`\Pj(\sigma; S) \to S` and its comparison morphism
$`\Pj(\sigma; S) \to \Pj^{\sigma}_{\mathbb{Z}}` to the integral model.
:::

:::lemma_ "lem:projective-space-cartesian" (parent := "grp:projective") (lean := "AlgebraicGeometry.RelativeProjectiveSpace.isPullback_over")
*Relative projective space is a base change of the integral model.*
The square formed by the structure morphism $`\Pj(\sigma; S) \to S`, the comparison morphism
$`\Pj(\sigma; S) \to \Pj^{\sigma}_{\mathbb{Z}}` and the two morphisms to $`\Spec \mathbb{Z}`
is cartesian {uses "def:relative-projective-space"}[].
:::

:::proof "lem:projective-space-cartesian" (uses := "def:relative-projective-space")
The relative projective space is defined as the fibre product of the integral model and
$`S` over $`\Spec \mathbb{Z}`, and the two morphisms in question are its projections.
:::

:::theorem "thm:proj-proper" (parent := "grp:projective") (lean := "AlgebraicGeometry.RelativeProjectiveSpace.isProper_over")
*The relative projective space is proper over its base.*
For finite $`\sigma` the structure morphism $`\Pj(\sigma; S) \to S` is proper.
:::

:::proof "thm:proj-proper" (uses := "def:relative-projective-space")
The morphism $`\Pj^{\sigma}_{\mathbb{Z}} \to \Spec \mathbb{Z}` is proper, the spectrum of
the degree-zero part being terminal, and $`\Pj(\sigma; S) \to S` is one of its base changes;
properness is stable under base change.
:::

:::lemma_ "lem:dehomogenization" (parent := "grp:projective") (lean := "MvPolynomial.dehomogenizeEquiv")
*Dehomogenization at the distinguished variable.*
Let $`R` be a commutative ring and let $`R[T_\ast, T_i : i \in \sigma]` carry its
total-degree grading. The degree-zero part of the localization away from the variable
$`T_\ast` is canonically isomorphic to the polynomial ring in the remaining variables:
$$`\bigl(R[T_\ast, T_i]_{T_\ast}\bigr)_0 \;\xrightarrow{\ \sim\ }\; R[T_i : i \in \sigma], \qquad \frac{a}{T_\ast^{\,k}} \longmapsto a(1, T_i),`
for $`a` homogeneous of degree $`k`; the inverse sends $`T_i` to $`T_i / T_\ast`.
:::

:::definition "def:standard-affine-chart" (parent := "grp:projective") (lean := "AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpace")
*The standard affine chart of the relative projective space.*
The _standard chart_ $`\Aff(\sigma; S) \to \Pj(\sigma; S)` is the morphism obtained by base
change from the morphism of integral models given by $`T_i \mapsto T_i / T_\ast`
{uses "def:relative-projective-space"}[].
:::

:::lemma_ "lem:affine-chart" (parent := "grp:projective") (lean := "AlgebraicGeometry.AffineSpace.isOpenImmersion_toRelativeProjectiveSpace, AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpace_over")
*The standard chart is an open immersion over the base.*
The standard chart $`\Aff(\sigma; S) \to \Pj(\sigma; S)` {uses "def:standard-affine-chart"}[]
is an open immersion, and it is a morphism over $`S`.
:::

:::proof "lem:affine-chart" (uses := "lem:dehomogenization, def:standard-affine-chart, lem:projective-space-cartesian")
On the integral model the chart is the open immersion of the affine chart identified by
dehomogenization. The relative statement is obtained by base change to $`S`, the square
exhibiting the relative chart as a base change of the integral one being cartesian; open
immersions are stable under base change.
:::

# Quasi-affine sources

:::theorem "thm:04II" (parent := "grp:projective") (lean := "AlgebraicGeometry.exists_immersion_affineSpace_of_quasiAffine, AlgebraicGeometry.exists_immersion_affineSpace_of_quasiAffine'")
*Stacks Tag 04II: immersion of a quasi-affine scheme into a relative affine space.*
Let $`X` be a quasi-affine scheme and let $`\pi \colon X \to S` be locally of finite type.
Then there are a finite index type $`\sigma` and an immersion $`i \colon X \to \Aff(\sigma; S)`
over $`S`, that is, with $`\pi` equal to the composite of $`i` with the structure morphism of
$`\Aff(\sigma; S)`. No hypothesis on $`S` is needed.
:::

:::proof "thm:04II"
At each point of $`X` one chooses a basic affine open of $`X` contained in the preimage of an
affine open of $`S`; over such a pair the morphism is described by finitely many sections.
Quasi-affineness of $`X` and finite type of $`\pi` provide finitely many global sections of
$`\sO_X`, containing a unit on the chart, which generate the sections over the chart as an
algebra over the sections of the base. The resulting morphism to $`\Aff(\sigma; S)` is a
closed immersion into the basic open of one of the coordinates, hence an immersion.
:::

:::definition "def:affine-compactification" (parent := "grp:projective") (lean := "AlgebraicGeometry.Compactification.ofIsImmersionAffineSpace")
*The affine compactification construction.*
Let $`f \colon X \to S` be quasi-compact and let $`i \colon X \to \Aff(\sigma; S)` be an
immersion over $`S` with $`\sigma` finite. Composing $`i` with the standard chart
{uses "def:standard-affine-chart"}[] {uses "lem:affine-chart"}[] exhibits $`f` as an
immersion into a scheme proper over $`S`
{uses "thm:proj-proper"}[]; closing up its image inside $`\Pj(\sigma; S)`
{uses "def:of-immersion"}[] yields a compactification of $`f`.
:::

:::theorem "thm:quasi-affine-compactifiable" (parent := "grp:projective") (lean := "AlgebraicGeometry.HasCompactification.of_isQuasiAffine")
*A quasi-affine scheme of finite type over the base is compactifiable.*
Let $`f \colon X \to S` be quasi-compact and locally of finite type with $`X` quasi-affine.
Then $`f` admits a compactification. In particular this holds when $`X` is affine.
:::

:::proof "thm:quasi-affine-compactifiable" (uses := "thm:04II, def:affine-compactification")
Combine the immersion into a relative affine space with the closing-up construction inside
relative projective space. This is the base case of the induction over an affine cover.
:::
