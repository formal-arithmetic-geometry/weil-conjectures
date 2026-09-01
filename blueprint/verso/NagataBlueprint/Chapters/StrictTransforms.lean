import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Strict transforms" =>

:::group "grp:strict-transform"
The strict transform of a morphism along another morphism, preserving an open of the base,
and its identification with the blow-up of the pulled-back centre.
:::

:::definition "def:strict-transform" (parent := "grp:strict-transform") (lean := "AlgebraicGeometry.strictTransformOpen, AlgebraicGeometry.strictTransform, AlgebraicGeometry.strictTransformι, AlgebraicGeometry.strictTransformMap, AlgebraicGeometry.strictTransformToSource, AlgebraicGeometry.Scheme.IdealSheafData.strictTransform, AlgebraicGeometry.Scheme.IdealSheafData.strictTransformι")
Let $`f \colon Y \to X` and $`\pi \colon X' \to X` be morphisms and let $`U \subseteq X` be an
open. Inside the fibre product $`Y \times_X X'` consider the open locus $`L` lying over $`U`.
The _strict transform_ $`\St{f}{\pi}{U}` of $`f` along $`\pi` preserving $`U` is the
scheme-theoretic image of $`L` in $`Y \times_X X'`. It is a closed subscheme of
$`Y \times_X X'`; we write $`\St{f}{\pi}{U} \to X'` and $`\St{f}{\pi}{U} \to Y` for the two
projections. For $`\pi = \pi_\sI` the blow-up of an ideal sheaf $`\sI` and $`U = V(\sI)^{c}`
this is the classical strict transform {uses "def:blowup"}[].
:::

:::proposition "prop:strict-transform-basic" (parent := "grp:strict-transform") (lean := "AlgebraicGeometry.range_strictTransformMap_subset_preimage_range, AlgebraicGeometry.mem_range_strictTransformMap_of_mem_of_mem_range, AlgebraicGeometry.disjoint_range_strictTransformMap_of_disjoint")
Separatedness, quasi-compactness, being locally of finite type and being a closed immersion
pass from $`f` to the projection $`\St{f}{\pi}{U} \to X'`. The strict transform contains the
whole open locus over $`U`. Its underlying set is squeezed between the inverse image of the
$`U`-part of the image of $`f` and the full inverse image of the image of $`f`; consequently,
disjointness of two closed subschemes of $`X` persists for their strict transforms
{uses "def:strict-transform"}[].
:::

:::lemma_ "lem:strict-transform-over-U" (parent := "grp:strict-transform") (lean := "AlgebraicGeometry.isPullback_strictTransformOpen, AlgebraicGeometry.isPullback_strictTransform_over, AlgebraicGeometry.strictTransformOpenIso")
If $`\pi` is an isomorphism over $`U`, then the open locus $`L` is canonically
$`Y \times_X U`, hence identified with $`f^{-1}U`, and the part of the strict transform lying
over $`U` is the ordinary base change $`Y \times_X U`.
:::

:::lemma_ "lem:kernel-criterion" (parent := "grp:strict-transform") (lean := "AlgebraicGeometry.ker_strictTransformMap, AlgebraicGeometry.ker_eq_ker_strictTransformOpen_ι")
Assume the inclusion of the open locus $`L` is quasi-compact. Then the strict transform and
its open locus have the same scheme-theoretic image in $`X'`. Moreover, a morphism to
$`Y \times_X X'` whose first component is an isomorphism over $`f^{-1}U` on a schematically
dense preimage of $`f^{-1}U` cuts out the same closed subscheme of $`Y \times_X X'` as the
open locus over $`U`.
:::

:::theorem "thm:080E" (parent := "grp:strict-transform") (lean := "AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform")
Let $`f \colon Y \to X` be a morphism and $`\sI` a quasi-coherent ideal sheaf on $`X`. Then
there is an isomorphism
$$`\Bl_{\sI \cdot \sO_Y}(Y) \;\xrightarrow{\ \sim\ }\; \St{f}{\pi_\sI}{V(\sI)^{c}}`
compatible with the projections to $`Y` and with the structure morphisms to $`X`. No
finiteness or quasi-compactness hypotheses are required.
:::

:::proof "thm:080E" (uses := "thm:0806, lem:kernel-criterion, thm:admissible-density, def:strict-transform")
Consider the comparison morphism
$`\psi \colon \Bl_{\sI \cdot \sO_Y}(Y) \to Y \times_X \Bl_\sI(X)` whose components are the
structure morphism of $`\Bl_{\sI \cdot \sO_Y}(Y)` and the lift supplied by the universal
property. It is a closed immersion: the assertion is local, and over a chart of
$`\Bl_\sI(X)` at a degree-one element $`x` it is the spectrum of the canonical ring map
$`B \otimes_A A[\sI/x] \to B[\sI B/\varphi(x)]`, which is surjective because a fraction
$`y/\varphi(a)^n` with $`y \in \sI^n B` decomposes as a $`B`-linear combination of fractions
coming from the chart ring of $`\Bl_\sI(X)`. Furthermore $`\psi` has the same kernel as the
inclusion of the open locus: the open locus factors through $`\psi` as the preimage of
$`V(\sI \cdot \sO_Y)^{c}` in $`\Bl_{\sI \cdot \sO_Y}(Y)`, which is schematically dense there
because the exceptional ideal is invertible; so precomposing with it does not change the
kernel, and the kernel criterion applies. Since the strict transform is by definition the
closed subscheme cut out by the kernel of the open locus, the two closed subschemes of
$`Y \times_X \Bl_\sI(X)` coincide.
:::

:::corollary "cor:080E-closed" (parent := "grp:strict-transform") (lean := "AlgebraicGeometry.Scheme.IdealSheafData.exists_isClosedImmersion_blowup_comap")
Let $`j \colon Z \to X` be a closed immersion and $`\sI` a quasi-coherent ideal sheaf on
$`X`. Then $`\Bl_{\sI \cdot \sO_Z}(Z)` is a closed subscheme of $`\Bl_\sI(X)`, compatibly
with the two blow-up morphisms.
:::

:::proof "cor:080E-closed" (uses := "thm:080E, prop:strict-transform-basic")
The strict transform of a closed immersion is a closed subscheme of the fibre product, which
is itself closed in $`\Bl_\sI(X)`.
:::
