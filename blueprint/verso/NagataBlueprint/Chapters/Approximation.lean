import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Removing the Noetherian hypothesis" =>

:::group "grp:approximation"
Absolute Noetherian approximation, descent of separated morphisms of finite presentation to a
finite stage, the finite-presentation envelope of a morphism of finite type, and the Nagata
theorem for morphisms of finite presentation over a quasi-compact quasi-separated base.
:::

# Absolute Noetherian approximation

:::definition "def:noetherian-approximation" (parent := "grp:approximation") (lean := "AlgebraicGeometry.Scheme.NoetherianApproximation, AlgebraicGeometry.Scheme.NoetherianApproximation.ofIso, AlgebraicGeometry.Scheme.NoetherianApproximation.over, AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine")
A _Noetherian approximation_ of a scheme $`S` consists of a small cofiltered index category
$`I`, a diagram $`D \colon I \to \mathrm{Sch}` whose values are of finite type over
$`\Spec \mathbb{Z}` (that is, quasi-compact and locally of finite type over
$`\Spec \mathbb{Z}`) and whose transition morphisms are affine, together with a cone from
$`S` exhibiting $`S` as the limit $`\varprojlim_i D_i`. Every stage of such a system is a
Noetherian scheme.
:::

:::theorem "thm:01ZA" (parent := "grp:approximation") (lean := "AlgebraicGeometry.Scheme.nonempty_noetherianApproximation, AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData, AlgebraicGeometry.Scheme.NoetherianApproximation.ExtensionData.approximation")
Every scheme which is quasi-compact and quasi-separated admits a Noetherian approximation.
:::

:::proof "thm:01ZA" (uses := "def:noetherian-approximation")
For an affine scheme $`S` the spectra of the finitely generated $`\mathbb{Z}`-subalgebras of
the global sections form a Noetherian approximation: the global sections are the filtered
colimit of those subalgebras, and $`\Spec`, being a right adjoint, turns that colimit into a
limit. The general case is an induction over a finite affine cover, each step extending an
approximation of a quasi-compact open $`U` across one more affine open $`V`. The stages of a
step are indexed by triples consisting of a stage of the approximation of $`U`, lifts of
finitely many sections of $`V` whose basic opens cover $`U \cap V`, and a finitely generated
$`\mathbb{Z}`-subalgebra of a suitable fibre product of section rings large enough that the
relevant overlap becomes a quasi-affine open of its spectrum. These stages form a cofiltered
category and the functor remembering the underlying index is initial, so limits over the
system of overlaps may be computed over the category of stages. The limit property is
verified chart by chart, using that a cone over a cofiltered diagram of schemes is a limit
cone as soon as its restrictions to the members of an open cover of one stage, and to their
pairwise intersections, are limit cones.
:::

# Descending finite presentation and separatedness

:::theorem "thm:01ZM" (parent := "grp:approximation") (lean := "AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation, AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine")
Let $`(D_i)` be a cofiltered inverse system of quasi-compact quasi-separated schemes with
affine transition morphisms, and let $`X` be of finite presentation over
$`\varprojlim_i D_i`. Then $`X` is the base change of a scheme of finite presentation over
one of the $`D_i`.
:::

:::proof "thm:01ZM"
The affine case is treated first: an affine $`X` lying over an affine open of a stage
descends after base changing the whole system to that open. The general case is an induction
over a finite cover of $`X` by such affine opens; at each step two finite-stage models are
glued along a descent of their intersection. The gluing data comes from the facts that a
quasi-compact open descends to a stage and that two finite-stage models of the same scheme
become isomorphic at a later stage; the gluing itself is a pushout of two open immersions,
and the glued morphism is again cartesian.
:::

:::theorem "thm:086Q" (parent := "grp:approximation") (lean := "AlgebraicGeometry.Scheme.exists_isSeparated_of_isLimit, AlgebraicGeometry.Scheme.exists_isSeparated_app_of_isLimit, AlgebraicGeometry.IsSeparatingPair, AlgebraicGeometry.Scheme.isSeparated_of_isSeparatingPair")
Let $`(D_i)` be a cofiltered inverse system of quasi-compact quasi-separated schemes with
affine transition morphisms. If $`\varprojlim_i D_i` is separated, then $`D_i` is separated
for every $`i` past some stage. If all $`D_i` lie over a fixed base $`S` and
$`\varprojlim_i D_i \to S` is separated, then $`D_i \to S` is separated for every $`i` past
some stage.
:::

:::proof "thm:086Q"
Both go through an affine criterion: a scheme is separated as soon as the affine opens of a
finite affine cover pairwise have affine intersections and the sections over such an
intersection are generated as a ring by the sections of the two members. Affineness of the
intersections descends to a stage. The generation statement descends because, on the one
hand, the sections over the intersection at a stage are finitely generated over the sections
of one member, and on the other hand the elements of the limit which come from a stage inside
the subring generated by the two members form a subring, which by hypothesis is everything.
:::

:::theorem "thm:01ZQ" (parent := "grp:approximation") (lean := "AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated, AlgebraicGeometry.Scheme.exists_isClosedImmersion_pullback_snd, AlgebraicGeometry.Scheme.exists_isClosedImmersion_overPullbackMap, AlgebraicGeometry.Scheme.exists_isSeparated_pullback_snd")
Let $`(D_i)` be a cofiltered inverse system of quasi-compact quasi-separated schemes with
affine transition morphisms and let $`g \colon X \to \varprojlim_i D_i` be separated,
quasi-compact and locally of finite presentation. Then there are an index $`i`, a scheme
$`Y` and a morphism $`p \colon Y \to D_i` which is separated, quasi-compact and locally of
finite presentation, together with a cartesian square exhibiting $`g` as the base change of
$`p` along $`\varprojlim_j D_j \to D_i`.
:::

:::proof "thm:01ZQ" (uses := "thm:01ZM, thm:086Q")
Descend $`X` and then apply the descent of separatedness to the diagonal of the descended
model: a morphism of finite presentation whose base change to the limit is a closed immersion
is a closed immersion at a finite stage.
:::

# From finite presentation to finite type

:::theorem "thm:09ZQ" (parent := "grp:approximation") (lean := "AlgebraicGeometry.Scheme.Hom.FinitePresentationApproximation, AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation, AlgebraicGeometry.Scheme.Hom.exists_isImmersion_locallyOfFinitePresentation, AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_locallyOfFinitePresentation")
Let $`S` be quasi-compact quasi-separated and let $`f \colon X \to S` be locally of finite
type with $`X` quasi-compact quasi-separated. Then $`X` is a cofiltered limit of schemes of
finite presentation over $`S` whose transition morphisms, and whose morphisms from $`X`, are
closed immersions.
:::

:::proof "thm:09ZQ" (uses := "thm:01ZA, thm:01ZM")
Shrink an immersion of $`X` into a finite-presentation model to a closed immersion
$`X \to Y` into a quasi-compact open of that model, then write $`X` as the limit of the
closed subschemes of $`Y` cut out by the finite-type subsheaves of the kernel of
$`X \to Y`.
:::

:::theorem "thm:01ZJ" (parent := "grp:approximation") (lean := "AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation")
Let $`X` and $`S` be quasi-compact quasi-separated and let $`f \colon X \to S` be separated,
quasi-compact and locally of finite type. Then $`f` factors as
$$`X \xrightarrow{\ i\ } X' \xrightarrow{\ f'\ } S`
with $`i` a closed immersion and $`f'` separated, quasi-compact and locally of finite
presentation.
:::

:::proof "thm:01ZJ" (uses := "thm:09ZQ, thm:086Q")
Take a finite presentation approximation of $`f` and descend the separatedness of $`f` to a
stage of the system; that stage is the required envelope.
:::

# The case of a morphism of finite presentation

:::theorem "thm:fp-nagata" (parent := "grp:approximation") (lean := "AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation")
Let $`S` be quasi-compact quasi-separated and let $`f \colon X \to S` be separated,
quasi-compact and locally of finite presentation. Then $`f` admits a compactification.
:::

:::proof "thm:fp-nagata" (uses := "thm:01ZA, thm:01ZQ, thm:noetherian, thm:base-change")
Write $`S = \varprojlim_i D_i` as a cofiltered limit of Noetherian stages with affine
transition morphisms. The morphism $`f` descends to a morphism $`p \colon Y \to D_i` over one
of the stages which is again separated, quasi-compact and locally of finite presentation,
with $`f` the base change of $`p`. The stage $`D_i` is Noetherian, so $`p` admits a
compactification by the Noetherian case. Base changing that compactification back along
$`S \to D_i` compactifies $`f`.
:::
