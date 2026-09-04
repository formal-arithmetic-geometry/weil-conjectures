import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Compactifications of morphisms" =>

:::group "grp:compactifications"
The formal calculus of compactifications: the notion itself, what it forces on the
compactified morphism, and the three stability constructions (immersions, closed
subschemes, base change).
:::

# The notion

:::definition "def:compactification" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.Compactification, AlgebraicGeometry.HasCompactification")
*Compactification of a morphism.*
Let $`f \colon X \to Y` be a morphism of schemes. A _compactification_ of $`f` is a triple
$`(Z, g, i)` consisting of a scheme $`Z`, a proper morphism $`g \colon Z \to Y` and an open
immersion $`i \colon X \to Z` such that
$$`f = g \circ i.`
We say that $`f` is _compactifiable_ if a compactification of $`f` exists.
:::

:::proposition "prop:compactification-basic" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.Compactification.isSeparated, AlgebraicGeometry.Compactification.locallyOfFiniteType, AlgebraicGeometry.Compactification.quasiCompact_openImmersion_iff, AlgebraicGeometry.Compactification.isProper_openImmersion, AlgebraicGeometry.Compactification.isClosedImmersion_openImmersion, AlgebraicGeometry.Compactification.isClopen_range_openImmersion")
*Properties forced by a compactification.*
Let $`(Z, g, i)` be a compactification of $`f \colon X \to Y`. Then

* $`f` is separated;
* $`f` is locally of finite type;
* $`i` is quasi-compact if and only if $`f` is quasi-compact;
* if $`f` is proper, then $`i` is proper, hence a closed immersion, and its range is open
  and closed in $`Z`.

These are the properties forced on $`f` and on the open immersion by the existence of a
compactification {uses "def:compactification"}[].
:::

:::proof "prop:compactification-basic"
The first two items hold because $`g` is proper, hence separated and locally of finite
type, $`i` is an open immersion, hence separated and locally of finite type, and both
classes are stable under composition. For the third, if $`i` is quasi-compact then so is
$`g \circ i = f`; conversely if $`g \circ i` is quasi-compact then $`i` is, because $`g` is
separated. The last item is the same cancellation for properness: $`g \circ i` proper and
$`g` separated force $`i` proper; a proper open immersion is a closed immersion, and a
morphism which is both an open and a closed immersion has open and closed range.
:::

:::proposition "prop:compactification-elementary" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.Compactification.ofIsProper, AlgebraicGeometry.Compactification.copy, AlgebraicGeometry.Compactification.precomp, AlgebraicGeometry.HasCompactification.comp_of_isOpenImmersion")
*Elementary constructions of compactifications.*
Three elementary constructions {uses "def:compactification"}[]:

* a proper morphism $`f` is a compactification of itself, via $`(X, f, \mathrm{id}_X)`;
* a compactification of $`f` is a compactification of any morphism equal to $`f`;
* _(restriction to open subschemes)_ if $`(Z, g, i)` compactifies $`f \colon X \to Y` and
  $`e \colon X' \to X` is an open immersion, then $`(Z, g, i \circ e)` compactifies
  $`f \circ e`. In particular compactifiability is inherited by open subschemes of the
  source.
:::

# Compactification by closing up an immersion

The scheme-theoretic image of a quasi-compact morphism, its canonical factorization, and
the fact that a quasi-compact immersion factors as an open immersion onto its
scheme-theoretic image followed by a closed immersion, are taken from the ambient library
and are not restated as nodes of this blueprint.

:::definition "def:of-immersion" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.Compactification.ofIsImmersion")
*Compactification constructed from an immersion.*
Let $`g \colon X \to Y` be a quasi-compact immersion and let $`p \colon Y \to S` be proper.
The factorization of $`p \circ g` through the scheme-theoretic image of $`g`,
$$`X \xrightarrow{\ g_{\to}\ } \operatorname{im} g \xrightarrow{\ \iota\ } Y \xrightarrow{\ p\ } S,`
is a compactification of $`p \circ g` {uses "def:compactification"}[]: the first morphism is
an open immersion because $`g` is a quasi-compact immersion, and $`p \circ \iota` is proper
as the composite of a closed immersion with a proper morphism.
:::

:::theorem "thm:immersion-into-proper" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.HasCompactification.of_isImmersion")
*An immersion into a proper scheme is compactifiable.*
Let $`u \colon X \to S` be quasi-compact and suppose that $`u = p \circ g` for an immersion
$`g \colon X \to Y` and a proper morphism $`p \colon Y \to S`. Then $`u` admits a
compactification.
:::

:::proof "thm:immersion-into-proper" (uses := "def:of-immersion, prop:compactification-basic")
Since $`u = p \circ g` is quasi-compact and $`p` is separated, $`g` is quasi-compact, so the
closing-up construction applies.
:::

:::corollary "cor:closed-subscheme" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.Compactification.ofIsClosedImmersion, AlgebraicGeometry.HasCompactification.of_isClosedImmersion")
*Compactifiability is inherited by closed subschemes.*
Let $`i \colon X \to X'` be a closed immersion and let $`f' \colon X' \to S` be quasi-compact
and compactifiable. Then $`f' \circ i` admits a compactification; one may take for its
ambient scheme the scheme-theoretic image of $`X` inside the ambient scheme of a
compactification of $`f'`.
:::

:::proof "cor:closed-subscheme" (uses := "thm:immersion-into-proper, prop:compactification-basic")
Let $`(Z, g, j)` compactify $`f'`. The open immersion $`j` is quasi-compact, hence
$`j \circ i` is a quasi-compact immersion into the scheme $`Z`, which is proper over $`S`.
Now close up that immersion, using $`f' \circ i = g \circ (j \circ i)`.
:::

# Base change

:::definition "def:compactification-base-change" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.Compactification.ofIsPullback")
*Base change construction for a compactification.*
Let a cartesian square with horizontal morphisms $`h \colon X \to Y` and $`t \colon S \to T`
and vertical morphisms $`u \colon X \to S` and $`p \colon Y \to T` be given, and let
$`(Z, g, i)` be a compactification of $`p` {uses "def:compactification"}[]. Then
$`Z \times_T S \to S` is proper, the canonical morphism $`X \to Z \times_T S` determined by
$`h \circ i` and $`u` is an open immersion, and
$$`X \longrightarrow Z \times_T S \longrightarrow S`
is a compactification of $`u`.
:::

:::lemma_ "lem:base-change-square" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.Compactification.isPullback_of_isPullback")
*The base-changed open immersion square is cartesian.*
In the situation above, the square formed by $`h`, the morphism $`X \to Z \times_T S`, the
open immersion $`i` and the first projection $`Z \times_T S \to Z` is cartesian.
Consequently $`X \to Z \times_T S` is an open immersion, open immersions being stable under
base change.
:::

:::theorem "thm:base-change" (parent := "grp:compactifications") (lean := "AlgebraicGeometry.HasCompactification.of_isPullback")
*Compactifiability is stable under base change.*
If $`p \colon Y \to T` admits a compactification and $`u \colon X \to S` is a base change of
$`p` along a morphism $`t \colon S \to T`, then $`u` admits a compactification.
:::

:::proof "thm:base-change" (uses := "def:compactification-base-change, lem:base-change-square")
Base change the compactification and use the previous lemma to see that the induced
morphism from $`X` is an open immersion; properness is stable under base change.
:::
