import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Quasi-coherent ideal sheaves of finite type" =>

:::group "grp:finite-type"
Finite-type quasi-coherent ideal sheaves, their extension across a quasi-compact open, their
compactness in the lattice of quasi-coherent ideal sheaves, the boundary ideals cutting out
the complement of a quasi-compact open, and the power lemma comparing two supports.
:::

A quasi-coherent ideal sheaf $`\sI` on a scheme $`X` is recorded by its ideals of sections
$`\sI(U)` over the affine opens $`U` of $`X`. These form a complete lattice, with $`\bot` the
zero ideal sheaf and $`\top` the unit ideal sheaf, and with products $`\sI \cdot \sL` and
suprema $`\sI \sqcup \sL` computed sectionwise. We write $`V(\sI)` for the support of $`\sI`
and $`\sI \cdot \sO_Y` for the inverse image ideal sheaf along $`Y \to X`.

:::definition "def:finite-type-ideal" (parent := "grp:finite-type") (lean := "AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteTypeOn, AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType")
*Ideal sheaves of finite type.*
Let $`\sI` be a quasi-coherent ideal sheaf on $`X` and let $`O \subseteq X` be an open. We say
$`\sI` is _of finite type_ on $`O` if $`\sI(U)` is a finitely generated ideal for every affine
open $`U \subseteq O`, and _of finite type_ if this holds for every affine open of $`X`.
:::

:::proposition "prop:finite-type-stability" (parent := "grp:finite-type") (lean := "AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType_top, AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType_bot, AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteTypeOn_iff_comap, AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteTypeOn.sup, AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteTypeOn.iSup, AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType.comap, AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType_of_isLocallyNoetherian")
*Stability properties of finite-typeness.*
The zero and unit ideal sheaves are of finite type. Finite-typeness on an open is
finite-typeness of the restriction to that open; it is local on the target, that is, stable
under finite suprema and under suprema of families of opens. On a locally Noetherian scheme
every quasi-coherent ideal sheaf is of finite type. Finite-typeness is stable under inverse
image along an arbitrary morphism {uses "def:finite-type-ideal"}[].
:::

:::theorem "thm:01PF" (parent := "grp:finite-type") (lean := "AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_le_comap_eq_of_le, AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_comap_eq")
*Stacks Tag 01PF: extension of a finite-type ideal sheaf across a quasi-compact open.*
Let $`X` be a quasi-compact quasi-separated scheme.

* Let $`\sI_0 \le \sH_0` be quasi-coherent ideal sheaves on $`X`, let $`W \subseteq X` be a
  quasi-compact open, and assume $`\sI_0` is of finite type on $`W`. Then there is a
  finite-type quasi-coherent ideal sheaf $`\sI \le \sH_0` on $`X` with
  $`\sI|_W = \sI_0|_W`.
* In particular, every finite-type quasi-coherent ideal sheaf $`\sJ` on a quasi-compact open
  $`W \subseteq X` extends to a finite-type quasi-coherent ideal sheaf $`\sI` on $`X` with
  $`\sI|_W = \sJ`.
:::

:::proof "thm:01PF" (uses := "prop:finite-type-stability")
One enlarges the open on which the ideal sheaf is of finite type one affine open at a time;
a finite induction over an affine cover then concludes. The binary gluing step is
order-theoretic: the glued ideal sheaf is the intersection of the maximal quasi-coherent
extensions of the current ideal sheaf and of a finitely generated approximation on the new
affine piece, intersected with the ambient ideal sheaf. Its restrictions are computed by
flat base change of scheme-theoretic images, and the approximation on the new affine piece is
obtained by clearing denominators on a finite cover of the overlap by basic opens.
:::

:::theorem "thm:01PF-affine" (parent := "grp:finite-type") (lean := "AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_le_comap_eq_of_isAffineHom, AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_le_comap_eq_disjoint_support")
*Extension of a finite-type centre along an affine morphism.*
Let $`X` be quasi-compact quasi-separated, let $`\sH_0` be a quasi-coherent ideal sheaf on
$`X` and let $`j \colon Z \to X` be an affine morphism such that $`\sH_0 \cdot \sO_Z` is of
finite type.
Then there is a finite-type $`\sI \le \sH_0` on $`X` with
$`\sI \cdot \sO_Z = \sH_0 \cdot \sO_Z`. If moreover $`V \subseteq X` is a quasi-compact open
with $`V \cap V(\sH_0) = \emptyset`, then $`\sI` may be chosen with
$`V \cap V(\sI) = \emptyset` as well.
:::

:::proof "thm:01PF-affine" (uses := "thm:01PF")
Cover $`X` by finitely many affine opens $`W`; over each of them choose finitely many
sections of $`\sH_0` already generating its inverse image over the affine open $`j^{-1}W`,
extend the ideal sheaf they span to a finite-type ideal sheaf inside $`\sH_0`, and sum over
the cover.
:::

:::theorem "thm:finite-type-directed" (parent := "grp:finite-type") (lean := "AlgebraicGeometry.Scheme.IdealSheafData.exists_le_of_ofFiniteType_le_iSup, AlgebraicGeometry.Scheme.IdealSheafData.directedOn_ofFiniteType_le, AlgebraicGeometry.Scheme.IdealSheafData.sSup_ofFiniteType_le_eq, AlgebraicGeometry.Scheme.IdealSheafData.directedOn_ofFiniteType_le_comap_eq_top, AlgebraicGeometry.Scheme.IdealSheafData.sSup_ofFiniteType_le_comap_eq_top_eq")
*Finite-type ideal sheaves are compact and exhaust every quasi-coherent ideal sheaf.*
Let $`X` be a quasi-compact scheme.

* If $`\mathcal{A}` is of finite type and $`\mathcal{A} \le \bigvee_i \mathcal{B}_i` for a
  directed family $`(\mathcal{B}_i)_i` of quasi-coherent ideal sheaves, then
  $`\mathcal{A} \le \mathcal{B}_i` for some $`i`.
* Every quasi-coherent ideal sheaf $`\sH` on a quasi-compact quasi-separated scheme is the
  supremum of the directed family of its finite-type quasi-coherent subsheaves. If moreover
  $`\sH` restricts to the unit ideal on a quasi-compact open $`U`, the same holds for the
  directed subfamily of those finite-type subsheaves which still restrict to the unit ideal
  on $`U`.
:::

:::proof "thm:finite-type-directed" (uses := "thm:01PF, prop:finite-type-stability")
Directedness of the family of finite-type subsheaves comes from stability under finite
suprema, and its supremum is computed affine-locally. Compactness of a finite-type element
is the statement that a finitely generated ideal contained in a directed supremum already
lies in one member.
:::

:::theorem "thm:01PH" (parent := "grp:finite-type") (lean := "AlgebraicGeometry.Scheme.exists_finiteType_ideal_coe_support_eq_compl, AlgebraicGeometry.Scheme.exists_finiteType_ideal_coe_support_eq_compl_of_isLocallyNoetherian")
*Stacks Tag 01PH: a quasi-compact open is the complement of the support of a finite-type ideal.*
Let $`X` be quasi-compact quasi-separated and let $`U \subseteq X` be a quasi-compact open.
Then there is a finite-type quasi-coherent ideal sheaf $`\sI` on $`X` with
$`V(\sI) = X \setminus U`. On a locally Noetherian scheme the same holds for an arbitrary
open $`U`, no quasi-compactness being needed.
:::

:::proof "thm:01PH" (uses := "thm:01PF")
The vanishing ideal of the reduced closed complement of $`U` restricts to the unit ideal on
$`U`; the extension theorem produces a finite-type subsheaf with the same restriction to
$`U`, and the support of such a subsheaf is exactly the complement of $`U`.
:::

:::lemma_ "lem:power-in-ideal" (parent := "grp:finite-type") (lean := "AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le")
*A finite-type ideal sheaf has a power inside any ideal sheaf whose support it contains.*
Let $`X` be quasi-compact, let $`\mathcal{A}, \mathcal{B}` be quasi-coherent ideal sheaves
with $`\mathcal{B}` of finite type, and assume $`V(\mathcal{A}) \subseteq V(\mathcal{B})`.
Then $`\mathcal{B}^n \le \mathcal{A}` for some $`n \in \mathbb{N}`.
:::

:::proof "lem:power-in-ideal" (uses := "def:finite-type-ideal")
The inclusion of supports says exactly that $`\mathcal{B}` is contained in the radical of
$`\mathcal{A}`. On an affine open, $`\mathcal{B}` is a finitely generated ideal inside the
radical of $`\mathcal{A}`, so some power of it lies in $`\mathcal{A}` there.
Quasi-compactness bounds these exponents: the maximum over a finite affine cover works
globally, containment of ideal sheaves being checkable on an affine cover.
:::
