import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Noetherian case" =>

:::group "grp:noetherian"
Induction over a finite affine open cover whose total intersection is dense: the base case is
the quasi-affine one, the inductive step is the two-open theorem.
:::

:::theorem "thm:dense-affine-cover" (parent := "grp:noetherian") (lean := "AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter")
*Dense affine covers exist.*
Let $`X` be a quasi-compact scheme with finitely many irreducible components. Then $`X`
admits a finite affine open cover $`U_0, \dots, U_{n-1}` whose total intersection
$`\bigcap_i U_i` contains every generic point of $`X`, and is therefore dense in $`X`.
:::

:::proof "thm:dense-affine-cover"
Every point has an affine open neighbourhood containing all generic points: take the disjoint
union of an affine neighbourhood of the point avoiding the components the point does not lie
on, together with one small affine neighbourhood of each remaining generic point.
Quasi-compactness extracts a finite cover from this family, and the total intersection of such
a cover contains all generic points, hence is dense.
:::

:::definition "def:partial-unions" (parent := "grp:noetherian") (lean := "AlgebraicGeometry.Scheme.partialAffineOpenUnions")
*The partial unions of a finite family of opens.*
For a finite family $`U_0, \dots, U_{n-1}` of opens of $`X` put $`X_r = \bigcup_{i < r} U_i`.
:::

:::lemma_ "lem:partial-unions-endpoints" (parent := "grp:noetherian") (lean := "AlgebraicGeometry.Scheme.partialAffineOpenUnions_zero, AlgebraicGeometry.Scheme.partialAffineOpenUnions_self")
*The extreme partial unions.*
The two extreme partial unions are $`X_0 = \emptyset` and $`X_n = \bigcup_i U_i`
{uses "def:partial-unions"}[].
:::

:::proof "lem:partial-unions-endpoints" (uses := "def:partial-unions")
Immediate from the definition: the empty supremum is $`\emptyset`, and for $`r = n` the
condition $`i < r` holds for every index of the family.
:::

:::lemma_ "lem:gluing-step" (parent := "grp:noetherian") (lean := "AlgebraicGeometry.HasCompactification.of_sup_of_dense_subset")
*The gluing step of the induction over a dense affine cover.*
Let $`S` be Noetherian and $`f \colon X \to S` separated, locally of finite type and
quasi-compact. Let $`D \subseteq X` be dense and contained in two opens $`V, W \subseteq X`,
and assume both $`f \circ \iota_V` and $`f \circ \iota_W` are compactifiable. Then
$`f \circ \iota_{V \cup W}` is compactifiable.
:::

:::proof "lem:gluing-step" (uses := "thm:two-open, prop:compactification-elementary")
Apply the two-open theorem to the two opens $`V, W` of the scheme $`V \cup W` and to the
restriction of $`f`. Their intersection contains $`D`, which is dense in $`V \cup W` because
$`V \cup W` is open in $`X`; the two restrictions inherit compactifiability from $`V` and
$`W`; and $`V \cup W` is Noetherian, $`X` being locally Noetherian and quasi-compact.
:::

:::theorem "thm:noetherian" (parent := "grp:noetherian") (lean := "AlgebraicGeometry.nagataCompactification_of_isNoetherian")
*Nagata compactification over a Noetherian base.*
Let $`S` be a Noetherian scheme and let $`f \colon X \to S` be separated, locally of finite
type and quasi-compact. Then $`f` admits a compactification.
:::

:::proof "thm:noetherian" (uses := "thm:dense-affine-cover, def:partial-unions, lem:gluing-step, thm:quasi-affine-compactifiable, prop:compactification-elementary")
Since $`f` is locally of finite type over a Noetherian base and quasi-compact, $`X` is a
Noetherian scheme; in particular it has finitely many irreducible components, so there is a
finite affine open cover $`U_0, \dots, U_{n-1}` with dense total intersection $`D`. We prove
by induction on $`r` that $`f \circ \iota_{X_r}` is compactifiable, for the partial unions.

For $`r = 0` the scheme $`X_0` is empty, so $`X_0 \to S` is proper and hence compactifiable.
For $`r = 1` the scheme $`X_1 = U_0` is affine, and the quasi-affine case applies. For the
step from $`r \ge 1` to $`r + 1`, write $`X_{r+1} = X_r \cup U_r`. The dense set $`D` is
contained in $`U_0 \subseteq X_r` and in $`U_r`, and both $`X_r \to S` and $`U_r \to S` are
compactifiable, the first by induction and the second again by the quasi-affine case. The
gluing step gives the claim for $`X_{r+1}`. The hypotheses of the gluing step hold at every
stage because separatedness, local finite type and quasi-compactness of $`X_r \to S` are
inherited from $`f` by the open subscheme $`X_r`. Since $`X_n = X`, the last stage
compactifies $`f`.
:::
