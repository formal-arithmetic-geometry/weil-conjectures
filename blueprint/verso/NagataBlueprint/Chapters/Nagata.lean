import NagataBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Nagata compactification theorem" =>

:::group "grp:nagata"
The final assembly.
:::

:::theorem "thm:nagata" (parent := "grp:nagata") (tags := "main-theorem") (lean := "AlgebraicGeometry.NagataCompactification")
*Nagata compactification.* Let $`Y` be a quasi-compact quasi-separated scheme and let
$`f \colon X \to Y` be separated, quasi-compact and locally of finite type. Then $`f`
factors as an open immersion followed by a proper morphism; that is, $`f` admits a
compactification {uses "def:compactification"}[].
:::

:::proof "thm:nagata" (uses := "thm:01ZJ, thm:fp-nagata, cor:closed-subscheme")
Since $`f` is quasi-compact with quasi-compact quasi-separated target, the source $`X` is
quasi-compact quasi-separated as well. The morphism $`f` is only locally of finite _type_,
whereas the finite-presentation case requires finite _presentation_; the bridge is the
finite-presentation envelope, which writes $`f = f' \circ i` with $`i \colon X \to X'` a
closed immersion and $`f' \colon X' \to Y` separated, quasi-compact and locally of finite
presentation. The morphism $`f'` admits a compactification, and cutting that compactification
back along the closed immersion $`i` compactifies $`f`.
:::

# What the argument takes from outside

The chain leading to the theorem contains no open step: every statement above is proved from
the statements before it together with the following facts, which the argument uses but does
not establish.

* *Scheme-theoretic images.* Existence of the scheme-theoretic image of a quasi-compact
  morphism, its universal factorization property, and the fact that a quasi-compact immersion
  factors as an open immersion onto its scheme-theoretic image followed by a closed
  immersion. First used in {bpref "def:of-immersion"}[].
* *Zariski's Main Theorem.* A separated, quasi-compact, locally quasi-finite morphism of
  finite type factors as an open immersion into the relative normalization of the target in
  the source followed by an integral morphism, recorded as {bpref "thm:zmt-factorization"}[].
  Its two consequences used here are proved in this development and recorded as
  {bpref "cor:quasi-affine-of-quasi-finite"}[]; the theorem itself is
  taken from the ambient library. Used exactly once, to pass from
  {bpref "thm:graph-quasi-finite"}[] to {bpref "thm:conrad24"}[].

Two points deserve emphasis, since the classical treatment proceeds differently.

* _Elimination of indeterminacy is unconditional here._ The classical derivation of
  {bpref "thm:081S"}[] rests on module flattening by blowing up, and thence on a dévissage
  which is not developed here. The route taken instead — through {bpref "thm:conrad24"}[] and
  Zariski's Main Theorem, prepared by {bpref "thm:disjointness"}[],
  {bpref "thm:conrad-case1"}[], {bpref "thm:conrad-case2"}[], {bpref "thm:conrad-case3"}[]
  and {bpref "thm:graph-quasi-finite"}[] — avoids flattening altogether.
* _The two-open theorem does not use flattening either._ It proceeds by boundary separation
  ({bpref "thm:0F3V"}[]), common modifications ({bpref "thm:0F3X"}[]) and the dense-source
  valuative criterion ({bpref "thm:dense-valuative-criterion"}[]).

# Scope of the three principal statements

The hypotheses of the three compactification theorems differ, and the differences matter.

* {bpref "thm:noetherian"}[] needs the _base_ to be Noetherian; the morphism is separated,
  locally of finite type and quasi-compact.
* {bpref "thm:fp-nagata"}[] needs the base only quasi-compact quasi-separated, but requires
  the morphism to be locally of finite _presentation_.
* {bpref "thm:nagata"}[] needs the base only quasi-compact quasi-separated and the morphism
  only locally of finite _type_, in addition to separated and quasi-compact.

Similarly, {bpref "thm:conrad24"}[] assumes the preserved open $`U` to be dense in $`X`,
whereas {bpref "thm:conrad-case3"}[] does not; and {bpref "thm:080E"}[] requires no
finiteness hypothesis at all, whereas {bpref "thm:0803"}[], {bpref "thm:080B"}[] and
{bpref "thm:080M"}[] require the ambient scheme to be quasi-compact quasi-separated and the
centres to be of finite type.
