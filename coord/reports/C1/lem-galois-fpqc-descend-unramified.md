## Worker report

The module states the first assertion of Stacks Project, Descent, Lemma 02VM,
in its descent direction. Its only proof is `sorry`. The source was read in
`/home/ubuntu/c1-stacks-review/descent.tex`, lines 6187-6205; the repository's
`literature/stacks-project/descent.tex` is absent on this machine.

Hypotheses and conclusion, checked against the node:

- The schemes `S`, `X`, and the family `S_i` are `S X : Scheme.{u}` and
  `S' : I → Scheme.{u}`; `f : X ⟶ S` and `g : ∀ i, S' i ⟶ S` are the stated maps.
- An arbitrary index set is `I : Type v`. The fpqc-covering hypothesis is
  `Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`, the Mathlib match of
  `def-weil-pbc-fpqc-covering`.
- The fibre product `X ×_S S_i` is `pullback f (g i)`; its second projection
  is `pullback.snd f (g i)`, the recorded `def-pc-fibre-product` match.
- Each base change is unramified by the two conjuncts of `h`: its second
  projection is `LocallyOfFiniteType`, and its `pullback.diagonal` is
  `IsOpenImmersion`. These are exactly the recorded conjunction for
  `def-weil-unramified-morphism`.
- The conclusion is the same conjunction for `f`: `LocallyOfFiniteType f ∧
  IsOpenImmersion (pullback.diagonal f)`.

Dependency declarations used: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
(`Mathlib.AlgebraicGeometry.Scheme`); `AlgebraicGeometry.Scheme.fpqcPrecoverage`
(`Mathlib.AlgebraicGeometry.Sites.Fpqc`); `CategoryTheory.Limits.pullback`,
`pullback.snd`, and `pullback.diagonal` (Mathlib pullback modules);
`AlgebraicGeometry.LocallyOfFiniteType` (Mathlib finite-type morphisms) and
`AlgebraicGeometry.IsOpenImmersion` (Mathlib open immersions).

Edge cases: the index type can be empty; then an fpqc covering is possible
only for an empty base, and no nonempty-cover assumption was added. Empty
source schemes and arbitrary characteristics are included. The independent
universe `v` allows index sets of any size; all scheme objects use the same
universe `u`, as Mathlib's pullback does.

Searches for an existing statement:

- `leanfinder`, query `a morphism of schemes unramified if all pullbacks to an
  fpqc covering are unramified`: eight hits, all about formal unramifiedness
  or base change; no matching family-descent statement.
- `loogle`, query `AlgebraicGeometry.LocallyOfFiniteType,
  AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.Scheme.fpqcPrecoverage`:
  zero hits.
- Mathlib grep via `msearch.py`, query
  `DescendsAlong|FormallyUnramified|Unramified` in `AlgebraicGeometry/Morphisms`:
  only property descent along one surjective flat quasi-compact morphism,
  not this family assertion.
- `rg` of unramified descent and the generic fpqc descent helper in
  `WeilConjectures` and `lean/Sheaf`: the helper in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` is generic but does
  not itself state the unramified conclusion; no exact declaration found.
- `grep -rn` for the node ID in `WeilConjectures`: no result.

The node proof is represented in the declaration docstring step by step:
local finite type descent, diagonal base change and identification, open
immersion of each new diagonal, base change of the cover, open-immersion
descent, and the unramified conclusion.

## Second reading by C1

Independent comparison with the node and Stacks Project, Descent, Lemma 02VM
(first assertion, descent direction), and Definition 02KO:

- Objects: the node's schemes `X` and `S` are `{S X : Scheme.{u}}`; its
  arbitrary family of schemes `S_i` is `{I : Type v} {S' : I → Scheme.{u}}`.
  Verdict: the same schemes, with no base field or nonemptiness requirement.
- Maps: the node's `f : X → S` and `g_i : S_i → S` are
  `(f : X ⟶ S) (g : ∀ i, S' i ⟶ S)`. Verdict: exact domains, codomains,
  and quantifier order.
- Cover hypothesis: the node's fpqc covering is
  `(hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)`. The
  `def-weil-pbc-fpqc-covering` record identifies this Mathlib precoverage
  with Stacks 022B: flat arrows and a finite affine-open covering over
  each affine open of `S`. Verdict: no stronger covering hypothesis.
- Base changes: `pullback f (g i)` is the chosen `X ×_S S_i`, and
  `pullback.snd f (g i)` is `f_i : X ×_S S_i → S_i`, by the
  `def-pc-fibre-product` record and Mathlib's pullback universal property.
  Verdict: the node's second projection, not the first.
- Each unramified hypothesis is the `∀ i` in `h`; its two clauses are
  `LocallyOfFiniteType (pullback.snd f (g i))` and
  `IsOpenImmersion (pullback.diagonal (pullback.snd f (g i)))`.
  The `def-weil-unramified-morphism` record identifies precisely this
  conjunction with unramifiedness. Verdict: both clauses, no extra one.
- Conclusion: `LocallyOfFiniteType f ∧
  IsOpenImmersion (pullback.diagonal f)` is exactly the same conjunction
  for `f`. Verdict: no clause weakened or strengthened.

The empty index type is admitted; its cover hypothesis can hold on the
empty base. The empty source or base scheme and zero rings are not excluded.
There is no integer parameter or characteristic restriction. Universes `u`
and `v` are independent, and every variable is explicitly bound; the
single-file compile succeeds with relaxed auto-implicit disabled.

Independent searches: `msearch.py` leanfinder query "fpqc cover family
morphisms of schemes unramified descends" returned only formal-unramified
and cover infrastructure; loogle query with the qualified local-finite-type
and open-diagonal conjunction returned no result; `msearch.py` grep for the
declaration and unramified/fpqc combinations returned no result. Direct
`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` found the generic
fpqc descent helper in `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`
and single-morphism descent instances, but no declaration of this statement.

No mismatch was found; the Lean module and node record needed no change.
The module contains only the stated theorem with a `sorry` proof. Its
docstring follows the node's six proof steps: local finite type descent,
diagonal base change and cartesian pasting, open immersion after base change,
base change of the covering, descent of the open immersion, and the final
unramified conjunction. The module and declaration docstrings cite 02VM
and the blueprint ID. The single-file compile reported no error or warning.

## Reviewer note (R-fdu0632)

FIX: the import `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` was unused
(`Mathlib.AlgebraicGeometry.Sites.Fpqc` alone supplies `fpqcPrecoverage`,
`LocallyOfFiniteType`, `IsOpenImmersion` and `pullback.diagonal`; the file compiles
without it) and was removed. Correction to both readings: `def-weil-unramified-morphism`
has no recorded Lean declaration; the hypothesis and conclusion spell out its node
statement literally (locally of finite type and open-immersion diagonal), which is
the node's definition, not a recorded conjunction. Mathlib's
`DescendsAlong @FormallyUnramified (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`
(Morphisms/LocalFlatDescent.lean) is single-morphism descent of formal
unramifiedness, not this family statement; `existing: false` stands.
