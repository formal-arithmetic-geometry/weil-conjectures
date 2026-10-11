## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcDescentEtale` states
`AlgebraicGeometry.etale_of_fpqc_cover`, with proof `sorry` as required for
stage 2. It uses `Scheme.fpqcTopology` and `Sieve.ofArrows` for the fpqc
covering family, and `pullback.snd f (g i)` for the second projection of the
base change.

The node's hypotheses render as follows:

- `f : X ⟶ S`, with `X S : Scheme.{u}`, renders a morphism of schemes.
- `S' : I → Scheme.{u}` and `g : ∀ i, S' i ⟶ S`, with `I : Type v`, render the
  indexed family of scheme morphisms.
- `hg : Sieve.ofArrows S' g ∈ Scheme.fpqcTopology S` renders that the family is
  an fpqc covering. Mathlib's `fpqcPrecoverage` is the quasi-compact flat
  precoverage and `fpqcTopology` is its generated topology.
- `h : ∀ i, Etale (pullback.snd f (g i))` renders etaleness of every base
  change, with `pullback.snd` the second projection of the chosen fibre
  product.

The conclusion `Etale f` renders that the original morphism is etale. The
index universe is independent (`I : Type v`), so empty and singleton index
types are allowed and no family cardinality is excluded. The identity-cover
singleton and the empty-scheme cases are type-correct. The theorem proof is
only `sorry`; no mathematical content is proved in this stage.

Dependencies used are Mathlib declarations: `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.Scheme.fpqcPrecoverage`/`fpqcTopology`,
`CategoryTheory.Limits.pullback` and `pullback.snd`, and
`AlgebraicGeometry.Etale`. The dependency nodes `def-pc-scheme`,
`def-weil-pbc-fpqc-covering`, `def-pc-fibre-product`, and
`def-weil-etale-morphism` all record these Mathlib notions.

Searches made: `msearch.py leanfinder` for etale descent returned no exact
match; `msearch.py loogle` found
`AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact`,
which only handles one surjective flat quasi-compact morphism; grep of Mathlib
confirmed this is the only such etale descent instance. `rg` over
`WeilConjectures` and the project found no declaration of this family-form
statement. The generic
`Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` in the source repository
was not attached because it is stated for a generic property and a covering
sieve, rather than this exact node statement.

No `STATEMENT-DISPUTED:` issue or dependency-record fault was found.

## Second reading by H1

The node introduces: (1) schemes `X,S` and a morphism `f : X ⟶ S`; (2) an
arbitrary index type `I`, schemes `S' i`, and morphisms `g i : S' i ⟶ S`; (3)
the fpqc-family condition; (4) for each `i`, the base change
`f_i : X ×_S S' i ⟶ S' i`, identified with `pullback.snd f (g i)`; (5) the
hypothesis that every `f_i` is etale; and (6) the conclusion that `f` is etale.

The original worker signature used
`Sieve.ofArrows S' g ∈ Scheme.fpqcTopology S`. That is Mathlib's generated
topology notion and does not render the node's definition: it can hold for a
family containing a non-flat arrow (for example, an identity arrow together
with an unrelated arrow), whereas the node requires every member to be flat.
I changed `hg` to the exact family definition: `(∀ i, Flat (g i))` together
with, for every affine open `V` of `S`, a finite `Fin n` list of indices and
affine opens `W j` whose images union to `V`. No other hypothesis or
conclusion changed. The quantifier order and independent universe `v` remain
as in the node, so empty `I` and `n = 0` are represented; the empty-scheme and
zero-object cases are type-correct.

Searches were repeated with `rg` over Mathlib and `WeilConjectures`, and with
the recorded LeanFinder/Loogle searches. No exact family-form declaration was
found. Mathlib's
`AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact`
only treats one surjective flat quasi-compact morphism, so it is not an exact
match. The source repository's generic
`Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` likewise uses a generic
morphism property and sieve hypothesis, not the node's family definition.

The repaired module compiles cleanly with only the expected `sorry` warning.

## Review fix (R-fde0652)

The second reading replaced `Sieve.ofArrows S' g ∈ Scheme.fpqcTopology S` (rightly
rejected: the generated topology admits non-flat members) by an inlined copy of the
fpqc-covering definition. That is a private copy of a notion the merged siblings
already render as `Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`
(lem-galois-fpqc-descend-open-immersion, lem-galois-fpqc-descend-unramified). Mathlib's
`fpqcPrecoverage` is the jointly surjective, quasi-compact family of flat morphisms
(`QuasiCompactCover`: every affine open of `S` is covered by finitely many images of
compact opens), which is the node's definition. The reviewer restored that form,
added the copyright header, imported `Mathlib.AlgebraicGeometry.Sites.Fpqc` in place of
`Pullbacks`, dropped the redundant `open AlgebraicGeometry`, and wrote the node's
proof into the docstring. The base change stays `pullback.snd f (g i)`, as in the C1
sibling and as the node's chosen fibre product.
