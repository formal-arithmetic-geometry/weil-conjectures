## Worker report

The module states `AlgebraicGeometry.isClosedImmersion_of_isAffineHom_of_surjective_structureStalks`.
Its proof is `sorry`. Source: Stacks Project, `morphisms.tex`, Lemma 01QO and Lemma 01SA.

Hypotheses and conclusion, clause by clause:

- `X Y : Scheme.{u}` are arbitrary schemes, rendering `def-pc-scheme`.
- `f : X ⟶ Y` is the given morphism.
- `[IsAffineHom f]` is the affineness hypothesis from `pqf-def-affine-morphism`.
- `hf : ∀ y : Y, Function.Surjective
  ((TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c)` says that every stalk
  of the natural map `f.c : O_Y ⟶ f_* O_X` is surjective. In particular, its
  quantifier ranges over points of `Y`, including those outside the image of `f`.
- `IsClosedImmersion f` is precisely the conclusion from `def-weil-closed-immersion`.

Dependencies used: `Mathlib.AlgebraicGeometry.Scheme` supplies `Scheme` and its
scheme morphisms; `Mathlib.AlgebraicGeometry.Morphisms.Affine` supplies
`AlgebraicGeometry.IsAffineHom`; and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` supplies
`AlgebraicGeometry.IsClosedImmersion`. The latter import exposes all three.
`Mathlib.Topology.Sheaves.Stalks` supplies `TopCat.Presheaf.stalkFunctor`.

Edge cases: `X` or `Y` may be empty. In particular the `∀ y : Y` hypothesis is
vacuous when `Y` is empty, and the conclusion is still the closed immersion of
the empty scheme. There is no finite-type, Noetherian, separated, field, or
characteristic assumption. The scheme universe is explicit; all variables are
bound. The hypothesis uses the direct-image stalk, not `f.stalkMap x`, whose
quantifier would range only over `x : X` and would change the statement.

Searches for an existing exact declaration:

- `msearch.py leanfinder "affine morphism of schemes surjective on stalks of
  structure sheaf to pushforward structure sheaf is closed immersion"` found
  `isClosedImmersion_iff_isAffineHom` and related affine-section criteria, but
  no theorem with the direct-image stalk hypothesis.
- `msearch.py loogle "AlgebraicGeometry.isClosedImmersion_iff_isAffineHom,
  AlgebraicGeometry.Scheme.Hom.app"` found the affine-section criterion only.
- `msearch.py grep "isClosedImmersion_iff_isAffineHom|surjective.*stalk|
  stalk.*surjective" AlgebraicGeometry/Morphisms` found the closed-immersion
  definition and stalk-map API, but no exact theorem.
- `rg` in `WeilConjectures` found closed-immersion lemmas with other hypotheses;
  exact-node-ID `grep` had no hit. `rg` in `lean/Sheaf` found only an unrelated
  projective-morphism use. Source inspection of Mathlib's
  `Morphisms/ClosedImmersion.lean` confirmed its criterion asks for surjectivity
  on sections over affine opens, a different hypothesis.

The Stacks source was read at `/home/ubuntu/c1-stacks-review/morphisms.tex`
because `literature/stacks-project/morphisms.tex` is absent from this checkout.
Lemma 01QO gives the closed-immersion criterion and Lemma 01SA identifies the
direct-image algebra for an affine morphism. No node fault or statement dispute
was found.

## Second reading by G1

The node introduces a morphism `f : X ⟶ Y` of schemes, with no restrictions on
the scheme universe beyond Lean's common `Scheme.{u}` category. Lean renders
these as `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`. The node's affine hypothesis is
rendered by `[IsAffineHom f]`, exactly the Mathlib declaration recorded for
`pqf-def-affine-morphism`; no finite-type, Noetherian, separated, field, or
characteristic assumption is added. The structure-sheaf map is rendered by
`f.c`, and the hypothesis `∀ y ∈ Y, O_{Y,y} → (f_* O_X)_y` surjective is exactly
`hf : ∀ y : Y, Function.Surjective
((TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c)`. The conclusion is
`IsClosedImmersion f`, the recorded Mathlib rendering of
`def-weil-closed-immersion`. Quantifiers and implication order agree with the
node.

Edge cases were checked: `Y` empty makes the stalk hypothesis vacuous, `X` may
be empty, and no positivity or nonzero assumption is present. The explicit
universe parameter does not exclude the cases represented in the node's
scheme category. The hypothesis uses the pushforward stalk over points of `Y`,
not `f.stalkMap` over points of `X`.

I repeated the existing-definition searches with `msearch.py` (LeanFinder and
Loogle queries in `searches.jsonl`), grep in Mathlib and `WeilConjectures`, and
`rg` in `lean/Sheaf`. They found only the affine-section criterion
`isClosedImmersion_iff_isAffineHom`, which is not the node's stalk formulation;
no exact declaration exists. The source was checked at Stacks Morphisms Lemmas
01QO and 01SA. No mismatch was found and no statement change was needed. The
only repair was to expand the declaration docstring with the node's explicit
three proof steps and all cited proof dependencies; the Lean signature remains
verbatim unchanged.
