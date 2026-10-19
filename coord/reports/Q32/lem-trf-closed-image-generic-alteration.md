## Worker report

The module `Sheaf.TraceFormula.ClosedImageGenericAlteration` states
`AlgebraicGeometry.Orgogozo.exists_closed_image_generic_alteration` with proof `sorry`.
It uses the recorded declarations `AlgebraicGeometry.IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsClosedImmersion`
from `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsIntegral`
from `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsFinite` from
`Mathlib.AlgebraicGeometry.Morphisms.Finite`, and
`AlgebraicGeometry.Orgogozo.IsAlteration` from `Sheaf.Paper.OrgogozoInductionData`.

The binders `(X Y : Scheme.{u}) [IsReduced X] [IsNoetherian X] [IsReduced Y]
[IsNoetherian Y]` render that `h : Y → X` is a morphism of reduced Noetherian schemes.
The binder `[IsProper h]` renders that `h` is proper. The data
`(Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]` renders the
integral closed subscheme `Z ↪ X`. The hypothesis
`Set.range i.base ⊆ Set.range h.base` renders containment of its underlying space in
the image of `h`.

The conclusion quantifies `W`, `j : W ⟶ Y`, and `a : W ⟶ Z`. The conjuncts
`IsClosedImmersion j` and `IsIntegral W` render an integral closed subscheme
`W ↪ Y`. The equation `a ≫ i = j ≫ h` is exactly the required compatibility.
The remaining conjuncts render, respectively, properness (`IsProper a`),
surjectivity (`Surjective a`), finiteness after restriction to a dense open
`U : Z.Opens` (`Dense (U : Set Z) ∧ IsFinite (pullback.snd a U.ι)`), and the
stated alteration conclusion (`IsAlteration a`). The dense-open restriction is
written via the canonical fibre product projection used by `IsAlteration` itself.

Edge cases checked: `Z` is integral and therefore nonempty, so its generic-point
argument is meaningful; `W` is explicitly required integral; no nonemptiness of `X`
or `Y` is added; the dense open is quantified rather than fixed, and the empty
fibre cases are excluded only by the source hypothesis that the image contains
`Z`. The identity proper map and a proper map to a point agree with the shape of
the statement.

Searches for an existing statement or definition:

- `msearch.py ... leanfinder "proper morphism reduced Noetherian schemes integral closed subscheme image alteration generic point closure"`: returned only general `IsIntegral`, normalization, and `IsIntegralHom` declarations; no generic alteration statement.
- `msearch.py ... loogle "IsAlteration, IsProper, IsClosedImmersion, IsIntegral, Surjective"`: no result (the project-specific `IsAlteration` identifier is not in Loogle).
- `msearch.py ... grep "IsAlteration|generic.*alteration|closed.*image" AlgebraicGeometry`: no matching generic-image alteration declaration; only unrelated closed-image material.
- `rg` in `WeilConjectures/`: no matching statement or definition.
- `rg` in `lean/Sheaf`: no matching statement; the only relevant existing notion is
  `Orgogozo.IsAlteration`, which is imported and reused.

No `STATEMENT-DISPUTED` flag or node fault.

## Second reading by Q32

I reread the node and the complete theorem signature. The reduced and Noetherian
hypotheses occur for both source and target schemes; properness is a typeclass on
`h`; the closed immersion and integrality assumptions occur on `i` and `Z`; and the
underlying-image condition is exactly `Set.range i.base ⊆ Set.range h.base`. Each
conclusion clause is present: integral closed `W ↪ Y`, a map `a : W ⟶ Z`, the
commuting composite, properness, surjectivity, finite restriction over a dense open,
and the alteration conclusion. No additional geometric hypothesis or dropped clause
was found.
