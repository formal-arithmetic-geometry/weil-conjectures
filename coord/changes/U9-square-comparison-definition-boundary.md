# AlgebraicGeometry.ProEtale.ringSheafSquareComparison

## Reason

Kernel checking of the assigned coefficient equation repeatedly expands the transparent
square comparison through sheafification and chosen inverse-image left adjoints. Even a
reflexive component equation at `condensedRingObj` versus its point-pullback expansion
exceeds a diagnostic budget of 20,000 heartbeats. The complete original conversion
exceeds the unchanged 60-second file limit. The replacement creates a definition boundary
using choice of an isomorphism *equal to the existing explicit compositor*. Its witness
is that compositor with reflexive equality. The predicate uniquely determines the object;
no unproved existence theorem supplies data. A proved public equation recovers exactly
the old construction. No mathematical statement or target changes meaning.

## Old

```lean
abbrev ringSheafSquareComparison {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X) :=
  upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f))
```

## New

```lean
def ringSheafSquareComparison {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X) :
    upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} (pullback.fst g f) ≅
      upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} (pullback.snd g f) :=
  Classical.choose (show ∃ e :
      upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} (pullback.fst g f) ≅
        upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} (pullback.snd g f),
      e = upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f)) from
    ⟨upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f)), rfl⟩)

/-- The square comparison is the specified inverse-image compositor.

The equality in the choice predicate uniquely determines the comparison. Keeping that
predicate behind a definition boundary prevents kernel conversion from expanding the
chosen sheafification left adjoints in every component equation.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4).
(blueprint: def-sf-proetale-ring-sheaf-operations). -/
theorem ringSheafSquareComparison_eq {X' T X : Scheme.{u}}
    (g : X' ⟶ X) (f : T ⟶ X) :
    ringSheafSquareComparison g f =
      upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f)) := by
  unfold ringSheafSquareComparison
  exact Classical.choose_spec (show ∃ e :
      upperStar Ab.{u + 1} g ⋙ upperStar Ab.{u + 1} (pullback.fst g f) ≅
        upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} (pullback.snd g f),
      e = upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f)) from
    ⟨_, rfl⟩)
```

## Users

The operations module and both other direct users are unclaimed at the time of repair.
There are 190 transitive importers, but only four textual users of the comparison. Its
functor type, components and specified compositor are propositionally unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations | unclaimed | Equality-determined definition and proved public construction equation; zero holes before and after. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates | unclaimed | Replace unfolding of the square comparison in squareMonoidal by rewriting its construction equation, then unfold upperStarCompIso as before. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf | unclaimed | Statement uses the same comparison; source unchanged. Consumer compile checked separately. |
| Sheaf.Paper.CondensedOpenSquareScalarComparison | U9 | Use the public equation through a private component equation; all coefficient and adjunct normalizations retained. |

The original base-change-mates proof fails at line 60: `simp made no progress`, with
`ringSheafSquareComparison._proof_2 g f` having the unexpanded compositor predicate
where unfolding upperStarCompIso demanded the expanded predicate. The adaptation at
lines 59–60 is `rw [ringSheafSquareComparison_eq]` followed by
`dsimp only [upperStarCompIso]`. All existing signatures and other proof steps stay.

The definition node gains the proved construction equation in `lean.declarations` and
records the equality-determined construction in its proof fields. The source-library
boundary is respected: no file of `lean/WeilConjectures/` is changed.

## Status

landed 20261024T020809-L-2668101 2026-10-24 (merge of deliver/U9/Sheaf.Paper.CondensedOpenSquareScalarComparison)
