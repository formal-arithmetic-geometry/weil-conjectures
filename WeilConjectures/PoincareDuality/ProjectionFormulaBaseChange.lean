/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange
public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison

/-!

# The projection formula is compatible with base change

For a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
of separated `k`-schemes of finite type, the exceptional projection morphisms
`PF^!_f : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` of `f` and `f'` are compatible with compact-support
base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` (SGA 4, Exposé XVII, §5.2): the square
```
Lg^* (Rf_! K ⊗ᴸ B) ──Lg^* PF──▶ Lg^* Rf_! (K ⊗ᴸ Lf^* B) ──Ex_!──▶ Rf'_! Lg'^* (K ⊗ᴸ Lf^* B)
       │≅                                                               │≅
       ▼                                                               ▼
Rf'_! Lg'^* K ⊗ᴸ Lg^* B ─────────────PF'────────────▶ Rf'_! (Lg'^* K ⊗ᴸ Lf'^* Lg^* B)
```
commutes. In the formalism of `CategoryTheory.ProjectionBaseChange` this is
`CategoryTheory.ProjectionBaseChange.PFBaseChange`.

## Sorried input

- `ProEtale.CondensedRing.pfBaseChange_boundedConstructibleExceptionalProjection`: the clause
  "compatible with base change" of blueprint `sk-prop-sf-pf-coherence` (section
  `sec-six-functors`). For proper `f` and `f'` it is proved in
  `WeilConjectures.TraceFormula.LowerShriekCoherence`
  (`ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_baseChange`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The projection formula is compatible with base change** (blueprint `sk-prop-sf-pf-coherence`,
section `sec-six-functors`, the clause "it is compatible with base change: for a Cartesian square
`(f', g', f, g)` [...] the square [...] commutes"; SGA 4, Exposé XVII, §5.2): for a cartesian
square, the exceptional projection morphisms of `f` and `f'` are compatible with compact-support
base change `Ex_!` and the pullback comparison `Lf'^* Lg^* ≅ Lg'^* Lf^*`. -/
theorem pfBaseChange_boundedConstructibleExceptionalProjection (sq : IsPullback g' f' f g) :
    ProjectionBaseChange.PFBaseChange (boundedConstructibleUpperStar _ ℓ g)
      (boundedConstructibleUpperStar _ ℓ g')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (boundedConstructiblePullbackSquareComparison _ ℓ sq.toCommSq)
      (boundedConstructibleExceptionalProjection _ ℓ f)
      (boundedConstructibleExceptionalProjection _ ℓ f') :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
