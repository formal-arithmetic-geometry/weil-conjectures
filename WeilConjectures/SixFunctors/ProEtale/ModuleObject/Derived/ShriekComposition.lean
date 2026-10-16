/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# Composition of the derived lower and upper shrieks on bounded constructible complexes

As in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all
schemes are separated and of finite type over a field `k` of characteristic `p > 0` with
`p ≠ ℓ`, and all morphisms are morphisms of `Over (Spec (.of k))`. For composable morphisms
`f : X ⟶ Y` and `g : Y ⟶ S`, this file gives the composition isomorphisms
```
R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!,      R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!
```
on the bounded constructible derived categories.

The lower shriek `Rf_!` is defined through the compactification `compactificationOverField f`
chosen for each morphism separately, so the first isomorphism compares three unrelated
compactifications. Its construction needs a compactification of `f ≫ g` built from those of
`f` and `g`, proper base change `Rp_* i_! ≅ i'_! Rp'_*`, and the independence of the lower
shriek from the compactification
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl`), none
of which is available yet. It is therefore `sorry`ed.

The second isomorphism is constructed from the first: it is its conjugate (`conjugateIsoEquiv`)
under the adjunctions `R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`, the latter
being the composite of `Rf_! ⊣ Rf^!` and `Rg_! ⊣ Rg^!`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp`: `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
- `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp`: `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`.

## Sorried input

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp` is `sorry`, see above.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible complexes. It is currently `sorry`, see the module docstring. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp :
    boundedConstructibleLowerShriek Λ ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek Λ ℓ f ⋙ boundedConstructibleLowerShriek Λ ℓ g :=
  sorry

variable [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField g).overG).IsLeftAdjoint]
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField (f ≫ g)).overG).IsLeftAdjoint]

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible complexes: the conjugate of `boundedConstructibleLowerShriekComp` under the
adjunctions `R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp :
    boundedConstructibleUpperShriek Λ ℓ (f ≫ g) ≅
      boundedConstructibleUpperShriek Λ ℓ g ⋙ boundedConstructibleUpperShriek Λ ℓ f :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction Λ ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction Λ ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction Λ ℓ g))
    (boundedConstructibleLowerShriekComp Λ ℓ f g).symm

end AlgebraicGeometry.ProEtale.CondensedRing
