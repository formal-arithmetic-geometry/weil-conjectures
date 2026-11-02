/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeProper

/-!

# The trivial compactification of a proper morphism in the exchange formalism

For a proper morphism `g`, the identification `Rg_!^{𝟙} ≅ Rg_*` of the trivial compactification
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationOfIsProperIso`) is
`(𝟙)_! ≅ 𝟭` of the exchange formalism `boundedConstructibleExchangeFormalism`, whiskered by `Rg_*`.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (c : Compactification f.left) (c' : Compactification f'.left)
  (h : c'.overObj ⟶ c.overObj) (hi : IsPullback g' c'.overI c.overI h)
  (hp : IsPullback h c'.overG c.overG g)

omit [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom] in
/-- The identification `Rg'_!^{𝟙} ≅ Rg'_*` of the trivial compactification of a proper `g'` is
`(𝟙)_! ≅ 𝟭` of the exchange formalism. -/
lemma boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_inv_eq [IsProper g'.left] :
    (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ g').inv =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight ((𝔽).shId (SepFinType.mk X')).inv ((𝔽).pf (SepFinType.homMk g')) := by
  rw [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso,
    boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId]
  obtain ⟨X'l, ⟨⟨⟩⟩, X'h⟩ := X'
  obtain ⟨g'l, ⟨⟨⟨⟩⟩⟩, g'w⟩ := g'
  dsimp only at g'l
  obtain rfl : X'h = g'l ≫ X.hom := by simpa using g'w.symm
  rfl

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The identification `Rg_!^{𝟙} ≅ Rg_*` of the trivial compactification of a proper `g` is
`(𝟙)_! ≅ 𝟭` of the exchange formalism. -/
lemma boundedConstructibleLowerShriekOfCompactificationOfIsProperIso_hom_eq [IsProper g.left] :
    (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ g).hom =
      Functor.whiskerRight ((𝔽).shId (SepFinType.mk Y')).hom ((𝔽).pf (SepFinType.homMk g)) ≫
        (Functor.leftUnitor _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso,
    boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId]
  obtain ⟨Y'l, ⟨⟨⟩⟩, Y'h⟩ := Y'
  obtain ⟨gl, ⟨⟨⟨⟩⟩⟩, gw⟩ := g
  dsimp only at gl
  obtain rfl : Y'h = gl ≫ Y.hom := by simpa using gw.symm
  rfl

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
