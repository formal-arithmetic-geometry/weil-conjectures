/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Locally free sheaves of finite rank are coherent

A sheaf of modules which is locally free of finite rank — that is, one admitting local
generators which are simultaneously a basis and finite in number — is coherent:
`SheafOfModules.LocalGeneratorsData.isCoherent`. In particular the unit `SheafOfModules.unit R`,
which over a scheme is the structure sheaf, is coherent.
-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts C]

instance (ι : Type u) [Finite ι] : (free (R := R) ι).IsFiniteType :=
  have : (free.generatingSections (R := R) ι).IsFiniteType := ⟨inferInstanceAs (Finite ι)⟩
  (free.generatingSections ι).isFiniteType

/-- A finite free sheaf of modules is coherent. -/
instance (ι : Type u) [Finite ι] : (free (R := R) ι).IsCoherent where

/-- The unit sheaf of modules — over a scheme, the structure sheaf — is coherent. -/
instance : (unit R).IsCoherent :=
  (isCoherent R).prop_of_iso (freeUniqueIso PUnit.{u + 1}) inferInstance

end

/-- **A locally free sheaf of finite rank is coherent.** Here "locally free of finite rank" is
recorded as the existence of local generators `q` which are a basis (`q.IsLocallyFreeData`) and
finite in number (`q.IsFiniteType`). -/
theorem LocalGeneratorsData.isCoherent {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] [q.IsFiniteType] : M.IsCoherent :=
  have := q.quasiCoherentData.isQuasicoherent
  have := q.isFiniteType
  ⟨⟩

instance (M : SheafOfModules.{u} R) [M.IsLocallyFree] [M.IsFiniteType] : M.IsCoherent where

end SheafOfModules
