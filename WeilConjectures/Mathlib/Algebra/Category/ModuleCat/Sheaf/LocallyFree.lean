/-
Copyright (c) 2026 Orchestra Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Orchestra Agent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Invertible sheaves of modules

A sheaf of modules is *invertible* if it is locally free of rank one, i.e. if it admits local
generators data all of whose generating families are indexed by a one-element type.

## Main definitions

- `SheafOfModules.LocalGeneratorsData.IsInvertibleData`: a predicate on
  `q : M.LocalGeneratorsData` saying that `q` is locally free data whose generating families
  are each indexed by a type with exactly one element.
- `SheafOfModules.IsInvertible`: `M : SheafOfModules R` is invertible if there exists
  invertible data for it.

## Main results

- `SheafOfModules.IsInvertible.of_iso`: invertibility only depends on the isomorphism class.
- `SheafOfModules.instIsInvertibleUnit`: the unit sheaf `𝒪` is invertible.
-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

noncomputable section

namespace SheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of modules on a one-element type is the unit sheaf of modules. -/
def freeUniqueIso (I : Type u) [Unique I] : free (R := R) I ≅ unit R :=
  coproductUniqueIso (fun _ : I ↦ unit R)

end

section

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Local generators data `q` is *invertible data* if it is locally free data whose
families of generators are each indexed by a type with exactly one element. -/
class IsInvertibleData {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) : Prop
    extends q.IsLocallyFreeData where
  nonempty_unique (i : q.I) : Nonempty (Unique (q.generators i).I)

/-- The transport of local generators data along an isomorphism of sheaves of modules. -/
@[simps]
def ofIso {M N : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) (e : M ≅ N) :
    N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (((overFunctor R (q.X i)).mapIso e).hom)

instance isLocallyFreeData_ofIso {M N : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] (e : M ≅ N) : (q.ofIso e).IsLocallyFreeData where
  isIso i := by
    change IsIso ((q.generators i).ofEpi _).π
    rw [GeneratingSections.ofEpi_π]
    infer_instance

instance isInvertibleData_ofIso {M N : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsInvertibleData] (e : M ≅ N) : (q.ofIso e).IsInvertibleData where
  nonempty_unique i := IsInvertibleData.nonempty_unique (q := q) i

instance IsInvertibleData.shrink {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsInvertibleData] : q.shrink.IsInvertibleData where
  __ := (inferInstance : q.shrink.IsLocallyFreeData)
  nonempty_unique i := IsInvertibleData.nonempty_unique (q := q) i.2.choose

end LocalGeneratorsData

/-- A sheaf of modules is *invertible* if it is locally free of rank one, i.e. if there
exist local generators satisfying `IsInvertibleData`. -/
class IsInvertible (M : SheafOfModules.{u} R) : Prop where
  exists_isInvertibleData : ∃ q : LocalGeneratorsData.{u₁} M, q.IsInvertibleData

theorem LocalGeneratorsData.isInvertible {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsInvertibleData] : M.IsInvertible := ⟨q.shrink, inferInstance⟩

instance (priority := 100) IsInvertible.isLocallyFree (M : SheafOfModules.{u} R)
    [h : M.IsInvertible] : M.IsLocallyFree :=
  have := h.exists_isInvertibleData.choose_spec
  ⟨h.exists_isInvertibleData.choose, inferInstance⟩

theorem IsInvertible.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [h : M.IsInvertible] :
    N.IsInvertible := by
  obtain ⟨q, hq⟩ := h.exists_isInvertibleData
  exact (q.ofIso e).isInvertible

end

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

instance (I : Type u) [Unique I] :
    (free.generatingSections (R := R) I).localGeneratorsData.IsInvertibleData where
  nonempty_unique _ := ⟨inferInstanceAs (Unique I)⟩

instance (I : Type u) [Unique I] : (free (R := R) I).IsInvertible :=
  (free.generatingSections I).localGeneratorsData.isInvertible

instance : (unit R).IsInvertible :=
  IsInvertible.of_iso (freeUniqueIso (R := R) PUnit.{u + 1})

end

section

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

theorem IsInvertible.isQuasicoherent (M : SheafOfModules.{u} R) [M.IsInvertible] :
    M.IsQuasicoherent :=
  inferInstance

end

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules isomorphic to the unit is generated by a single section. -/
def generatingSectionsOfUnitIso {M : SheafOfModules.{u} R} (e : M ≅ unit R) :
    M.GeneratingSections :=
  (free.generatingSections PUnit.{u + 1}).ofEpi (freeUniqueIso _ ≪≫ e.symm).hom

@[simp]
lemma generatingSectionsOfUnitIso_I {M : SheafOfModules.{u} R} (e : M ≅ unit R) :
    (generatingSectionsOfUnitIso e).I = PUnit.{u + 1} := rfl

instance {M : SheafOfModules.{u} R} (e : M ≅ unit R) :
    Unique (generatingSectionsOfUnitIso e).I :=
  inferInstanceAs (Unique PUnit.{u + 1})

instance {M : SheafOfModules.{u} R} (e : M ≅ unit R) :
    IsIso (generatingSectionsOfUnitIso e).π := by
  rw [generatingSectionsOfUnitIso, GeneratingSections.ofEpi_π]
  infer_instance

end

section

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Local generators data for a sheaf of modules which is locally isomorphic to the unit:
over each `X i`, the single section corresponding to `1`. -/
@[simps]
def localGeneratorsDataOfUnitIso {M : SheafOfModules.{u} R} {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (R.over (X i)))) : M.LocalGeneratorsData where
  I := I
  X := X
  coversTop := hX
  generators i := generatingSectionsOfUnitIso (h i).some

instance isInvertibleData_localGeneratorsDataOfUnitIso {M : SheafOfModules.{u} R} {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (R.over (X i)))) :
    (localGeneratorsDataOfUnitIso X hX h).IsInvertibleData where
  isIso i := by rw [localGeneratorsDataOfUnitIso_generators]; infer_instance
  nonempty_unique i := by
    rw [localGeneratorsDataOfUnitIso_generators]
    exact ⟨inferInstance⟩

/-- A sheaf of modules which is locally isomorphic to the unit is invertible. -/
theorem isInvertible_of_forall_over_unit {M : SheafOfModules.{u} R} {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X)
    (h : ∀ i, Nonempty (M.over (X i) ≅ unit (R.over (X i)))) : M.IsInvertible :=
  (localGeneratorsDataOfUnitIso X hX h).isInvertible

end

end SheafOfModules

end
