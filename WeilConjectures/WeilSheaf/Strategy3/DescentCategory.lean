/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.IndexedCategory
public import WeilConjectures.WeilSheaf.SmoothPurityScalarDatumNamed

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

namespace CategoryTheory.K4Coefficient

inductive Label
  | source | sourceUnit | target | targetUnit

section

variable {C₀ C : Type*} [Category C₀] [Category C] [Preadditive C]
  (P : C₀ ⥤ C) (Q : C ⥤ C) (M N : C₀) (T U : C)

/-- Initial objects in their native presentations. -/
def baseValue : Label → C
  | .source => P.obj M
  | .sourceUnit => P.obj N
  | .target => T
  | .targetUnit => U

/-- Degree-one sources keep the natural-transformation component presentation. -/
def firstValue : Label → C
  | .source => (P ⋙ Q).obj M
  | .sourceUnit => (P ⋙ Q).obj N
  | .target => Q.obj T
  | .targetUnit => Q.obj U

/-- Further iterates only use ordinary geometric pullback. -/
def valueAt : ℕ → Label → C
  | 0 => baseValue P M N T U
  | 1 => firstValue P Q M N T U
  | n + 2 => fun i ↦ Q.obj (valueAt (n + 1) i)

def value (i : ℕ × Label) : C := valueAt P Q M N T U i.1 i.2

def shift (i : ℕ × Label) : ℕ × Label := (i.1 + 1, i.2)

def step (i : ℕ × Label) :
    Q.obj (value P Q M N T U i) ≅ value P Q M N T U (shift i) := by
  rcases i with ⟨n, i⟩
  cases n with
  | zero => cases i <;> exact Iso.refl (Q.obj _)
  | succ n => exact Iso.refl (Q.obj (valueAt P Q M N T U (n + 1) i))

/-- The scalar-law calculation takes place in its own category of labeled objects. -/
abbrev DescentCategory := Object (value P Q M N T U)

def object (i : ℕ × Label) : DescentCategory P Q M N T U := ⟨i⟩

def liftIso (i j : ℕ × Label)
    (e : value P Q M N T U i ≅ value P Q M N T U j) :
    object P Q M N T U i ≅ object P Q M N T U j where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

end

/-- Calculate in the dedicated category and realize the final equation once.
The source scalar equation keeps precisely its native descent-component type. -/
lemma scalarDatum_conjugate_indexed
    {C₀ C : Type*} [Category C₀] [Category C] [Preadditive C]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (b : P ⋙ Q ≅ P)
    {M N : C₀} {T U : C} (α : P.obj M ≅ T) (β : P.obj N ≅ U)
    (t : Q.obj T ⟶ T) (u : Q.obj U ⟶ U)
    (ha : Q.map α.hom ≫ t = b.hom.app M ≫ α.hom)
    (hb : Q.map β.hom ≫ u = b.hom.app N ≫ β.hom)
    (e : P.obj M ≅ P.obj N) (v : T ≅ U) (hv : v = α.symm ≪≫ e ≪≫ β)
    (c : ℤ) (he : c • (b.hom.app M ≫ e.hom) = Q.map e.hom ≫ b.hom.app N) :
    c • (t ≫ v.hom) = Q.map v.hom ≫ u := by
  let V := value P Q M N T U
  let F := pullback V Q shift (step P Q M N T U)
  let α' := liftIso P Q M N T U (0, .source) (0, .target) α
  let β' := liftIso P Q M N T U (0, .sourceUnit) (0, .targetUnit) β
  let e' := liftIso P Q M N T U (0, .source) (0, .sourceUnit) e
  let v' := liftIso P Q M N T U (0, .target) (0, .targetUnit) v
  have h := purity_scalarDatum_conjugate_named F α' β'
    (b.hom.app M) (b.hom.app N) t u
    (by
      change (𝟙 (Q.obj (P.obj M)) ≫ Q.map α.hom ≫ 𝟙 (Q.obj T)) ≫ t =
        b.hom.app M ≫ α.hom
      simpa only [Category.id_comp, Category.comp_id] using ha)
    (by
      change (𝟙 (Q.obj (P.obj N)) ≫ Q.map β.hom ≫ 𝟙 (Q.obj U)) ≫ u =
        b.hom.app N ≫ β.hom
      simpa only [Category.id_comp, Category.comp_id] using hb)
    e' v'
    (by
      apply Iso.ext
      change v.hom = α.inv ≫ e.hom ≫ β.hom
      rw [hv]
      rfl)
    c (by
      change c • (b.hom.app M ≫ e.hom) =
        (𝟙 (Q.obj (P.obj M)) ≫ Q.map e.hom ≫ 𝟙 (Q.obj (P.obj N))) ≫ b.hom.app N
      simpa only [Category.id_comp, Category.comp_id] using he)
  have h' := congrArg ((realize V).map) h
  change c • (t ≫ v.hom) =
    (𝟙 (Q.obj T) ≫ Q.map v.hom ≫ 𝟙 (Q.obj U)) ≫ u at h'
  simpa only [Category.id_comp, Category.comp_id] using h' 

end CategoryTheory.K4Coefficient
