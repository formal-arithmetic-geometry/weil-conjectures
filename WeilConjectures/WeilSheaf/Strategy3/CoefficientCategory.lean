/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.FinitePullback

/-! # A minimal category for finite K4 coefficient readings

Only objects, morphisms, composition, pullback and reading are needed for the finite
reading square. This category deliberately supplies no derived or monoidal structures.
Its single realization functor interprets the result in coefficient sheaves. All
comparison data come from the independently checked Strategy3 construction.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3.K4Coefficient

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- The finite coefficient objects used by the K4 reading calculation. -/
structure Object (X : Scheme.{u}) where
  val : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (coeffType.{u} T))

instance (X : Scheme.{u}) : Category (Object T X) where
  Hom A B := A.val ⟶ B.val
  id A := 𝟙 A.val
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- The only interpretation into the ambient coefficient category. -/
def realize (X : Scheme.{u}) :
    Object T X ⥤ Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (coeffType.{u} T)) where
  obj A := A.val
  map f := f

instance (X : Scheme.{u}) : (realize T X).Faithful where
  map_injective h := h

/-- Realization changes no morphisms, hence is fully faithful. -/
def fullyFaithfulRealize (X : Scheme.{u}) : (realize T X).FullyFaithful where
  preimage f := f
  map_preimage f := rfl
  preimage_map f := rfl

/-- Introduce a coefficient sheaf as one of the objects of the calculation. -/
def ofSheaf (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (coeffType.{u} T)) ⥤ Object T X where
  obj A := ⟨A⟩
  map f := f

lemma ofSheaf_realize (X : Scheme.{u}) : ofSheaf T X ⋙ realize T X = 𝟭 _ := by rfl

/-- Native geometric pullback on the dedicated coefficient objects. -/
noncomputable def upperStar {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Object T Y ⥤ Object T X where
  obj A := ⟨(g)^*[ModuleCat.{u + 1} (coeffType.{u} T)].obj A.val⟩
  map f := (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)].map f
  map_id A := (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)].map_id A.val
  map_comp f g' := (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)].map_comp f g'

lemma upperStar_realize {X Y : Scheme.{u}} (g : X ⟶ Y) :
    upperStar T g ⋙ realize T X =
      realize T Y ⋙ (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)] := by rfl

/-- Read an actual module object in the dedicated coefficient category. -/
noncomputable def reading (X : Scheme.{u}) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (coeffRing T) X) ⥤
      Object T X where
  obj A := ⟨(finiteCoefficientModEquivalence X T).functor.obj A⟩
  map f := (finiteCoefficientModEquivalence X T).functor.map f
  map_id A := (finiteCoefficientModEquivalence X T).functor.map_id A
  map_comp f g := (finiteCoefficientModEquivalence X T).functor.map_comp f g

lemma reading_realize (X : Scheme.{u}) :
    reading T X ⋙ realize T X = (finiteCoefficientModEquivalence X T).functor := by rfl

/-- The pullback comparison is constructed in the dedicated category. -/
noncomputable def readingPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Strategy3.upperStar (coeffRing T) g ⋙ reading T X ≅
      reading T Y ⋙ upperStar T g :=
  NatIso.ofComponents (fun A ↦
    { hom := (upperStarFiniteCoefficientModEquivalenceIso g T).hom.app A
      inv := (upperStarFiniteCoefficientModEquivalenceIso g T).inv.app A
      hom_inv_id := (upperStarFiniteCoefficientModEquivalenceIso g T).hom_inv_id_app A
      inv_hom_id := (upperStarFiniteCoefficientModEquivalenceIso g T).inv_hom_id_app A })
    (fun f ↦ (upperStarFiniteCoefficientModEquivalenceIso g T).hom.naturality f)

end AlgebraicGeometry.ProEtale.Strategy3.K4Coefficient
