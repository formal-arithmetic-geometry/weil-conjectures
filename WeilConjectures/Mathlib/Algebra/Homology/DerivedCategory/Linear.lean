/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# The homology functors of the derived category are linear

For an `R`-linear abelian category `C`, the homology functors `D(C) ⥤ C` are `R`-linear
(`DerivedCategory.homologyFunctor_linear`): on objects of the form `Q L` the action of a scalar
is computed on the complex `L`, where homology is linear.
-/

@[expose] public section

open CategoryTheory Category

universe t w v u

namespace DerivedCategory

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C]

omit [HasDerivedCategory C] in
lemma _root_.HomologicalComplex.homologyMap_smul_id {ι : Type*} {c : ComplexShape ι}
    (L : HomologicalComplex C c) (i : ι) (r : R) :
    HomologicalComplex.homologyMap (r • 𝟙 L) i = r • 𝟙 _ := by
  have : (HomologicalComplex.shortComplexFunctor C c i).map (r • 𝟙 L) =
      r • 𝟙 ((HomologicalComplex.shortComplexFunctor C c i).obj L) := by
    ext <;> simp [HomologicalComplex.smul_f_apply] <;> rfl
  change ShortComplex.homologyMap _ = _
  rw [this, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

lemma homologyFunctor_map_smul_id (n : ℤ) (r : R) (X : DerivedCategory C) :
    (homologyFunctor C n).map (r • 𝟙 X) = r • 𝟙 _ := by
  let L := Q.objPreimage X
  let e : Q.obj L ≅ X := Q.objObjPreimageIso X
  have hQ : (homologyFunctor C n).map (r • 𝟙 (Q.obj L)) = r • 𝟙 _ := by
    rw [← cancel_mono ((homologyFunctorFactors C n).hom.app L)]
    have h := homologyFunctorFactors_hom_naturality (r • 𝟙 L) n
    rw [Functor.map_smul, CategoryTheory.Functor.map_id] at h
    rw [h, HomologicalComplex.homologyMap_smul_id]
    simp only [Linear.smul_comp, id_comp]
    exact (Linear.comp_smul (f := _) (r := r) (g := 𝟙 _)).trans (by rw [comp_id])
  have : r • 𝟙 X = e.inv ≫ (r • 𝟙 (Q.obj L)) ≫ e.hom := by simp
  rw [this, Functor.map_comp, Functor.map_comp, hQ, Linear.smul_comp, id_comp,
    Linear.comp_smul, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]

instance homologyFunctor_linear (n : ℤ) : (homologyFunctor C n).Linear R where
  map_smul {X Y} f r := by
    rw [show r • f = (r • 𝟙 X) ≫ f by simp, Functor.map_comp, homologyFunctor_map_smul_id,
      Linear.smul_comp, id_comp]

end DerivedCategory
