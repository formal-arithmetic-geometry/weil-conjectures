/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor


@[expose] public section
universe u v u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
open scoped ChangeOfRings

/--
The proof cancels the tensor comparison and uses the tensor universal property to identify maps.
Source: Stacks Project, Modules on Sites, Tag 03EL.
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness).
Proof in words: cancel the tensor comparison and apply the tensor universal property. -/
theorem canonicalRingedTensorComparison_unit_unique
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∀ (j j' : L.obj (SheafOfModules.unit ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ),
      (      ∀ M : SheafOfModules.{u}
          ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) ) → (      ∀ M : SheafOfModules.{u}
          ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j'.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) ) → j = j' := by
  sorry

end SheafOfModules
