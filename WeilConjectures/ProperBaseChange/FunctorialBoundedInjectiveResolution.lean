/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus

import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.ProperBaseChange.FunctorialObjectResolution

/-!
# Functorial injective resolutions preserving every lower bound

Source: Stacks Project, Derived Categories, Tag 0141, assertion (1) and its construction
(blueprint: lem-weil-pbc-functorial-bounded-injective-resolution).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ZeroObject ComplexShape
open HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
end HomologicalComplex₂

namespace CochainComplex
namespace FunctorialInjectiveTotal

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (E : C ⥤ CochainComplex C ℕ)
variable (ε : single₀ C ⟶ E)
variable [E.PreservesZeroMorphisms]

private noncomputable abbrev extension : C ⥤ CochainComplex C ℤ :=
  E ⋙ embeddingUpNat.extendFunctor C

set_option backward.isDefEq.respectTransparency false in
private noncomputable def singleExtensionIso :
    single₀ C ⋙ embeddingUpNat.extendFunctor C ≅
      HomologicalComplex.single C (up ℤ) 0 :=
  NatIso.ofComponents (fun A ↦ HomologicalComplex.extendSingleIso embeddingUpNat A 0 0 rfl)
    (by
      intro A B f
      apply HomologicalComplex.Hom.ext
      funext n
      by_cases hn : n = 0
      · subst n
        dsimp only [Functor.comp_map, HomologicalComplex.comp_f]
        change (HomologicalComplex.extendMap ((single₀ C).map f) embeddingUpNat).f 0 ≫ _ = _
        rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := (0 : ℤ)) rfl]
        simp [HomologicalComplex.extendSingleIso_hom_f,
          HomologicalComplex.single_map_f_self]
      · apply IsZero.eq_of_tgt
        exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

private noncomputable def extendedAugmentation :
    HomologicalComplex.single C (up ℤ) 0 ⟶ extension E :=
  (singleExtensionIso (C := C)).inv ≫ Functor.whiskerRight ε (embeddingUpNat.extendFunctor C)

-- Outer degree is the original complex degree; inner degree is resolution degree.
private noncomputable def bicomplexFunctor :
    CochainComplex C ℤ ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (extension E).mapHomologicalComplex (up ℤ)

private noncomputable def bicomplexAugmentation :
    singleRow C (up ℤ) (up ℤ) 0 ⟶ bicomplexFunctor E :=
  NatTrans.mapHomologicalComplex (extendedAugmentation E ε) (up ℤ)

omit [E.PreservesZeroMorphisms] in
private theorem extension_neg (A : C) (q : ℤ) (hq : q < 0) :
    IsZero ((extension E).obj A |>.X q) := by
  change IsZero (((E.obj A).extend embeddingUpNat).X q)
  exact isZero_of_isStrictlyGE _ 0 q hq

private theorem bicomplex_below (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] (p q : ℤ) (hp : p < a) :
    IsZero (((bicomplexFunctor E).obj K).X p |>.X q) := by
  exact (HomologicalComplex.eval _ _ q).map_isZero
    ((extension E).map_isZero (isZero_of_isStrictlyGE K a p hp))

private theorem total_below (K : Plus C) (a : ℤ) [K.obj.IsStrictlyGE a] :
    IsStrictlyGE (((bicomplexFunctor E).obj K.obj).total (up ℤ)) a := by
  rw [isStrictlyGE_iff]
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  apply total.hom_ext
  intro p q hpq
  by_cases hq : q < 0
  · exact (extension_neg E (K.obj.X p) q hq).eq_of_src _ _
  · exact (bicomplex_below E K.obj a p q (by change p + q = n at hpq; omega)).eq_of_src _ _

private noncomputable def replacement : Plus C ⥤ Plus C where
  obj K := ⟨((bicomplexFunctor E).obj K.obj).total (up ℤ), by
    obtain ⟨a, ha⟩ := K.property
    exact ⟨a, total_below E K a⟩⟩
  map f := ObjectProperty.homMk (total.map ((bicomplexFunctor E).map f.hom) (up ℤ))
  map_id K := by
    ext : 1
    simp
  map_comp f g := by
    ext : 1
    simp

private noncomputable def augmentation : Plus.ι C ⟶ replacement E ⋙ Plus.ι C where
  app K := (singleRow₀ObjTotal K.obj).inv ≫
    total.map ((bicomplexAugmentation E ε).app K.obj) (up ℤ)
  naturality {K L} f := by
    have h := (bicomplexAugmentation E ε).naturality f.hom
    dsimp [replacement]
    have hi : f.hom ≫ (singleRow₀ObjTotal L.obj).inv =
        (singleRow₀ObjTotal K.obj).inv ≫ total.map
          ((singleRow C (up ℤ) (up ℤ) 0).map f.hom) (up ℤ) := by
      rw [← cancel_mono (singleRow₀ObjTotal L.obj).hom]
      simp [Category.assoc, singleRow₀ObjTotal_hom_naturality]
    change f.hom ≫ _ ≫ _ = (_ ≫ _) ≫ _
    rw [← Category.assoc, hi, Category.assoc, ← total.map_comp, h, total.map_comp]
    simp only [Category.assoc]

end FunctorialInjectiveTotal

end CochainComplex
