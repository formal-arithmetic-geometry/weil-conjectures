/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.SixFunctors.BifunctorHomHomotopyExactSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Exactness of the native derived internal Hom in its source

## References

* Stacks Project, Cohomology on Sites, Tag 08JC
-/

@[expose] public section

set_option autoImplicit false

universe c v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open CategoryTheory.Pretriangulated.Opposite

namespace DerivedCategory

section
variable (C : Type c) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

private instance internalHom_additive : (MonoidalClosed.internalHom (C := C)).Additive where
  map_add := by
    intro X Y f g
    ext Z
    exact MonoidalClosed.pre_add_app f.unop g.unop Z

private instance internalHom_obj_additive (X : Cᵒᵖ) :
    (MonoidalClosed.internalHom.obj X).Additive :=
  inferInstanceAs (ihom X.unop).Additive

omit [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C] in
private theorem model_map {P P' : CochainComplex C ℤ} (f : P ⟶ P')
    (I : CochainComplex C ℤ) :
    CochainComplex.bifunctorHomMapLeft (H := MonoidalClosed.internalHom) (Y := I) f =
      CochainComplex.internalHomPre f I := by
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.internalHomObj_hom_ext
  intro p q h
  change (CochainComplex.bifunctorHomMapLeft f).f n ≫
      CochainComplex.bifunctorHomπ MonoidalClosed.internalHom P I n p q h = _
  rw [CochainComplex.bifunctorHomMapLeft_f_π]
  exact (CochainComplex.internalHomPre_f_π f I n p q h).symm

private noncomputable def modelComparison (I : CochainComplex C ℤ) [I.IsKInjective] :
    (CochainComplex.bifunctorHomHomotopyFunctor MonoidalClosed.internalHom I).leftOp ≅
      Qh.op ⋙ MonoidalClosed.internalHom.flip.obj (Q.obj I) := by
  refine NatIso.ofComponents
    (fun X ↦ asIso (qhInternalHomToIhom X.unop.as I) ≪≫
      (ihom _).mapIso ((quotientCompQhIso C).app I)) ?_
  intro X Y f
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f.unop
  have hf : f = ((HomotopyCategory.quotient C (.up ℤ)).map g).op := by
    rw [hg]
    rfl
  subst f
  change Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.bifunctorHomMapLeft
        (H := MonoidalClosed.internalHom) (Y := I) g)) ≫ qhInternalHomToIhom P' I ≫
      (ihom _).map ((quotientCompQhIso C).hom.app I) =
    (qhInternalHomToIhom P I ≫ (ihom _).map ((quotientCompQhIso C).hom.app I)) ≫ _
  rw [model_map C, reassoc_of% qhInternalHomToIhom_naturality g I, Category.assoc]
  congr 1
  exact ((MonoidalClosed.pre _).naturality _).symm

end

/-- The native derived closed structure is exact in the contravariant variable.
Source: Stacks Project, Tag 08JC. -/
theorem nativeInternalHom_contravariant_exact
    (C : Type c) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (W : DerivedCategory C) :
    ∃ s : (MonoidalClosed.internalHom.flip.obj W).CommShift ℤ,
      letI := s
      (MonoidalClosed.internalHom.flip.obj W).IsTriangulated := by
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_iso_Q_obj_of_isKInjective W
  have := hI
  let F := (CochainComplex.bifunctorHomHomotopyFunctor MonoidalClosed.internalHom I).leftOp
  let T := MonoidalClosed.internalHom.flip.obj W
  obtain ⟨sF, hF⟩ :=
    CochainComplex.bifunctorHomHomotopyFunctor_leftOp_exact MonoidalClosed.internalHom I
  let := sF
  have := hF
  let e : F ≅ Qh.op ⋙ T := modelComparison C I ≪≫
    isoWhiskerLeft Qh.op (MonoidalClosed.internalHom.flip.mapIso eI.symm)
  let V := (HomotopyCategory.quasiIso C (.up ℤ)).op
  let : Localization.Lifting Qh.op V F T := ⟨e.symm⟩
  let sT := Functor.commShiftOfLocalization Qh.op V ℤ F T
  let := sT
  have : NatTrans.CommShift e.inv ℤ :=
    inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso Qh.op V F T).hom ℤ)
  have : NatTrans.CommShift e.hom ℤ := by
    constructor
    intro n
    ext X
    dsimp
    rw [← cancel_epi (e.inv.app (X⟦n⟧)), e.inv_hom_id_app_assoc,
      ← NatTrans.shift_app_comm_assoc e.inv, ← Functor.map_comp,
      e.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  have : (Qh.op ⋙ T).IsTriangulated := Functor.isTriangulated_of_iso e
  have : Qh.op.mapArrow.EssSurj := Localization.essSurj_mapArrow Qh.op V
  exact ⟨sT, Functor.isTriangulated_of_precomp Qh.op T⟩

end DerivedCategory
