/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ProEtaleCoefficientPullback
public import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison

/-! # The ordinary coefficient restriction tensor square

Source: Stacks, Modules on Sites, Tag 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.restrictScalars
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalarsObj
  CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

private theorem tensor_pair_map {M M' N N' : proEtaleRingModules Y R}
    (v : M ⟶ M') (w : N ⟶ N') (V : Y.ProEtᵒᵖ)
    (m : M.val.obj V) (n : N.val.obj V) :
    ((SheafOfModules.monoidalCategory R).tensorHom v w).val.app V
        (proEtaleTensorPair Y R M N V m n) =
      proEtaleTensorPair Y R M' N' V (v.val.app V m) (w.val.app V n) := by
  exact SheafOfModules.ScalarHomOrdinary.pure_map R v w V m n

private theorem ordinaryPullback_inv_unit (M : proEtaleRingModules Y R)
    (V : Y.ProEtᵒᵖ) (m : M.val.obj V) :
    ((ordinaryPullback f R S c).inv.app M).val.app
        ((proEtaleBaseChange f).op.obj V)
        (((proEtaleRingModuleAdjunction f R
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
          (Iso.refl _)).unit.app M).val.app V m) =
      ((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app
        V m := by
  have hm := unit_mateEquiv
    (proEtaleRingModuleAdjunction f R S c)
    (proEtaleRingModuleAdjunction f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionPullbackInv f R R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
      (𝟙 R) c.hom (Iso.refl _) c (by simp))) M
  have hmate := restrictionPullback_mate f R R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
    (𝟙 R) c.hom (Iso.refl _) c (by simp)
  dsimp only [TwoSquare.natTrans] at hmate
  rw [hmate] at hm
  have h := congrArg (fun v ↦ v.val.app V m) hm
  have hd := (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique f R R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
      (𝟙 R) c.hom (Iso.refl _) c (by simp))).1
    ((proEtaleRingModulePullback f R S c).obj M) V
    (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app V m)
  dsimp only [ordinaryPullback, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerRight_inv, whiskerRight_app, leftUnitor_inv_app, Iso.refl_inv, NatTrans.id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, asIso_hom]
  exact h.symm.trans hd

private theorem ordinary_tensor_pure (M N : proEtaleRingModules Y R)
    (V : Y.ProEtᵒᵖ) (m : M.val.obj V) (n : N.val.obj V) :
    (proEtaleOrdinaryTensorPullback f R S c M N).hom.val.app
        ((proEtaleBaseChange f).op.obj V)
        (((proEtaleRingModuleAdjunction f R S c).unit.app
          (((proEtaleOrdinaryTensor Y R).obj M).obj N)).val.app V
            (proEtaleTensorPair Y R M N V m n)) =
      proEtaleTensorPair X S ((proEtaleRingModulePullback f R S c).obj M)
        ((proEtaleRingModulePullback f R S c).obj N) ((proEtaleBaseChange f).op.obj V)
        (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app V m)
        (((proEtaleRingModuleAdjunction f R S c).unit.app N).val.app V n) := by
  exact (Classical.choose_spec
    (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).2 M N V.unop m n

attribute [local irreducible] ordinaryPullback proEtaleOrdinaryTensorPullback
  proEtaleRingModulePullback

private theorem ordinary_inverse_square
    (o : SheafOfModules.RingIsoTensorTransport
      (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (M N : proEtaleRingModules Y R) :
    (ordinaryPullback f R S c).inv.app
        (((proEtaleOrdinaryTensor Y R).obj M).obj N) ≫
        (pbcRestrict c.hom).map (proEtaleOrdinaryTensorPullback f R S c M N).hom ≫
        o.monoidal.toMonoidal.toOplaxMonoidal.δ
          ((proEtaleRingModulePullback f R S c).obj M)
          ((proEtaleRingModulePullback f R S c).obj N) =
      (proEtaleOrdinaryTensorPullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
        (Iso.refl _) M N).hom ≫
        (SheafOfModules.monoidalCategory
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).tensorHom
          ((ordinaryPullback f R S c).inv.app M)
          ((ordinaryPullback f R S c).inv.app N) := by
  apply ((proEtaleRingModuleAdjunction f R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    (Iso.refl _)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext R M N _
  intro V m n
  have hc := ordinary_tensor_pure f R S c M N V m n
  have hi := ordinary_tensor_pure f R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    (Iso.refl _) M N V m n
  change (o.monoidal.toMonoidal.toOplaxMonoidal.δ _ _).val.app _
      ((proEtaleOrdinaryTensorPullback f R S c M N).hom.val.app _
        (((ordinaryPullback f R S c).inv.app _).val.app _
          (((proEtaleRingModuleAdjunction f R
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
            (Iso.refl _)).unit.app _).val.app V
            (proEtaleTensorPair Y R M N V m n)))) =
    ((SheafOfModules.monoidalCategory
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).tensorHom
        ((ordinaryPullback f R S c).inv.app M)
        ((ordinaryPullback f R S c).inv.app N)).val.app _
      ((proEtaleOrdinaryTensorPullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
        (Iso.refl _) M N).hom.val.app _
          (((proEtaleRingModuleAdjunction f R
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
            (Iso.refl _)).unit.app _).val.app V
            (proEtaleTensorPair Y R M N V m n)))
  erw [ordinaryPullback_inv_unit f R S c, hc, hi]
  rw [tensor_pair_map,
    ordinaryPullback_inv_unit f R S c, ordinaryPullback_inv_unit f R S c]
  exact o.pure_hom _ _ _ _ _

private theorem invert_square {A : Type*} [Category* A]
    {a b d e z : A} (mu : a ≅ b) (beta : a ≅ d) (nu : d ≅ e)
    (pair : z ≅ e) (delta : b ⟶ z)
    (h : beta.inv ≫ mu.hom ≫ delta = nu.hom ≫ pair.inv) :
    mu.inv ≫ beta.hom = delta ≫ pair.hom ≫ nu.inv := by
  apply (cancel_epi mu.hom).1
  apply (cancel_epi beta.inv).1
  have hh := congrArg (fun v ↦ v ≫ pair.hom ≫ nu.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Category.comp_id] using hh.symm

/-- Coefficient restriction commutes with the canonical ordinary tensor pullback.

Source: Stacks, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback.
(blueprint: lem-pbc-coefficient-restriction-ordinary-tensor-square)

Proof: apply the module pullback adjunction to the inverse-oriented square.
The mate-unit identity and the sectionwise identity direct-image comparison show
that inverse coefficient transport preserves the pullback unit. Both geometric
tensor maps carry unit pure tensors to the tensor of the two unit sections.
The supplied restriction tensorator fixes pure sections, and tensor functoriality
identifies the other route. Sheafified pure-tensor extensionality proves equality.
Finally cancel the ordinary tensor and coefficient isomorphisms to reverse the square. -/
theorem ordinary_square
    (o : SheafOfModules.RingIsoTensorTransport
      (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (M N : proEtaleRingModules Y R) :
    (pbcRestrict c.hom).map (proEtaleOrdinaryTensorPullback f R S c M N).inv ≫
        (ordinaryPullback f R S c).hom.app
          (((proEtaleOrdinaryTensor Y R).obj M).obj N) =
      o.monoidal.toMonoidal.toOplaxMonoidal.δ
          ((proEtaleRingModulePullback f R S c).obj M)
          ((proEtaleRingModulePullback f R S c).obj N) ≫
        (SheafOfModules.monoidalCategory
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).tensorHom
          ((ordinaryPullback f R S c).hom.app M)
          ((ordinaryPullback f R S c).hom.app N) ≫
        (proEtaleOrdinaryTensorPullback f R
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
          (Iso.refl _) M N).inv := by
  let := SheafOfModules.monoidalCategory
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  exact invert_square
    ((pbcRestrict c.hom).mapIso (proEtaleOrdinaryTensorPullback f R S c M N))
    ((ordinaryPullback f R S c).app _)
    (proEtaleOrdinaryTensorPullback f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) M N)
    (MonoidalCategory.tensorIso ((ordinaryPullback f R S c).app M)
      ((ordinaryPullback f R S c).app N)) _
    (ordinary_inverse_square f R S c o M N)

private theorem complex_component (P : CochainComplex (proEtaleRingModules Y R) ℤ)
    (n : ℤ) :
    ((complexPullback f R S c).hom.app P).f n =
      (ordinaryPullback f R S c).hom.app (P.X n) := by
  simp only [complexPullback, Functor.mapHomologicalComplexCompIso_hom_app_f]

private theorem ordinary_bifunctor_square
    (o : SheafOfModules.RingIsoTensorTransport
      (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (M N : proEtaleRingModules Y R) :
    (pbcRestrict c.hom).map (proEtaleOrdinaryTensorPullback f R S c M N).inv ≫
        (ordinaryPullback f R S c).hom.app
          (((proEtaleOrdinaryTensor Y R).obj M).obj N) =
      o.monoidal.toMonoidal.toOplaxMonoidal.δ
          ((proEtaleRingModulePullback f R S c).obj M)
          ((proEtaleRingModulePullback f R S c).obj N) ≫
        ((proEtaleOrdinaryTensor X
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).map
            ((ordinaryPullback f R S c).hom.app M)).app
              ((pbcRestrict c.hom).obj ((proEtaleRingModulePullback f R S c).obj N)) ≫
        ((proEtaleOrdinaryTensor X
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).obj
            ((proEtaleRingModulePullback f R
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
              (Iso.refl _)).obj M)).map ((ordinaryPullback f R S c).hom.app N) ≫
        (proEtaleOrdinaryTensorPullback f R
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
          (Iso.refl _) M N).inv := by
  simpa only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
    Category.assoc] using ordinary_square f R S c o M N

end AlgebraicGeometry.Scheme.CoefficientTensorChain
