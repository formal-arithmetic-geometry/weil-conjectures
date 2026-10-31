/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces
import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Evaluation of inverse-image coefficient transport

Source: Zheng, Construction 5.15, Lemma 5.16 and Proposition 2.29(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem inverseConstantSection_unit
    {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O} (n : ℕ)
    (x : O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) (U : T.Etaleᵒᵖ) :
    (coefficientConstantSection (J := T.smallEtaleTopology) O ell n x).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj PUnit.{u + 2})).app U PUnit.unit) =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U x := by
  have h := ((sheafificationAdjunction T.smallEtaleTopology (Type (u + 1))).homEquiv
    ((Functor.const T.Etaleᵒᵖ).obj PUnit.{u + 2})
    ((sheafCompose T.smallEtaleTopology (forget CommRingCat.{u + 1})).obj
      (coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell n))).apply_symm_apply
      ((Functor.const T.Etaleᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ x)) ≫
        whiskerRight (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))))
          (forget CommRingCat.{u + 1}))
  exact congrArg (fun z ↦ z.app U PUnit.unit) h

private theorem inverseConstantSection_naturality
    {T : Scheme.{u}} {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (n : ℕ)
    (x : O ⧸ (Ideal.span ({ell} : Set O)) ^ (index n + 1)) :
    coefficientConstantSection (J := T.smallEtaleTopology) O ell (index n) x ≫
        (sheafCompose T.smallEtaleTopology (forget CommRingCat.{u + 1})).map
          (a.sheaf T n) =
      coefficientConstantSection (J := T.smallEtaleTopology) O' mu n (a.ring n x) := by
  apply ((sheafificationAdjunction T.smallEtaleTopology (Type (u + 1))).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  ext U t
  have hn := toSheafify_naturality T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).map (CommRingCat.ofHom (a.ring n)))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hn U) x).symm

private theorem inverseConstantSection_ext
    {T S : Scheme.{u}} (g : T ⟶ S)
    {O : Type (u + 1)} [CommRing O] {ell : O} (n : ℕ)
    {F : Sheaf T.smallEtaleTopology (Type (u + 1))}
    (f k : (Scheme.etaleSetPullback g).obj
      ((sheafCompose S.smallEtaleTopology (forget CommRingCat.{u + 1})).obj
        (coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell n)) ⟶ F)
    (h : ∀ x, (Scheme.etaleSetPullback g).map
        (coefficientConstantSection (J := S.smallEtaleTopology) O ell n x) ≫ f =
      (Scheme.etaleSetPullback g).map
        (coefficientConstantSection (J := S.smallEtaleTopology) O ell n x) ≫ k) : f = k := by
  apply ((strictEtaleSetAdjunction g).homEquiv _ _).injective
  apply Sheaf.hom_ext
  apply (cancel_epi (sheafifyComposeIso S.smallEtaleTopology
    (forget CommRingCat.{u + 1}) ((Functor.const S.Etaleᵒᵖ).obj
      (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).hom).1
  apply sheafify_hom_ext S.smallEtaleTopology _ _
    ((((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
      (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        (T.smallGrothendieckTopology @Etale)).obj F).property)
  simp only [← Category.assoc, sheafComposeIso_hom_fac]
  ext U x
  have hx := congrArg ((strictEtaleSetAdjunction g).homEquiv _ _) (h x)
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left] at hx
  have hx' := congrArg (fun z ↦ z.hom.app U
    ((toSheafify S.smallEtaleTopology
      ((Functor.const S.Etaleᵒᵖ).obj PUnit.{u + 2})).app U PUnit.unit)) hx
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply, inverseConstantSection_unit, TypeCat.Fun.toFun_apply,
    whiskerRight_app, TypeCat.ofHom_apply] at hx' ⊢
  convert hx' using 1 <;> rfl

private theorem inverseCoefficient_ringSquare
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {T S : Scheme.{u}} (g : T ⟶ S)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (n : ℕ) :
    (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (forget CommRingCat.{u + 1})).map
          (a.sheaf S n)) ≫ (B.lift n).ringUnderlying.hom =
      (A.lift (index n)).ringUnderlying.hom ≫
        (sheafCompose T.smallEtaleTopology (forget CommRingCat.{u + 1})).map
          (a.sheaf T n) := by
  apply inverseConstantSection_ext g (index n)
  intro x
  rw [← Functor.map_comp_assoc, inverseConstantSection_naturality,
    B.constants, reassoc_of% (A.constants (index n) x),
    inverseConstantSection_naturality]
  have hpoint : B.singleton.hom = A.singleton.hom := by
    exact ((Types.isTerminalPUnit.isTerminalObj (Functor.const T.Etaleᵒᵖ) _).isTerminalObj
      (presheafToSheaf T.smallEtaleTopology (Type (u + 1))) _).hom_ext _ _
  rw [hpoint]

/-- Scalar extension commutes with the chosen ordinary etale inverse images.
The comparison satisfies exactly the tensor-unit equation used by finite transport.
Source: Zheng, Construction 5.15; Stacks Tags 03D2 and 03EL.
(blueprint: lem-pur-strict-etale-ordinary-inverse-comparison).

Proof: constant quotient sections generate the sheafified constant ring. The
constant-section normalization of both geometric lifts therefore identifies their
coefficient square. Apply the independent-universe scalar/inverse-image theorem,
using left exactness of etale set inverse image. Finally compose its unit identity
with the two underlying-module isomorphisms and the inverse comparison to put it
in the displayed convention. -/
theorem inverseCoefficient_ordinary_exists
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {T S : Scheme.{u}} (g : T ⟶ S)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (n : ℕ) :
    ∃ e : siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙
        (B.lift n).modules ≅ (A.lift (index n)).modules ⋙
          siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n),
      ∀ M,
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
            (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
              ((A.lift (index n)).modules.obj M)) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
            (e.inv.app M) ≫
          (B.lift n).moduleUnderlying.hom.app
            ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) =
        (A.lift (index n)).moduleUnderlying.hom.app M ≫
          (Scheme.etaleSetPullback g).map
            ((sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
              (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) := by
  have : PreservesFiniteLimits (Scheme.etaleSetPullback g) :=
    (etaleSetInverseImage_exact g).2.2.1
  obtain ⟨e, he⟩ := SheafOfModules.ScalarIndependent.exists_scalarInverseImageIndependent
    (Scheme.etaleSetPullback g) _ (strictEtaleSetAdjunction g)
    (A.lift (index n)) (B.lift n) (a.sheaf S n) (a.sheaf T n)
    (inverseCoefficient_ringSquare a g A B n)
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n))
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf S n))
    (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n))
  refine ⟨e, ?_⟩
  intro M
  have h := congrArg (fun z ↦ (A.lift (index n)).moduleUnderlying.hom.app M ≫ z)
    (he M)
  simp only [Iso.hom_inv_id_app_assoc] at h
  dsimp only [siteTensorUnitUnderlying, siteScalarUnderlyingIso, Iso.refl_hom,
    NatTrans.id_app]
  apply (cancel_mono ((B.lift n).moduleUnderlying.inv.app _ ≫
    (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map (e.hom.app M))).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map_comp,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.symm

end AlgebraicGeometry
