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

/-! # Finite ordinary inverse-image comparison for coefficient change

Source: Zheng, Construction 4.1 and Construction 5.15; Stacks Tag 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem coefficientConstantSection_hom_ext
    {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O} (n : ℕ)
    {N : Sheaf T.smallEtaleTopology (Type (u + 1))}
    (f g : (sheafCompose T.smallEtaleTopology
      (CategoryTheory.forget CommRingCat.{u + 1})).obj
        (coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell n) ⟶ N)
    (h : ∀ x, coefficientConstantSection (J := T.smallEtaleTopology) O ell n x ≫ f =
      coefficientConstantSection (J := T.smallEtaleTopology) O ell n x ≫ g) : f = g := by
  apply Sheaf.hom_ext
  apply (cancel_epi
    (sheafifyComposeIso T.smallEtaleTopology (CategoryTheory.forget CommRingCat.{u + 1})
      ((Functor.const T.Etaleᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).hom).1
  apply sheafify_hom_ext T.smallEtaleTopology _ _ N.property
  simp only [← Category.assoc, sheafComposeIso_hom_fac]
  apply NatTrans.ext
  funext U
  ext x
  have hx := congrArg
    ((sheafificationAdjunction T.smallEtaleTopology (Type (u + 1))).homEquiv _ _) (h x)
  simp only [Adjunction.homEquiv_naturality_right, coefficientConstantSection,
    Equiv.apply_symm_apply] at hx
  exact congrArg (fun k ↦ k.app U PUnit.unit) hx

private theorem constantSection_map
    {T : Scheme.{u}} {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    {ell : O} {mu : O'} {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (n : ℕ)
    (x : O ⧸ (Ideal.span ({ell} : Set O)) ^ (index n + 1)) :
    coefficientConstantSection (J := T.smallEtaleTopology) O ell (index n) x ≫
        (sheafCompose T.smallEtaleTopology
          (CategoryTheory.forget CommRingCat.{u + 1})).map (a.sheaf T n) =
      coefficientConstantSection (J := T.smallEtaleTopology) O' mu n (a.ring n x) := by
  apply ((sheafificationAdjunction T.smallEtaleTopology (Type (u + 1))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [coefficientConstantSection, Equiv.apply_symm_apply]
  ext U t
  change (sheafifyMap T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).map (CommRingCat.ofHom (a.ring n)))).app U
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (index n + 1))))).app U x) =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (CommRingCat.of (O' ⧸ (Ideal.span ({mu} : Set O')) ^ (n + 1))))).app U (a.ring n x)
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).map (CommRingCat.ofHom (a.ring n)))) U) x).symm

private theorem constantRing_square
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {T S : Scheme.{u}} {g : T ⟶ S}
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g) (n : ℕ) :
    (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology
          (CategoryTheory.forget CommRingCat.{u + 1})).map (a.sheaf S n)) ≫
        (B.lift n).ringUnderlying.hom =
      (A.lift (index n)).ringUnderlying.hom ≫
        (sheafCompose T.smallEtaleTopology
          (CategoryTheory.forget CommRingCat.{u + 1})).map (a.sheaf T n) := by
  apply ((strictEtaleSetAdjunction g).homEquiv _ _).injective
  apply coefficientConstantSection_hom_ext (index n)
  intro x
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  apply ((strictEtaleSetAdjunction g).homEquiv _ _).congr_arg
  change (Scheme.etaleSetPullback g).map
      (coefficientConstantSection (J := S.smallEtaleTopology) O ell (index n) x) ≫
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology
          (CategoryTheory.forget CommRingCat.{u + 1})).map (a.sheaf S n)) ≫
      (B.lift n).ringUnderlying.hom =
    (Scheme.etaleSetPullback g).map
      (coefficientConstantSection (J := S.smallEtaleTopology) O ell (index n) x) ≫
      (A.lift (index n)).ringUnderlying.hom ≫
      (sheafCompose T.smallEtaleTopology
        (CategoryTheory.forget CommRingCat.{u + 1})).map (a.sheaf T n)
  rw [← Category.assoc, ← Functor.map_comp, constantSection_map, B.constants,
    ← Category.assoc, A.constants, Category.assoc, constantSection_map]
  have hterminal : IsTerminal
      ((constantSheaf T.smallEtaleTopology (Type (u + 1))).obj PUnit) :=
    Types.isTerminalPUnit.isTerminalObj (constantSheaf T.smallEtaleTopology (Type (u + 1))) _
  rw [hterminal.hom_ext B.singleton.hom A.singleton.hom]

attribute [local irreducible] siteCoefficientTensorAdj

private theorem insertionUnderlying
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n : ℕ)
    (M : strictEtaleLevel T O ell (index n)) :
    (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf T n) M) =
      (coefficientUnderlying (J := T.smallEtaleTopology) O ell (index n)).map
        ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)).unit.app M) := by
  dsimp only [siteTensorUnitUnderlying, siteScalarUnderlyingIso, Iso.refl_hom,
    NatTrans.id_app]
  exact congrArg
    ((sheafCompose T.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).map)
    (Category.comp_id _)

set_option maxHeartbeats 1000000 in
-- Keep tensor insertions behind their public underlying-sheaf API.
/-- The supplied geometric lifts commute with scalar extension at one coefficient level,
with the actual tensor-insertion normalization.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03EL; Zheng Construction 4.1.
(blueprint: lem-pur-strict-etale-finite-ordinary-inverse-transport).

Proof: maps from the underlying constant quotient ring sheaf are determined by
precomposition with all its constant sections, by the constant/sheafification
adjunction. The sheaf map a.sheaf carries each such section to the section of
its image under a.ring. Apply the set inverse-image adjunction to the desired
ring square and test its transpose on these sections. The constants equations
of A and B identify the two words; their singleton maps agree because the constant
singleton sheaf is terminal. The set inverse image is left exact. Apply the proved
independent-site scalar/inverse-image comparison theorem directly to these two
algebraic lifts, this ring square, and the actual tensor adjunctions. Its normalized
unit equation becomes the displayed insertion equation after forgetting to sets. -/
theorem strictEtaleFiniteOrdinaryInverseTransport
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {T S : Scheme.{u}} {g : T ⟶ S}
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g) (n : ℕ) :
    ∃ e : siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
        (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n),
      ∀ M : strictEtaleLevel S O ell (index n),
        (Scheme.etaleSetPullback g).map
            ((sheafCompose S.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
              (siteTensorUnitUnderlying (a.sheaf S n) M)) ≫
            (B.lift n).moduleUnderlying.inv.app
              ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) ≫
            (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map (e.hom.app M) =
          (A.lift (index n)).moduleUnderlying.inv.app M ≫
            (sheafCompose T.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
              (siteTensorUnitUnderlying (a.sheaf T n) ((A.lift (index n)).modules.obj M)) := by
  let : PreservesFiniteLimits (Scheme.etaleSetPullback g) :=
    (etaleSetInverseImage_exact g).2.2.1
  have h := SheafOfModules.ScalarIndependent.exists_scalarInverseImageIndependent
    (Scheme.etaleSetPullback g) _ (strictEtaleSetAdjunction g)
    (A.lift (index n)) (B.lift n) (a.sheaf S n) (a.sheaf T n)
    (constantRing_square a A B n)
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n))
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf S n))
    (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n))
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  intro M
  have hS := insertionUnderlying a S n M
  have hT := insertionUnderlying a T n ((A.lift (index n)).modules.obj M)
  exact (congrArg (fun z ↦ (Scheme.etaleSetPullback g).map z ≫
      (B.lift n).moduleUnderlying.inv.app
        ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) ≫
      (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map (e.hom.app M)) hS).trans
    ((he M).trans (congrArg
      (fun z ↦ (A.lift (index n)).moduleUnderlying.inv.app M ≫ z) hT.symm))

end AlgebraicGeometry
