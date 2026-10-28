/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalHomTransport
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Ordinary exceptional counit carrier

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, carrier and invariance steps.
(blueprint: lem-sf-native-exceptional-ordinary-counit-carrier).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

-- The matrix obstruction below takes place in any preadditive category. For
-- Spec(F_(q^2)) over Spec(F_q), the two geometric components give exactly this
-- biproduct, and phi and psi are the two components of the Frobenius structure.
-- The upper triangular comparison is natural in these fixed pairs.
private def triangularComparison {C : Type*} [Category C] [Preadditive C]
    {A B : C} [HasBinaryBiproduct A B] (phi : B ⟶ A) : A ⊞ B ≅ A ⊞ B where
  hom := biprod.desc biprod.inl (phi ≫ biprod.inl + biprod.inr)
  inv := biprod.desc biprod.inl (-phi ≫ biprod.inl + biprod.inr)
  hom_inv_id := by
    apply biprod.hom_ext' <;> simp [Preadditive.add_comp, Category.assoc]
  inv_hom_id := by
    apply biprod.hom_ext' <;>
      simp [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc]

-- This is precisely the naturality square for the first component of a map
-- of pairs with swapping action; the second component is not needed here.
private theorem triangularComparison_naturality
    {C : Type*} [Category C] [Preadditive C]
    {A B A' B' : C} [HasBinaryBiproduct A B] [HasBinaryBiproduct A' B']
    (phi : B ⟶ A) (phi' : B' ⟶ A') (f : A ⟶ A') (g : B ⟶ B')
    (h : g ≫ phi' = phi ≫ f) :
    biprod.map f g ≫ (triangularComparison phi').hom =
      (triangularComparison phi).hom ≫ biprod.map f g := by
  apply biprod.hom_ext'
  · simp [triangularComparison]
  · simpa [triangularComparison, Preadditive.add_comp, Category.assoc] using
      congrArg (fun k ↦ k ≫ (biprod.inl : A' ⟶ A' ⊞ B')) h

-- Invertible components give an actual invertible Frobenius action on the sum.
private def swappingAction {C : Type*} [Category C] [Preadditive C]
    {A B : C} [HasBinaryBiproduct A B] (phi : B ≅ A) (psi : A ≅ B) :
    A ⊞ B ≅ A ⊞ B where
  hom := biprod.desc (psi.hom ≫ biprod.inr) (phi.hom ≫ biprod.inl)
  inv := biprod.desc (phi.inv ≫ biprod.inr) (psi.inv ≫ biprod.inl)
  hom_inv_id := by apply biprod.hom_ext' <;> simp [Category.assoc]
  inv_hom_id := by apply biprod.hom_ext' <;> simp [Category.assoc]

-- With target Frobenius the identity, invariance is theta >> t = t.
-- For the triangular comparison and an invertible second component eB, this
-- forces the target to be zero. In particular the nonzero coefficient unit
-- cannot have a carrier for this comparison.
private theorem triangular_counit_obstruction {C : Type*} [Category C] [Preadditive C]
    {A B L : C} [HasBinaryBiproduct A B] (phi : B ⟶ A) (psi : A ⟶ B)
    (eA : A ≅ L) (eB : B ≅ L)
    (hinv : biprod.desc (psi ≫ biprod.inr) (phi ≫ biprod.inl) ≫
        (triangularComparison phi).hom ≫ biprod.desc eA.hom eB.hom =
      (triangularComparison phi).hom ≫ biprod.desc eA.hom eB.hom) : IsZero L := by
  have h := congrArg (fun t ↦ (biprod.inr : B ⟶ A ⊞ B) ≫ t) hinv
  have hcancel : phi ≫ eA.hom = phi ≫ eA.hom + eB.hom := by
    simpa [triangularComparison, Preadditive.add_comp, Category.assoc] using h
  have hz : eB.hom = 0 := by
    apply add_left_cancel (a := phi ≫ eA.hom)
    simpa only [add_zero] using hcancel.symm
  apply (IsZero.iff_id_eq_zero L).mpr
  calc
    𝟙 L = eB.inv ≫ eB.hom := eB.inv_hom_id.symm
    _ = 0 := by rw [hz, comp_zero]

-- The zero-shift condition in the item really is ordinary equivariance.
private theorem invariant_implies_equivariant
    {C : Type*} [Category C] [Abelian C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    [HasDerivedCategory C] [HasDerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra F)]
    (M N : DerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra F))
    (t : (forget F).mapDerivedCategory.obj M ⟶ (forget F).mapDerivedCategory.obj N)
    (ht : t ≫ (shiftFunctorZero (DerivedCategory C) ℤ).inv.app _ ∈
      CyclicDerivedHomInvariants F M N) :
    (cyclicDerivedStructure F).hom.app M ≫ t =
      F.mapDerivedCategory.map t ≫ (cyclicDerivedStructure F).hom.app N := by
  rw [AddMonoidHom.mem_ker] at ht
  change _ - cyclicDerivedHomAction F M N 0 _ = 0 at ht
  rw [sub_eq_zero] at ht
  change _ = (((cyclicDerivedStructure F).inv.app M ≫
    F.mapDerivedCategory.map (t ≫ (shiftFunctorZero (DerivedCategory C) ℤ).inv.app _)) ≫
    ((F.mapDerivedCategory.commShiftIso 0).hom.app _ ≫
      ((cyclicDerivedStructure F).hom.app N)⟦(0 : ℤ)⟧')) at ht
  rw [F.mapDerivedCategory.commShiftIso_zero] at ht
  simp only [Functor.CommShift.isoZero_hom_app, Functor.map_comp, Category.assoc] at ht
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app] at ht
  erw [← (shiftFunctorZero (DerivedCategory C) ℤ).inv.naturality
    ((cyclicDerivedStructure F).hom.app N)] at ht
  simp only [Functor.id_map] at ht
  have heq : t = (cyclicDerivedStructure F).inv.app M ≫
      F.mapDerivedCategory.map t ≫ (cyclicDerivedStructure F).hom.app N := by
    apply (cancel_mono ((shiftFunctorZero (DerivedCategory C) ℤ).inv.app _)).mp
    simpa only [AddMonoidHom.id_apply, Functor.id_obj, Category.comp_id, Category.assoc]
      using ht
  calc
    _ = (cyclicDerivedStructure F).hom.app M ≫
        ((cyclicDerivedStructure F).inv.app M ≫ F.mapDerivedCategory.map t ≫
          (cyclicDerivedStructure F).hom.app N) := congrArg (_ ≫ ·) heq
    _ = _ := by simp

-- STATEMENT-DISPUTED: a is arbitrary, but a triangular natural automorphism of
-- the ordinary sum comparison for Spec(F_(q^2)) -> Spec(F_q) has no invariant
-- counit carrier for the nonzero constant unit. See the delivery report and the checked
-- triangular_counit_obstruction above. The normalized scalar comparison in the
-- source cannot be replaced by an arbitrary natural comparison isomorphism.
/--
The ordinary scalar counit construction supplies its carrier and its invariant
zero-shift equation for a fixed comparison and a fixed target object.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-
adjunction sentence.  Choose the scalar-normalized Frobenius mate, realize its
invertible action by a bounded fixed-pair complex, and transport the ordinary
adjunction counit through the comparison and the action-compatible isomorphism.
The mate-counit identity gives the transported-arrow equation; the zero-shift
coherence gives the displayed invariant condition.  This is the carrier part
of the ordinary witness and does not assert graded Hom bijectivity.
(blueprint: lem-sf-native-exceptional-ordinary-counit-carrier).
-/
theorem native_exceptional_ordinary_counit_carrier (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (a : nativeShriek D l f₀ ⋙ VY.functor ≅
      VX.functor ⋙ (S.ring.operation c .closed).F)
    (L : W D l Y) :
    ∃ (H : W D l X)
      (e : VX.functor.obj H ≅ (S.ring.operation c .closed).G.obj (VY.functor.obj L))
      (t : WeilComplex.forget.obj ((nativeShriek D l f₀).obj H) ⟶
        WeilComplex.forget.obj L),
      ((ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ⋙
        sectionDerived l (geometric D Y).base.left
          (R.data (geometric D Y)).realization).map t =
        VY.realization.inv.app ((nativeShriek D l f₀).obj H) ≫
          (rho D l R Y).map (a.hom.app H ≫ (S.ring.operation c .closed).F.map e.hom ≫
            (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L)) ≫
          VY.realization.hom.app L ∧
      (t ≫ (shiftFunctorZero _ ℤ).inv.app (WeilComplex.forget.obj L)) ∈
        CyclicDerivedHomInvariants (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
          ((nativeShriek D l f₀).obj H).obj L.obj := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
