/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalHomTransport
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalNormalizedRightAction
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedActionRealization

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

private theorem equivariant_implies_invariant
    {C : Type*} [Category C] [Abelian C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    [HasDerivedCategory C] [HasDerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra F)]
    (M N : DerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra F))
    (t : (forget F).mapDerivedCategory.obj M ⟶ (forget F).mapDerivedCategory.obj N)
    (ht : (cyclicDerivedStructure F).hom.app M ≫ t =
      F.mapDerivedCategory.map t ≫ (cyclicDerivedStructure F).hom.app N) :
    t ≫ (shiftFunctorZero (DerivedCategory C) ℤ).inv.app _ ∈
      CyclicDerivedHomInvariants F M N := by
  rw [AddMonoidHom.mem_ker]
  change _ - cyclicDerivedHomAction F M N 0 _ = 0
  rw [sub_eq_zero]
  change _ = (((cyclicDerivedStructure F).inv.app M ≫
    F.mapDerivedCategory.map (t ≫ (shiftFunctorZero (DerivedCategory C) ℤ).inv.app _)) ≫
    ((F.mapDerivedCategory.commShiftIso 0).hom.app _ ≫
      ((cyclicDerivedStructure F).hom.app N)⟦(0 : ℤ)⟧'))
  rw [F.mapDerivedCategory.commShiftIso_zero]
  simp only [AddMonoidHom.id_apply, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Category.comp_id, Functor.id_obj]
  erw [← (shiftFunctorZero (DerivedCategory C) ℤ).inv.naturality
    ((cyclicDerivedStructure F).hom.app N)]
  simp only [Functor.id_map]
  rw [← reassoc_of% ht]
  simp

private theorem transported_equivariant
    {A B : Type*} [Category A] [Category B]
    (P : A ⥤ A) (Q : B ⥤ B) (O : A ⥤ B) (beta : O ⋙ Q ≅ P ⋙ O)
    {M N : A} {K L : B} (sigma : P.obj M ⟶ M) (v : P.obj N ⟶ N)
    (theta : Q.obj K ⟶ K) (tau : Q.obj L ⟶ L)
    (c : K ⟶ O.obj M) (d : M ⟶ N) (w : O.obj N ⟶ L)
    (hc : theta ≫ c = Q.map c ≫ beta.hom.app M ≫ O.map sigma)
    (hd : sigma ≫ d = P.map d ≫ v)
    (hw : beta.hom.app N ≫ O.map v ≫ w = Q.map w ≫ tau) :
    theta ≫ (c ≫ O.map d ≫ w) = Q.map (c ≫ O.map d ≫ w) ≫ tau := by
  calc
    _ = Q.map c ≫ beta.hom.app M ≫ O.map sigma ≫ O.map d ≫ w := by
      rw [← Category.assoc theta, hc]
      simp only [Category.assoc]
    _ = Q.map c ≫ beta.hom.app M ≫ O.map (P.map d) ≫ O.map v ≫ w := by
      rw [← O.map_comp_assoc, hd]
      simp only [Functor.map_comp, Category.assoc]
    _ = Q.map c ≫ Q.map (O.map d) ≫ beta.hom.app N ≫ O.map v ≫ w := by
      have hn := beta.hom.naturality d
      change Q.map (O.map d) ≫ beta.hom.app N =
        beta.hom.app M ≫ O.map (P.map d) at hn
      simpa only [Category.assoc] using
        congrArg (fun k ↦ Q.map c ≫ k ≫ O.map v ≫ w) hn.symm
    _ = _ := by
      rw [hw]
      simp only [Functor.map_comp, Category.assoc]

/-- Choose the normalized comparison together with its invariant ordinary counit carriers.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final sentence.
Proof: the normalized ordinary right-action construction gives a bounded constructible
ordinary exceptional object with an invertible Frobenius action and an equivariant counit.
Realize this action by the cyclic derived action realization theorem. Isomorphism closure
puts the resulting object in the native Weil category. Transport the normalized counit
along the action-compatible isomorphism. Naturality of the Frobenius exchange and its
counit equation prove equivariance; zero-shift coherence gives the invariant condition.
(blueprint: lem-sf-native-exceptional-ordinary-counit-carrier). -/
theorem native_exceptional_ordinary_counit_carrier (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀)) :
    ∃ a : nativeShriek D l f₀ ⋙ VY.functor ≅
        VX.functor ⋙ (S.ring.operation c .closed).F,
      ∀ L : W D l Y, ∃ (H : W D l X)
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
  obtain ⟨a, beta, hbeta, hright⟩ :=
    native_exceptional_normalized_right_action D l R X Y VX VY f₀ S c
  refine ⟨a, ?_⟩
  intro L
  obtain ⟨N, v, w, hN, hw, hreal⟩ := hright L
  let P := WeilSheaf.frobeniusPullback D.k₀ l X.base.left
  let Q := WeilSheaf.frobeniusPullback D.k₀ l Y.base.left
  let O := counitOrdinaryShriek D l f₀
  obtain ⟨M, d, hd, _, _⟩ := exists_cyclicDerivedActionRealization P N hN.1 v
  change (cyclicDerivedStructure P).hom.app M ≫ d.hom =
    P.mapDerivedCategory.map d.hom ≫ v.hom at hd
  have hM : WeilComplex.objectProperty D.k₀ l X.base.left M := by
    apply (WeilComplex.objectProperty_iff M).mpr
    exact (ProEtale.DerivedCategory.boundedConstructibleAdic l
      X.base.hom.geometricFiber).prop_of_iso d.symm hN
  let H : W D l X := ⟨M, hM⟩
  let t := (counitForgetComparison D l f₀).hom.app H ≫ O.map d.hom ≫ w
  obtain ⟨e, he⟩ := hreal H d
  refine ⟨H, e, t, he, ?_⟩
  apply equivariant_implies_invariant Q
  change (cyclicDerivedStructure Q).hom.app ((nativeShriek D l f₀).obj H).obj ≫
    t = Q.mapDerivedCategory.map t ≫ (cyclicDerivedStructure Q).hom.app L.obj
  exact transported_equivariant P.mapDerivedCategory Q.mapDerivedCategory O beta
    ((cyclicDerivedStructure P).hom.app M) v.hom
    ((cyclicDerivedStructure Q).hom.app ((nativeShriek D l f₀).obj H).obj)
    ((cyclicDerivedStructure Q).hom.app L.obj)
    ((counitForgetComparison D l f₀).hom.app H) d.hom w (hbeta H) hd hw

end WeilConjectures.NativeExceptionalForgetful
