/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Topology.KrullDimension
public import Sheaf.SixFunctors.ClassicalDefinition
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all Sheaf.AlgebraicGeometry.ProEtaleClassicalDirectImagePreservation
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
import Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts

/-!
# Uniform amplitude of finite-coefficient proper direct image

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, "Etale statements" and "Transfer";
Stacks Project, Tags 095U, 0D6J, 07KC, 0H72 and 0F0D
(blueprint: lem-sfb-finite-proper-classical-amplitude).

Both coefficient presentations use the canonical lift `ULift.{u + 1, u} A`.
The pro-etale category is the ordinary constant-ring module derived category;
its classicality predicate concerns all cohomology sheaves. Preservation of
products and coproducts means preservation of the canonical limiting cones and
colimiting cocones, hence of their projections and coprojections.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] intrinsicHasDerivedCategory

private noncomputable instance intrinsicGroth (X : Scheme.{u}) (A : Type u) [CommRing A] :
    IsGrothendieckAbelian.{u + 1}
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    (Scheme.ProEt.topology X) (Scheme.proEtaleConstantRing X A)).1

private noncomputable def constantAdjunction
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.proEtaleConstantRingPullback A f ⊣ Scheme.proEtaleConstantModuleDirectImage f A := by
  have he : Scheme.proEtaleRingDirectImageMap f (Scheme.proEtaleConstantRing Y A)
      (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRingComparison f A) =
        Scheme.proEtaleCoefficientDirectImageMap f A := by
    exact Equiv.apply_symm_apply
      ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _) _
  have hd : Scheme.proEtaleConstantRingPushforward A f =
      Scheme.proEtaleConstantModuleDirectImage f A := by
    unfold Scheme.proEtaleConstantRingPushforward Scheme.proEtaleRingModuleDirectImage
    rw [he]
    rfl
  exact (Scheme.proEtaleConstantRingAdjunction A f).ofNatIsoRight (eqToIso hd)

private theorem total_isGE
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : DerivedCategory C) (a : ℤ) [K.IsGE a] :
    (F.rightDerivedFunctor.obj K).IsGE a := by
  let Kp : DerivedCategory.Plus C := ⟨K, ⟨a, inferInstance⟩⟩
  have : Kp.IsGE a := ⟨(show K.IsGE a from inferInstance).1⟩
  apply (DerivedCategory.isGE_iff _ a).2
  intro q hq
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE Kp a hq).of_iso
    ((DerivedCategory.homologyFunctor D q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app Kp)).symm

private theorem fiber_bound
    {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ℕ)
    (hb : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞)) :
    ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞) := by
  intro y
  obtain ⟨i, _, _⟩ := baseChange_fiber f (Over.mk (𝟙 Y)) y
  have i' : f.fiber y ≅ (pullback.snd f (𝟙 Y)).fiber y := by
    change pullback f (Y.fromSpecResidueField y) ≅ _
    simpa using i
  exact (IsHomeomorph.topologicalKrullDim_eq _ i'.hom.homeomorph.isHomeomorph).le.trans
    (hb Y (𝟙 Y) y)

private theorem etale_vanishing
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (hb : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (q : ℤ) (hq : 2 * (e : ℤ) < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let B := ULift.{u + 1, u} A
  let U := sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} B)
    AddCommGrpCat.{u + 1})
  have htors : (U.obj F).IsTorsion := by
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro V x
    exact (isAddTorsion_of_finite : IsAddTorsion B).module_of_torsion B (F.obj.obj V) x
  have hz := Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le f e hb
    (U.obj F) ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mpr htors) q hq
  obtain ⟨i⟩ := Etale.nonempty_higherDirectImage_forget_iso B f q F
  let V := sheafCompose Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} B)
    AddCommGrpCat.{u + 1})
  have hzero := hz.of_iso i
  apply (IsZero.iff_id_eq_zero _).mpr
  apply V.map_injective
  rw [V.map_id, V.map_zero]
  exact hzero.eq_of_src _ _

private theorem heart_upper
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (hb : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (H : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (hH : IsClassicalModuleSheaf H) :
    ((Scheme.proEtaleConstantDerivedDirectImage f A).obj
      ((DerivedCategory.singleFunctor _ 0).obj H)).IsLE (2 * (e : ℤ)) := by
  let B := ULift.{u + 1, u} A
  let RX := intrinsicRestriction X A
  let RY := intrinsicRestriction Y A
  let F := RX.obj H
  have hF : IsClassical ((sheafCompose (Scheme.ProEt.topology X)
      (forget (ModuleCat.{u + 1} B))).obj F) := hH
  obtain ⟨adj, _, _, _, _, hc⟩ := proEtaleClassicalSheavesModules X B
  obtain ⟨E, ⟨i⟩⟩ := (hc F).mp hF
  let C := comparisonUpperStar (ModuleCat.{u + 1} B) X
  let D := comparisonUpperStar (ModuleCat.{u + 1} B) Y
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj E
  let V := lowerStar (ModuleCat.{u + 1} B) f
  let T := (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f).obj K
  have hT : T.obj.IsLE (2 * (e : ℤ)) :=
    (DerivedCategory.isLE_iff _ _).mpr (etale_vanishing A f e hb E)
  have hm : IsIso (comparisonDirectImageCanonicalMate B f) :=
    (directImageComparison A f).1 inferInstance inferInstance
  let j : RX.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj H) ≅
      (C.mapDerivedCategoryPlus.obj K).obj :=
    (RX.mapDerivedCategorySingleFunctor 0).app H ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso i.symm ≪≫
      (DerivedCategory.Plus.ι.mapIso ((C.mapDerivedCategoryPlusSingleFunctor 0).app E)).symm
  let c : RY.mapDerivedCategory.obj
      ((Scheme.proEtaleConstantDerivedDirectImage f A).obj
        ((DerivedCategory.singleFunctor _ 0).obj H)) ≅
      D.mapDerivedCategory.obj T.obj :=
    (restrictionDerivedDirectImageIso f A).app _ ≪≫
      V.rightDerivedFunctor.mapIso j ≪≫
      (V.rightDerivedFunctorPlusCompatibility.app (C.mapDerivedCategoryPlus.obj K)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso ((asIso (comparisonDirectImageCanonicalMate B f)).app K).symm
  have hd : (D.mapDerivedCategory.obj T.obj).IsLE (2 * (e : ℤ)) :=
    D.isLE_mapDerivedCategory_obj T.obj _
  have hout := DerivedCategory.TStructure.t.isLE_of_iso c.symm (2 * (e : ℤ))
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro q hq
  exact RY.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.isLE_iff _ _).mp hout q hq)

private theorem completeTriangle
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] [HasCountableProducts C]
    [HasExactLimitsOfShape (Discrete ℕ) C]
    (K : DerivedCategory C)
    [HasProduct (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)] :
    ∃ δ : (∏ᶜ (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) ⟶
        K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (DerivedCategory.TStructure.t.natTransTruncGEOfLE
          (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app K) K
        (Pi.lift (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)) δ := by
  let Z (n : ℕ) := (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K
  obtain ⟨δ, hδ⟩ := (DerivedCategory.isHomotopyLimit_truncGECone K).exists_distTriang
    (productIsProduct Z)
  have hπ : Fan.IsLimit.lift (productIsProduct Z)
      (fun n ↦ K.truncGECone.π.app (Opposite.op n)) =
        Pi.lift (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) := by
    apply Pi.hom_ext
    intro n
    rw [Pi.lift_π]
    exact Fan.IsLimit.fac (productIsProduct Z) _ n
  have hs : CategoryTheory.Pretriangulated.towerShift
      (F := K.truncGETower) (productIsProduct Z) =
        towerProductShift (fun n : ℕ ↦ (DerivedCategory.TStructure.t.natTransTruncGEOfLE
          (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app K) := by
    apply Pi.hom_ext
    intro n
    simp only [CategoryTheory.Pretriangulated.towerShift, towerProductShift, Pi.lift_π]
    change Fan.IsLimit.lift (productIsProduct Z) _ ≫
      (Fan.mk _ (Pi.π Z)).proj n = _
    rw [Fan.IsLimit.fac]
    rfl
  refine ⟨δ, ?_⟩
  simp only [hπ, hs, Fan.mk_pt, Z] at hδ
  unfold IsDerivedLimitTriangle towerTransitionEndomorphism
  convert hδ using 1
  congr 1

/-- Total proper direct image has lower amplitude zero on every complex and upper
amplitude `2e` on complexes with classical cohomology, including those unbounded below.
It is triangulated, commutes with integer shifts and preserves countable products.
The etale higher images vanish above `2e`, and the total etale direct image preserves
all existing small ambient coproducts by their canonical comparison.

Source: blueprint main-20261015, sk-prop-ctf-finite-proper-localizing.proof.md,
"Etale statements" and "Transfer"; Stacks Tags 095U, 0D6J, 07KC, 0H72 and 0F0D
(blueprint: lem-sfb-finite-proper-classical-amplitude).

Proof:
1. The Grothendieck module categories have K-injective resolutions. The canonical
   module pullback/direct-image adjunction gives a derived adjunction. Its right
   adjoint preserves products, and the generic K-injective construction gives
   triangulatedness, shift compatibility, and existence of derived products.
2. A complex bounded below belongs to the bounded-below derived category. Negative
   vanishing there, transported by total/bounded-below compatibility, gives the
   same lower bound for total direct image.
3. Every module over the finite ring has torsion underlying additive group.
   The identity base change supplies the fibre bound for the original morphism.
   Proper torsion vanishing and the higher-direct-image forgetful comparison give
   the etale module bound in every degree above `2e`; faithful additive forgetting
   reflects the zero object.
4. Restriction along constant scalar sections is an exact equivalence from the
   intrinsic module category to fixed-ring module sheaves, compatible with derived
   direct image. A classical sheaf is the comparison pullback of an etale module
   sheaf. The bounded-below direct-image comparison, exactness of comparison
   pullback and step 3 give upper bound `2e` on its degree-zero single complex.
   The restriction equivalence reflects this cohomological bound.
5. Pro-etale module products are exact, hence the ordinary derived category is
   left complete. Express its canonical homotopy-limit triangle with the chosen
   product by the product universal property. Apply the generic left-complete
   heart upper-bound theorem to the class of classical sheaves and the bound in
   step 4. It combines finite Postnikov induction with eventual invertibility of
   the cohomology tower, giving the sharp bound `b + 2e` without a lower bound.
6. Properness supplies qcqs. The finite-cohomological-dimension coproduct
   criterion, with `c = 2e` and step 3, gives preservation of every small etale
   coproduct. All assertions concern canonical limit/colimit cones. -/
theorem finiteProper_classical_amplitude
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (e : ℕ)
    (_hbound : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞)) :
    Nonempty ((Scheme.proEtaleConstantDerivedDirectImage f A).CommShift ℤ) ∧
    (Scheme.proEtaleConstantDerivedDirectImage f A).IsTriangulated ∧
    Nonempty (HasCountableProducts (Scheme.proEtaleDerivedCategory X A)) ∧
    Nonempty (HasCountableProducts (Scheme.proEtaleDerivedCategory Y A)) ∧
    (∀ (I : Type w) [Countable I], PreservesLimitsOfShape (Discrete I)
      (Scheme.proEtaleConstantDerivedDirectImage f A)) ∧
    (∀ (a : ℤ) (L : Scheme.proEtaleDerivedCategory X A), L.IsGE a →
      ((Scheme.proEtaleConstantDerivedDirectImage f A).obj L).IsGE a) ∧
    (∀ (b : ℤ) (L : Scheme.proEtaleDerivedCategory X A),
      IsClassicalModuleComplex L → L.IsLE b →
      ((Scheme.proEtaleConstantDerivedDirectImage f A).obj L).IsLE (b + 2 * (e : ℤ))) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (q : ℤ), 2 * (e : ℤ) < q →
      IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) ∧
    (∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)) := by
  have hprod : ∀ (I : Type w) [Countable I], PreservesLimitsOfShape (Discrete I)
      (Scheme.proEtaleConstantDerivedDirectImage f A) := by
    intro I _
    let adj := (constantAdjunction A f).mapDerivedCategoryRightDerivedAdjunction
    have := adj.rightAdjoint_preservesLimits
    infer_instance
  have hv := etale_vanishing A f e (fiber_bound f e _hbound)
  refine ⟨⟨inferInstance⟩, inferInstance, ⟨?_⟩, ⟨?_⟩, hprod, ?_, ?_, hv, ?_⟩
  · exact ⟨fun J _ ↦ inferInstance⟩
  · exact ⟨fun J _ ↦ inferInstance⟩
  · intro a L hL
    have := hL
    exact total_isGE (Scheme.proEtaleConstantModuleDirectImage f A) L a
  · intro b L hc hL
    have hAX : CountableAB4Star
        (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
      ⟨fun I _ ↦ Scheme.ProEt.products_exact.{u, 0, 0} X _ I⟩
    have hAY : CountableAB4Star
        (Scheme.proEtaleRingModules Y (Scheme.proEtaleConstantRing Y A)) :=
      ⟨fun I _ ↦ Scheme.ProEt.products_exact.{u, 0, 0} Y _ I⟩
    have hprod0 : ∀ (I : Type) [Countable I], PreservesLimitsOfShape (Discrete I)
        (Scheme.proEtaleConstantDerivedDirectImage f A) := by
      intro I _
      let adj := (constantAdjunction A f).mapDerivedCategoryRightDerivedAdjunction
      have := adj.rightAdjoint_preservesLimits
      infer_instance
    apply (DerivedCategory.isLE_iff _ _).mpr
    refine @DerivedCategory.upperBound_of_heart_of_leftComplete
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) _ _
      (HasDerivedCategory.standard _)
      (Scheme.proEtaleRingModules Y (Scheme.proEtaleConstantRing Y A)) _ _
      (HasDerivedCategory.standard _) _ hAX _ hAY
      (fun K _ ↦ completeTriangle K) (Scheme.proEtaleConstantDerivedDirectImage f A)
      _ _ hprod0 {H | IsClassicalModuleSheaf H} (2 * (e : ℤ)) ?_ b L hc
      ((DerivedCategory.isLE_iff _ _).mp hL)
    intro H hH q hq
    exact (DerivedCategory.isLE_iff _ _).mp
      (heart_upper A f e (fiber_bound f e _hbound) H hH) q hq
  · apply Etale.rightDerivedLowerStar_preservesCoproducts_of_finite_dimension
      (ULift.{u + 1, u} A) f (2 * e)
    intro M p hp
    let F := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
    exact (hv M p (by exact_mod_cast hp)).of_iso
      (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso M p).symm

end AlgebraicGeometry.ProEtale
