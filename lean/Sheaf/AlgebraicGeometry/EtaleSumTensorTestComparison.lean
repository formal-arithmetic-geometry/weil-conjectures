/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.Additive


/-! # Acyclic tensor tests for étale sum extension

Source: Stacks Project, More on Étale Cohomology, Tag 0GKF, and the unbounded
totalization expansion of lem-pur-etale-sum-tensor-totalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Sum extension on modules over the constant commutative ring sheaf, constructed
by restriction to constant scalars and the published realization functor.
Source: Stacks Tags 093I, 03CV, and 0GKF (blueprint: lem-pur-etale-sum-tensor-test). -/
def etaleSumTensorTestExtension {U X : Scheme.{u}} (f : U ⟶ X) (hf : Etale f)
    (A : Type (u + 1)) [CommRing A] :
    SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))) ⥤
    SheafOfModules.{u + 1} ((sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))) :=
  SheafOfModules.pushforward.{u + 1} (F := 𝟭 U.Etale)
      (constantModuleHomRingIso U.smallEtaleTopology A).hom ⋙
    etaleConstantModuleRestrictionFunctor U A ⋙
    Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f hf ⋙
    etaleConstantModuleFunctor X A ⋙
    SheafOfModules.pushforward.{u + 1} (F := 𝟭 X.Etale)
      (constantModuleHomRingIso X.smallEtaleTopology A).inv

set_option backward.isDefEq.respectTransparency false in
private theorem constantRingTransport_equivalence (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    (SheafOfModules.pushforward.{u + 1} (J := T.smallEtaleTopology)
      (K := T.smallEtaleTopology) (F := 𝟭 T.Etale)
      (S := (constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of A))
      (R := (sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)))
      (constantModuleHomRingIso T.smallEtaleTopology A).hom).IsEquivalence ∧
    (SheafOfModules.pushforward.{u + 1} (J := T.smallEtaleTopology)
      (K := T.smallEtaleTopology) (F := 𝟭 T.Etale)
      (R := (constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of A))
      (S := (sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)))
      (constantModuleHomRingIso T.smallEtaleTopology A).inv).IsEquivalence := by
  let : (CategoryTheory.Equivalence.refl (C := T.Etale)).functor.IsContinuous
      T.smallEtaleTopology T.smallEtaleTopology := by
    change (𝟭 T.Etale).IsContinuous T.smallEtaleTopology T.smallEtaleTopology
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := T.Etale)).inverse.IsContinuous
      T.smallEtaleTopology T.smallEtaleTopology := by
    change (𝟭 T.Etale).IsContinuous T.smallEtaleTopology T.smallEtaleTopology
    infer_instance
  let eT := SheafOfModules.pushforwardPushforwardEquivalence.{u + 1}
    (CategoryTheory.Equivalence.refl (C := T.Etale))
    (constantModuleHomRingIso T.smallEtaleTopology A).hom
    (constantModuleHomRingIso T.smallEtaleTopology A).inv (by
      ext W : 2
      dsimp [CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.counit]
      rw [CategoryTheory.Functor.map_id]
      change 𝟙 _ = ((constantModuleHomRingIso T.smallEtaleTopology A).inv ≫
        (constantModuleHomRingIso T.smallEtaleTopology A).hom).hom.app W
      rw [Iso.inv_hom_id]
      rfl) (by
      ext W : 2
      dsimp [CategoryTheory.Equivalence.refl, CategoryTheory.Equivalence.unit]
      rw [CategoryTheory.Functor.map_id]
      change ((constantModuleHomRingIso T.smallEtaleTopology A).hom ≫
        (constantModuleHomRingIso T.smallEtaleTopology A).inv).hom.app W = 𝟙 _
      rw [Iso.hom_inv_id]
      rfl)
  exact ⟨eT.isEquivalence_functor, eT.isEquivalence_inverse⟩

set_option backward.isDefEq.respectTransparency false in
/-- The transported sum extension is exact. Source: Stacks Tag 0GKF and the
constant-scalar equivalence (blueprint: lem-pur-etale-sum-tensor-test).
The two ring transports are equivalences. Restriction is inverse to the published
constant-scalar equivalence, and the middle sum extension is exact. -/
theorem etaleSumTensorTestExtension_exact {U X : Scheme.{u}} (f : U ⟶ X) (hf : Etale f)
    (A : Type (u + 1)) [CommRing A] :
    exactFunctor _ _ (etaleSumTensorTestExtension f hf A)   := by
  let := etaleConstantModuleFunctor_isEquivalence X A
  let : (etaleConstantModuleRestrictionFunctor U A).IsEquivalence :=
    Functor.IsEquivalence.mk' (etaleConstantModuleFunctor U A)
      (etaleConstantModuleCounitIso U A).symm (etaleConstantModuleUnitIso U A).symm
  let := (constantRingTransport_equivalence U A).1
  let := (constantRingTransport_equivalence X A).2
  let := (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f hf).isLeftAdjoint
  apply (exactFunctor_iff _).mpr
  constructor <;> dsimp only [etaleSumTensorTestExtension] <;> infer_instance

/-- Apply the exact transported extension degreewise.
Source: Stacks Tag 0GKF (blueprint: lem-pur-etale-sum-tensor-test). -/
def etaleSumTensorTestComplexExtension {U X : Scheme.{u}} (f : U ⟶ X) (hf : Etale f)
    (A : Type (u + 1)) [CommRing A] :=
  let h := etaleSumTensorTestExtension_exact f hf A
  let : PreservesFiniteLimits (etaleSumTensorTestExtension f hf A) := h.1
  let := Functor.additive_of_preserves_binary_products (etaleSumTensorTestExtension f hf A)
  (etaleSumTensorTestExtension f hf A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Exact transported sum extension preserves acyclicity.
Source: Stacks Tag 0GKF (blueprint: lem-pur-etale-sum-tensor-test).
In each degree apply the exact functor to the exact short complex. -/
theorem etaleSumTensorTestComplexExtension_acyclic {U X : Scheme.{u}}
    (f : U ⟶ X) (hf : Etale f) (A : Type (u + 1)) [CommRing A]
    (K : CochainComplex (SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)))) ℤ)
    (hK : K.Acyclic) : ((etaleSumTensorTestComplexExtension f hf A).obj K).Acyclic := by
  have h := etaleSumTensorTestExtension_exact f hf A
  let : PreservesFiniteLimits (etaleSumTensorTestExtension f hf A) := h.1
  let : PreservesFiniteColimits (etaleSumTensorTestExtension f hf A) := h.2
  let := Functor.additive_of_preserves_binary_products (etaleSumTensorTestExtension f hf A)
  intro n
  exact (hK n).map (etaleSumTensorTestExtension f hf A)

/-- Modules over the canonical constant commutative ring sheaf.
Source: Stacks Tags 093I and 03CV (blueprint: lem-pur-etale-sum-tensor-test). -/
abbrev EtaleSumTensorTestModule (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  SheafOfModules.{u + 1} ((sheafCompose T.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)))

/-- The canonical realization of constant-coefficient module sheaves.
Source: Stacks Tags 093I and 03CV (blueprint: lem-pur-etale-sum-tensor-test). -/
def etaleSumTensorTestRealization (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ EtaleSumTensorTestModule T A :=
  etaleConstantModuleFunctor T A ⋙
    SheafOfModules.pushforward.{u + 1} (F := 𝟭 T.Etale)
      (constantModuleHomRingIso T.smallEtaleTopology A).inv

/-- The canonical realization is an equivalence: both its constant-scalar functor and
its transport along a ring isomorphism are equivalences.
Source: Stacks Tags 093I and 03CV (blueprint: lem-pur-etale-sum-tensor-test). -/
theorem etaleSumTensorTestRealization_isEquivalence (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    (etaleSumTensorTestRealization T A).IsEquivalence := by
  let := etaleConstantModuleFunctor_isEquivalence T A
  let := (constantRingTransport_equivalence T A).2
  dsimp only [etaleSumTensorTestRealization]
  infer_instance

/-- Realization applied degreewise to an unbounded complex.
Source: Stacks Tag 0GKF (blueprint: lem-pur-etale-sum-tensor-test). -/
def etaleSumTensorTestRealizationComplex (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] :=
  letI := etaleConstantModuleFunctor_isEquivalence T A
  (etaleConstantModuleFunctor T A ⋙
    SheafOfModules.pushforward.{u + 1} (F := 𝟭 T.Etale)
      (constantModuleHomRingIso T.smallEtaleTopology A).inv).mapHomologicalComplex
        (ComplexShape.up ℤ)

/-- Sum extension applied degreewise before realization.
Source: Stacks Tag 0GKF (blueprint: lem-pur-etale-sum-tensor-test). -/
def etaleSumTensorTestSheafComplexExtension {U X : Scheme.{u}} (f : U ⟶ X)
    (hf : Etale f) (A : Type (u + 1)) [CommRing A] :=
  letI := (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f hf).isLeftAdjoint
  (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f hf).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Inverse image in the canonical constant-ring coordinates: restrict to constants,
apply the published upper star, and realize again. Source: Stacks Tags 093I, 03CV,
and 03D7 (blueprint: lem-pur-etale-sum-tensor-test). -/
def etaleSumTensorTestInverseImage {U X : Scheme.{u}} (f : U ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    EtaleSumTensorTestModule X A ⥤ EtaleSumTensorTestModule U A :=
  SheafOfModules.pushforward.{u + 1} (F := 𝟭 X.Etale)
      (constantModuleHomRingIso X.smallEtaleTopology A).hom ⋙
    etaleConstantModuleRestrictionFunctor X A ⋙
    Etale.upperStar (ModuleCat.{u + 1} A) f ⋙
    etaleSumTensorTestRealization U A

set_option backward.isDefEq.respectTransparency false in
/-- Transported inverse image is exact. The ring transports and the constant-scalar
restriction and realization are equivalences, and upper star is exact.
Source: Stacks Tag 03D7 (blueprint: lem-pur-etale-sum-tensor-test). -/
theorem etaleSumTensorTestInverseImage_exact {U X : Scheme.{u}} (f : U ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    exactFunctor _ _ (etaleSumTensorTestInverseImage f A) := by
  let := etaleConstantModuleFunctor_isEquivalence U A
  let : (etaleConstantModuleRestrictionFunctor X A).IsEquivalence :=
    Functor.IsEquivalence.mk' (etaleConstantModuleFunctor X A)
      (etaleConstantModuleCounitIso X A).symm (etaleConstantModuleUnitIso X A).symm
  let := (constantRingTransport_equivalence X A).1
  let := (constantRingTransport_equivalence U A).2
  apply (exactFunctor_iff _).mpr
  constructor <;>
    dsimp only [etaleSumTensorTestInverseImage, etaleSumTensorTestRealization] <;>
    infer_instance

/-- The explicit test complex obtained by exact inverse image degreewise.
Source: Stacks Tag 03D7 (blueprint: lem-pur-etale-sum-tensor-test). -/
def etaleSumTensorTestInverseImageComplex {U X : Scheme.{u}} (f : U ⟶ X)
    (A : Type (u + 1)) [CommRing A] :=
  let h := etaleSumTensorTestInverseImage_exact f A
  let : PreservesFiniteLimits (etaleSumTensorTestInverseImage f A) := h.1
  let := Functor.additive_of_preserves_binary_products (etaleSumTensorTestInverseImage f A)
  (etaleSumTensorTestInverseImage f A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The concrete inverse-image test is acyclic whenever the original test is.
Apply the exact functor to the exact short complex in every degree.
Source: Stacks Tag 03D7 (blueprint: lem-pur-etale-sum-tensor-test). -/
theorem etaleSumTensorTestInverseImageComplex_acyclic {U X : Scheme.{u}} (f : U ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    (B : CochainComplex (EtaleSumTensorTestModule X A) ℤ) (hB : B.Acyclic) :
    ((etaleSumTensorTestInverseImageComplex f A).obj B).Acyclic := by
  have h := etaleSumTensorTestInverseImage_exact f A
  let : PreservesFiniteLimits (etaleSumTensorTestInverseImage f A) := h.1
  let : PreservesFiniteColimits (etaleSumTensorTestInverseImage f A) := h.2
  let := Functor.additive_of_preserves_binary_products (etaleSumTensorTestInverseImage f A)
  intro n
  exact (hB n).map (etaleSumTensorTestInverseImage f A)

/-- The actual direct-sum total tensor, with Koszul differential.
Source: Stacks Tag 012Z (blueprint: lem-pur-etale-sum-tensor-test). -/
def etaleSumTensorTestTotal (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (B P : CochainComplex (EtaleSumTensorTestModule T A) ℤ) :=
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  CochainComplex.mapBifunctor B P (MonoidalCategory.curriedTensor _)

end AlgebraicGeometry.Scheme
