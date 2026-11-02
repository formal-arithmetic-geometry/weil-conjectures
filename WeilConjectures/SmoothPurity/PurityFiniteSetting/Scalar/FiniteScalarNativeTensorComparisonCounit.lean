/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarMonoidalModel
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact

/-! # The native scalar tensor comparison on cochain representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u u₁ u₂
open CategoryTheory CategoryTheory.Abelian MonoidalCategory AlgebraicGeometry DerivedCategory
open scoped CategoryTheory.Functor
namespace CategoryTheory
private theorem finiteScalar_transport_tensor_counit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) {P P' Q Q' T T' : C} {EP EP' EQ EQ' ET ET' V V' : D}
    (a : P ≅ P') (b : Q ≅ Q') (c : T ≅ T')
    (e : EP ≅ EP') (f : EQ ≅ EQ') (d : ET ≅ ET') (g : V ≅ V')
    (t : P ⊗ Q ⟶ T) (t' : EP ⊗ EQ ⟶ V)
    (εP : L.obj P ⟶ EP) (εQ : L.obj Q ⟶ EQ) (εT : L.obj T ⟶ ET)
    (δ : ET ⟶ V) (δ' : ET' ⟶ V')
    (τ : L.obj (P ⊗ Q) ⟶ L.obj P ⊗ L.obj Q)
    (τ' : L.obj (P' ⊗ Q') ⟶ L.obj P' ⊗ L.obj Q')
    (hn : L.map (a.inv ⊗ₘ b.inv) ≫ τ = τ' ≫ (L.map a.inv ⊗ₘ L.map b.inv))
    (hc : τ ≫ (εP ⊗ₘ εQ) ≫ t' = L.map t ≫ εT ≫ δ)
    (hδ : δ ≫ g.hom = d.hom ≫ δ') :
    L.map ((a.inv ⊗ₘ b.inv) ≫ t ≫ c.hom) ≫
        (L.map c.inv ≫ εT ≫ d.hom) ≫ δ' =
      τ' ≫ ((L.map a.inv ≫ εP ≫ e.hom) ⊗ₘ (L.map b.inv ≫ εQ ≫ f.hom)) ≫
        ((e.inv ⊗ₘ f.inv) ≫ t' ≫ g.hom) := by
  rw [← tensorHom_comp_tensorHom (L.map a.inv) (L.map b.inv)]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc,
    tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← tensorHom_comp_tensorHom (L.map a.inv) (L.map b.inv)]
  rw [Category.assoc, ← reassoc_of% hn, reassoc_of% hc, hδ]

end CategoryTheory
namespace CategoryTheory.Functor

attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  rightExact_cochainCounit

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

section CachedMonoidalStructures

-- Cache the canonical structures. All public signatures are outside this section.
private noncomputable abbrev complexMonoidalC : MonoidalCategory (CochainComplex C ℤ) :=
  inferInstance
private noncomputable abbrev complexMonoidalD : MonoidalCategory (CochainComplex D ℤ) :=
  inferInstance
private noncomputable abbrev homotopyMonoidalC :
    MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
private noncomputable abbrev homotopyMonoidalD :
    MonoidalCategory (HomotopyCategory D (.up ℤ)) := inferInstance
private noncomputable abbrev derivedMonoidalC : MonoidalCategory (DerivedCategory C) :=
  inferInstance
private noncomputable abbrev derivedMonoidalD : MonoidalCategory (DerivedCategory D) :=
  inferInstance

attribute [local instance 2000] complexMonoidalC complexMonoidalD
  homotopyMonoidalC homotopyMonoidalD derivedMonoidalC derivedMonoidalD

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

private lemma finiteScalar_tensorator_Q (P Q : CochainComplex C ℤ) :
    LaxMonoidal.μ DerivedCategory.Q P Q =
      ((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app Q) ≫
      LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app
        (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) := by
  change (_ ⊗ₘ _) ≫ (_ ≫ Qh.map (𝟙 _)) ≫ _ = _
  simp only [Qh.map_id, Category.comp_id]
  rfl

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh

private lemma finiteScalar_comparison_naturality_tensorHom {K₁ K₂ M₁ M₂ : DerivedCategory C}
    (f : K₁ ⟶ K₂) (g : M₁ ⟶ M₂) :
    F.leftDerivedFunctor.map (f ⊗ₘ g) ≫
        (F.leftDerivedTensorComparison.app K₂).app M₂ =
      (F.leftDerivedTensorComparison.app K₁).app M₁ ≫
        (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) := by
  have h₁ := congr_app (F.leftDerivedTensorComparison.naturality f) M₁
  have h₂ := (F.leftDerivedTensorComparison.app K₂).naturality g
  dsimp at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]

private lemma finiteScalar_comparison_cochain (P Q : CochainComplex C ℤ) :
    F.leftDerivedFunctor.map (LaxMonoidal.μ (DerivedCategory.Q (C := C)) P Q) ≫
        F.rightExact_cochainCounit (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) ≫
        (DerivedCategory.Q (C := D)).map
          (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
      (F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
        (F.rightExact_cochainCounit P ⊗ₘ F.rightExact_cochainCounit Q) ≫
        LaxMonoidal.μ (DerivedCategory.Q (C := D))
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) := by
  rw [finiteScalar_tensorator_Q, finiteScalar_tensorator_Q]
  let p := HomotopyCategory.quotient C (.up ℤ)
  let q := HomotopyCategory.quotient D (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  let e' := DerivedCategory.quotientCompQhIso D
  let δ := ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
  have h := F.leftDerivedTensorComparison_app_app_comp_tensorHom
    (p.obj P) (p.obj Q)
  have ht := finiteScalar_transport_tensor_counit
    (C := DerivedCategory C) (D := DerivedCategory D) F.leftDerivedFunctor (e.app P) (e.app Q)
    (e.app (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj
      (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q)))
    (e'.app (((curriedTensor (CochainComplex D ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (LaxMonoidal.μ (Qh (C := C)) (p.obj P) (p.obj Q))
    (LaxMonoidal.μ (Qh (C := D)) (q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
      (q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (F.leftDerivedFunctorCounit.app (p.obj P))
    (F.leftDerivedFunctorCounit.app (p.obj Q))
    (F.leftDerivedFunctorCounit.app (p.obj (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q)))
    ((Qh (C := D)).map (q.map δ)) ((DerivedCategory.Q (C := D)).map δ)
    ((F.leftDerivedTensorComparison.app (Qh.obj (p.obj P))).app (Qh.obj (p.obj Q)))
    ((F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
      (DerivedCategory.Q.obj Q))
    (F.finiteScalar_comparison_naturality_tensorHom (e.inv.app P) (e.inv.app Q)) h
    (DerivedCategory.quotientCompQhIso_hom_naturality δ)
  dsimp only [p, q, e, e', δ] at ht
  unfold rightExact_cochainCounit
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Iso.app_hom, Iso.app_inv, MonoidalCategory.curriedTensor_obj_obj] at ht ⊢
  simpa only [Category.assoc] using ht

end CachedMonoidalStructures

end CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

set_option maxHeartbeats 2000000 in
-- Specializing the pro-etale derived-category instances is expensive.
/-- The native scalar tensorator satisfies the cochain counit square.
Source: Stacks 06YY and 07A4; (blueprint:
lem-pur-finite-scalar-native-tensor-comparison-counit).
Proof: use the defining homotopy counit square of leftDerivedTensorComparison.
Express each cochain tensorator through quotientCompQhIso. Naturality moves the
comparison through the quotient isomorphisms, whose inverse pairs cancel. The
remaining three counit composites are exactly rightExact_cochainCounit. -/
theorem finiteScalarNativeTensorComparison_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    letI : Algebra A B := φ.toAlgebra
    let F := ProEtale.sheafExtendScalars φ T
    letI : F.PreservesKFlatQuasiIso :=
      ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
    F.leftDerivedFunctor.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q C D) ≫
      F.rightExact_cochainCounit (C ⊗ D) ≫
      _root_.DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app C).app D) =
    (F.leftDerivedTensorComparison.app (_root_.DerivedCategory.Q.obj C)).app
        (_root_.DerivedCategory.Q.obj D) ≫
      (F.rightExact_cochainCounit C ⊗ₘ F.rightExact_cochainCounit D) ≫
      Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj C)
        ((F.mapHomologicalComplex (.up ℤ)).obj D) := by
  let : Algebra A B := φ.toAlgebra
  let F := ProEtale.sheafExtendScalars φ T
  let : F.PreservesKFlatQuasiIso :=
    ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
  exact Functor.finiteScalar_comparison_cochain F C D

end WeilConjectures.PurityFiniteSetting
