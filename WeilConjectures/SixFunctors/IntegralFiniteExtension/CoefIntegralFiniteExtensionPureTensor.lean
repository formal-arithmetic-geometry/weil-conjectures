/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.Completed.CompletedScalarCanonicalAssociatorFormula
import all WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import all WeilConjectures.SmoothPurity.PurStrictScalar.OrdinaryOpenScalarComposition

/-! Pure-tensor coefficient and associator component of integral extension coherence.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
(blueprint: lem-sf-integral-finite-extension-composition-pure-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.sheafCompose CategoryTheory.presheafToSheaf
  CategoryTheory.Functor.leftAdjoint SheafOfModules.changeOfRings
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.completedCoefficientMap
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  WeilConjectures.completedScalarComparison
  WeilConjectures.completedScalarChangeData
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

attribute [local irreducible] comp unit completion CompletedLineTensor.chi
  PurCompactSupport.tensorComposition PurCompactSupport.tensorIdentity sfIntegralScalarComp
  sfIntegralScalarUnit

private theorem completion_eq_chi
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (X : Scheme.{u})
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K)
    (hK' : IsDerivedCompleteUnrestricted l E X K) :
    completion l E L i X K hK = CompletedLineTensor.chi l E X L i K hK' := by
  unfold completion CompletedLineTensor.chi
  rfl

private theorem comp_factor
    (l : ℕ) [Fact l.Prime]
    (E L F : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] F) (X : Scheme.{u})
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (comp l E L i X F j K hK).hom =
      (completion l L F j X _ (extension_complete l E L i X K hK)).inv ≫
        (pbcDerivedExtend (completedCoefficientMap l L F j X)).map
          (completion l E L i X K hK).inv ≫
        (PurCompactSupport.tensorComposition (completedCoefficientMap l E L i X)
          (completedCoefficientMap l L F j X) (completedCoefficientMap l E F (j.comp i) X)
          (PurCompactSupport.completedMap_composition l E L i F j X)).hom.app K ≫
        (completion l E F (j.comp i) X K hK).hom := by
  unfold comp
  rfl

private theorem comp_eq_intrinsic
    (l : ℕ) [Fact l.Prime]
    (E L F : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] F) (X : Scheme.{u})
    (K : sfIntegralConstructibleCategory l E X) :
    (comp l E L i X F j K.obj K.property.1).hom =
      ((sfIntegralScalarComp l E L i X 0 (Fact.out : l.Prime).ne_zero F j).hom.app K).hom := by
  rw [comp_factor, completion_eq_chi l L F j X _ _
      (CompletedLineTensor.extension_complete l E X L i K.obj
        (CompletedLineTensor.intrinsic_complete l E X K)),
    completion_eq_chi l E L i X _ _ (CompletedLineTensor.intrinsic_complete l E X K),
    completion_eq_chi l E F (j.comp i) X _ _
      (CompletedLineTensor.intrinsic_complete l E X K)]
  exact (completedScalarCanonicalAssociatorFormula l E L F i j X K).symm

private theorem unit_factor
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (unit l E X K hK).hom =
      (completion l E E (AlgHom.id (Padic l) E) X K hK).inv ≫
        (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
          (PurCompactSupport.completedMap_identity l E X)) ≪≫
            PurCompactSupport.tensorIdentity
              (completedIntegralCommRingSheafUnrestricted l E X)).hom.app K := by
  unfold unit
  have h := NatIso.trans_app
    (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)))
    (PurCompactSupport.tensorIdentity (completedIntegralCommRingSheafUnrestricted l E X)) K
  exact (congrArg (fun e ↦
    (completion l E E (AlgHom.id (Padic l) E) X K hK).inv ≫ e.hom) h).symm

private theorem completion_hom
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (X : Scheme.{u})
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (completion l E L i X K hK).hom = (completedScalarComparison l E L i X).app K := by
  unfold completion
  rfl

private theorem completion_naturality
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (X : Scheme.{u})
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) (f : K ⟶ M) :
    (pbcDerivedExtend (completedCoefficientMap l E L i X)).map f ≫
        (completion l E L i X M hM).hom =
      (completion l E L i X K hK).hom ≫
        (integralScalarExtensionOfUniverses l E L i X).map f := by
  rw [completion_hom, completion_hom]
  exact (completedScalarComparison l E L i X).naturality f

private theorem self_unit_conjugation
    {C : Type*} [Category* C] (P T : C ⥤ C) (K : C)
    (c : P.obj K ≅ T.obj K) (d : P.obj (T.obj K) ≅ T.obj (T.obj K))
    (v : P.obj K ⟶ K) (α : P.obj (P.obj K) ⟶ P.obj K)
    (ha : α = P.map v)
    (hn : P.map (c.inv ≫ v) ≫ c.hom = d.hom ≫ T.map (c.inv ≫ v)) :
    d.inv ≫ P.map c.inv ≫ α ≫ c.hom = T.map (c.inv ≫ v) := by
  rw [ha, ← Functor.map_comp_assoc, hn, Iso.inv_hom_id_assoc]

private theorem self_ordinary_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : IntegralVerdier.Ambient l E X) :
    let a := completedCoefficientMap l E E (AlgHom.id (Padic l) E) X
    (PurCompactSupport.tensorComposition a a a
      (PurCompactSupport.completedMap_composition l E E (AlgHom.id (Padic l) E)
        E (AlgHom.id (Padic l) E) X)).hom.app K =
      (pbcDerivedExtend a).map
        ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
          (PurCompactSupport.completedMap_identity l E X)) ≪≫
            PurCompactSupport.tensorIdentity
              (completedIntegralCommRingSheafUnrestricted l E X)).hom.app K) := by
  exact PurStrictScalar.tensorComposition_identity_left_of_eq
    (completedIntegralCommRingSheafUnrestricted l E X) _
    (PurCompactSupport.completedMap_identity l E X)
    (PurCompactSupport.completedMap_composition l E E (AlgHom.id (Padic l) E)
      E (AlgHom.id (Padic l) E) X) K

private theorem self_comp_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (comp l E E (AlgHom.id (Padic l) E) X E (AlgHom.id (Padic l) E)
      K hK).hom =
      (integralScalarExtensionOfUniverses l E E (AlgHom.id (Padic l) E) X).map
        (unit l E X K hK).hom := by
  rw [comp_factor, unit_factor]
  exact self_unit_conjugation
    (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X))
    (integralScalarExtensionOfUniverses l E E (AlgHom.id (Padic l) E) X) K
    (completion l E E (AlgHom.id (Padic l) E) X K hK)
    (completion l E E (AlgHom.id (Padic l) E) X _
      (extension_complete l E E (AlgHom.id (Padic l) E) X K hK))
    _ _ (self_ordinary_unit l E X K)
    (completion_naturality l E E (AlgHom.id (Padic l) E) X _ K
      (extension_complete l E E (AlgHom.id (Padic l) E) X K hK) hK _)

private theorem unit_eq_intrinsic
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : sfIntegralConstructibleCategory l E X) :
    (unit l E X K.obj K.property.1).hom =
      ((sfIntegralScalarUnit l E X 0 (Fact.out : l.Prime).ne_zero).hom.app K).hom := by
  let T := sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
    E E (AlgHom.id (Padic l) E) X
  have : T.Faithful := Functor.Faithful.of_iso
    (sfIntegralScalarUnit l E X 0 (Fact.out : l.Prime).ne_zero).symm
  let f : T.obj K ⟶ K := ObjectProperty.homMk (unit l E X K.obj K.property.1).hom
  have hf : T.map f =
      T.map ((sfIntegralScalarUnit l E X 0 (Fact.out : l.Prime).ne_zero).hom.app K) := by
    apply ObjectProperty.hom_ext
    exact (self_comp_unit l E X K.obj K.property.1).symm.trans
      ((comp_eq_intrinsic l E E E (AlgHom.id (Padic l) E)
        (AlgHom.id (Padic l) E) X K).trans
        (congrArg (fun g ↦ g.hom)
          (integral_source_unit l E E (AlgHom.id (Padic l) E) X 0
            (Fact.out : l.Prime).ne_zero K)))
  exact congrArg (fun g ↦ g.hom) (T.map_injective hf)

-- The original API retains the dualizing data and presentations; scalar coherence is independent.
set_option linter.unusedVariables false in
/-- Pure tensor unit and associator equations for fixed integral comparisons.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
Proof: on pure coefficient tensors scalar multiplication is the identity unitor,
and iterated scalar extension is balanced multiplication; the normalized completion
maps cancel at intermediate vertices. The two parenthesizations therefore agree.
-/
theorem comparison_composition_pure_tensor
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X)) :
    ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
      (c : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l F X)),
      (∀ (K : sfIntegralConstructibleCategory l E X),
        (comp l E E (AlgHom.id (Padic l) E) X L ι K.obj K.property.1).hom =
          (integralScalarExtensionOfUniverses l E L ι X).map
            (unit l E X K.obj K.property.1).hom) ∧
      (∀ (K : sfIntegralConstructibleCategory l E X),
        (comp l E L ι X L (AlgHom.id (Padic l) L) K.obj K.property.1).hom =
          (unit l L X
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)
            (extension_complete l E L ι X K.obj K.property.1)).hom) ∧
      (∀ (G : Type u) [Field G] [Algebra (Padic l) G]
        [FiniteDimensional (Padic l) G]
        (k : F →ₐ[Padic l] G) (K : sfIntegralConstructibleCategory l E X),
        (integralScalarExtensionOfUniverses l F G k X).map
            (comp l E L ι X F j K.obj K.property.1).hom ≫
          (comp l E F (j.comp ι) X G k K.obj K.property.1).hom =
          (comp l L F j X G k
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)
            (extension_complete l E L ι X K.obj K.property.1)).hom ≫
          (comp l E L ι X G (k.comp j) K.obj K.property.1).hom) := by
  intro F _ _ _ j wF c
  refine ⟨?_, ?_, ?_⟩
  · intro K
    rw [comp_eq_intrinsic, unit_eq_intrinsic]
    exact congrArg (fun g ↦ g.hom)
      (integral_source_unit l E L ι X 0 (Fact.out : l.Prime).ne_zero K)
  · intro K
    exact (comp_eq_intrinsic l E L L ι (AlgHom.id (Padic l) L) X K).trans
      ((congrArg (fun g ↦ g.hom)
        (integral_target_unit l E L ι X 0 (Fact.out : l.Prime).ne_zero K)).trans
        (unit_eq_intrinsic l L X
          ((sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
            E L ι X).obj K)).symm)
  · intro G _ _ _ k K
    exact (congrArg₂ (fun f g ↦ (integralScalarExtensionOfUniverses l F G k X).map f ≫ g)
      (comp_eq_intrinsic l E L F ι j X K)
      (comp_eq_intrinsic l E F G (j.comp ι) k X K)).trans
      ((congrArg (fun g ↦ g.hom)
        (integral_pentagon l E L ι X 0 (Fact.out : l.Prime).ne_zero F j G k K)).trans
        (congrArg₂ (fun f g ↦ f ≫ g)
          (comp_eq_intrinsic l L F G j k X
            ((sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
              E L ι X).obj K)).symm
          (comp_eq_intrinsic l E L G ι (k.comp j) X K).symm))

end WeilConjectures.IntegralFiniteExtension
