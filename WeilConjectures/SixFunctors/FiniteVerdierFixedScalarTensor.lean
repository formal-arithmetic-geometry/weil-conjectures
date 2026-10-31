/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarMonoidal
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars

/-! # Normalized tensor structure for the fixed scalar adjoint on either site -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures

section GenericNormalization
universe a b
variable {V : Type a} [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
  [MonoidalClosed V] [BraidedCategory V] [Abelian.HasFunctorialFlatResolution V]
  {W : Type b} [Category.{u + 1} W] [Abelian W]
  [IsGrothendieckAbelian.{u + 1} W] [MonoidalCategory W] [MonoidalPreadditive W]
  [MonoidalClosed W] [BraidedCategory W] [Abelian.HasFunctorialFlatResolution W]

private theorem coreTensor_normalized
    (F : V ⥤ W) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
    [F.IsLeftAdjoint] [F.Monoidal]
    (G : DerivedCategory V ⥤ DerivedCategory W) (e : G ≅ F.leftDerivedFunctor)
    (r : ∀ P : CochainComplex V ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = e.hom.app (DerivedCategory.Q.obj P) ≫ F.rightExact_cochainCounit P) :
    letI := F.leftDerivedFunctorMonoidal
    let c := Functor.Monoidal.coreMonoidalTransport e.symm
    ∀ P Q : CochainComplex V ℤ,
      (c.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv ≫
          (r P ⊗ₘ r Q) ≫ Functor.LaxMonoidal.μ DerivedCategory.Q
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
        G.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ r (P ⊗ Q) ≫
          DerivedCategory.Q.map
            (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) := by
  letI := F.leftDerivedFunctorMonoidal
  dsimp only
  intro P Q
  simp only [hr]
  change ((e.hom.app _ ≫ Functor.OplaxMonoidal.δ F.leftDerivedFunctor _ _) ≫
      (e.inv.app _ ⊗ₘ e.inv.app _)) ≫ _ ≫ _ = _
  change ((e.hom.app _ ≫ (F.rightExact_leftDerivedTensorComparison.app _).app _) ≫
      (e.inv.app _ ⊗ₘ e.inv.app _)) ≫ _ ≫ _ = _
  simpa only [Category.assoc, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    curriedTensor_obj_obj] using
    (CategoryTheory.transfer_tensor_counit G F.leftDerivedFunctor e
      (T := DerivedCategory.Q.obj (P ⊗ Q))
      _ _ _ _ _ _ (F.rightExact_comparison_cochain P Q)).symm

end GenericNormalization

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (φ : A →+* B)

private theorem ordinaryScalar_preservesKFlat :
    (finiteVerdierOrdinaryExtension J φ).PreservesKFlatQuasiIso := by
  letI := φ.toAlgebra
  let E := finiteVerdierOrdinaryExtension J φ
  let U := Sheaf.restrictScalars J φ
  let e : E ⋙ U ≅ tensorRight
      ((constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A B)) :=
    Sheaf.extendScalarsCompRestrictScalarsIso J A B
  apply Functor.PreservesKFlatQuasiIso.mk'
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa
    ((constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A B))
  have hEU := ht.of_iso ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
  have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
    hEU.of_iso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)

private theorem fixedScalar_derivedComparison
    [(finiteVerdierOrdinaryExtension J φ).PreservesKFlatQuasiIso] :
    ∃ e : pbcFixedScalarExtension J φ ≅
        (finiteVerdierOrdinaryExtension J φ).leftDerivedFunctor,
      ∀ P, finiteVerdierScalarRepresentative J φ P =
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteVerdierOrdinaryExtension J φ).rightExact_cochainCounit P := by
  let E := finiteVerdierOrdinaryExtension J φ
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U := finiteVerdierOrdinaryAdjunction J φ
  letI : E.IsLeftAdjoint := adj.isLeftAdjoint
  let ad : pbcFixedScalarExtension J φ ⊣ U.mapDerivedCategory :=
    Adjunction.ofIsRightAdjoint _
  let b : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e : pbcFixedScalarExtension J φ ≅ E.leftDerivedFunctor := ad.leftAdjointUniq b
  refine ⟨e, ?_⟩
  intro P
  exact (Adjunction.leftDerivedCochainCounit E U adj ad P).symm

/-- On any of the fixed module sites, the derived scalar adjoint has its normalized
strong tensor structure and the Koszul symmetry.

Source: blueprint cor-coef-finite-verdier.proof.md, evaluation compatibility;
Stacks 07A4, descent of scalar balancing on flat K-flat resolutions.
(blueprint: lem-coef-verdier-fixed-scalar-tensor).

Proof: ordinary scalar extension is monoidal, preserves flat objects, and sends
acyclic K-flat complexes to acyclic complexes. Restriction is exact and faithful;
after restriction the extension is tensor with the constant coefficient sheaf.
Derive the ordinary adjunction, then use uniqueness of left adjoints to compare it
with the fixed scalar adjoint. The localized ordinary unit computes its representative
counit. Transport the derived monoidal structure across that comparison. The derived
cochain tensor-counit identity is exactly the requested all-complex normalization.
Ordinary scalar balancing is braided, so its derived and transported tensor structures
respect the Koszul symmetry as well. No flatness of the coefficient quotient is used. -/
theorem finiteVerdier_fixedScalar_tensor :
    letI : (finiteVerdierOrdinaryExtension J φ).IsLeftAdjoint :=
      (finiteVerdierOrdinaryAdjunction J φ).isLeftAdjoint
    ∃ c : (pbcFixedScalarExtension J φ).CoreMonoidal,
      ∃ δ : tensor (C := DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) ⋙
          pbcFixedScalarExtension J φ ≅
        (pbcFixedScalarExtension J φ).prod (pbcFixedScalarExtension J φ) ⋙
          tensor (C := DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))),
      Etale.ExceptionalCoefficients.TensorNormalizationAux
        (finiteVerdierOrdinaryExtension J φ) (pbcFixedScalarExtension J φ)
        (finiteVerdierScalarRepresentative J φ) δ ∧
      (∀ K L, δ.app (K, L) = (c.μIso K L).symm) ∧
      (∀ K L,
        (finiteHomKoszulIso (Sheaf J (ModuleCat.{u + 1} B))
          ((pbcFixedScalarExtension J φ).obj K)
          ((pbcFixedScalarExtension J φ).obj L)).hom ≫ (c.μIso L K).hom =
        (c.μIso K L).hom ≫ (pbcFixedScalarExtension J φ).map
          (finiteHomKoszulIso (Sheaf J (ModuleCat.{u + 1} A)) K L).hom) := by
  let E := finiteVerdierOrdinaryExtension J φ
  let G := pbcFixedScalarExtension J φ
  let adj := finiteVerdierOrdinaryAdjunction J φ
  letI : E.IsLeftAdjoint := adj.isLeftAdjoint
  letI : E.PreservesFlat := Sheaf.preservesFlat_extendScalars J (f := φ)
  letI : E.PreservesKFlatQuasiIso := ordinaryScalar_preservesKFlat J φ
  letI : E.OplaxMonoidal := finiteVerdierOrdinaryExtension_oplax J φ
  letI : E.Monoidal := composeAndSheafifyMonoidal J
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  obtain ⟨e, hr⟩ := fixedScalar_derivedComparison J φ
  letI := E.leftDerivedFunctorMonoidal
  let c := Functor.Monoidal.coreMonoidalTransport e.symm
  letI := c.toMonoidal
  let δ : tensor (C := DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) ⋙ G ≅
      G.prod G ⋙ tensor (C := DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :=
    NatIso.ofComponents (fun KL ↦ (c.μIso KL.1 KL.2).symm)
      (fun f ↦ (Functor.OplaxMonoidal.δ_natural G f.1 f.2).symm)
  refine ⟨c, δ, ?_, fun K L ↦ rfl, ?_⟩
  · exact coreTensor_normalized E G e (finiteVerdierScalarRepresentative J φ) hr
  · apply Functor.core_braiding E G e
    intro K L
    exact (adj.leftAdjointOplaxMonoidal_δ_braiding K L).symm

end WeilConjectures
