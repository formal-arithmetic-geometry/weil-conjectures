/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup

/-! Uniqueness of normalized point tensor data.
Source: Stacks 07A4 and 03EL, and the normalization fields of the derived cup
(blueprint: lem-pod-condensed-point-tensor-data-unique).
Proof plan: compare two records field by field. Equality on pure ordinary tensors
and the total-complex summands gives equality of the chain maps; the unit equation
gives equality of units. The localization normalization then gives equality of
derived tensorators and their coherence fields. This is a genuine uniqueness
statement and has no contradiction hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings CategoryTheory.Obj

private theorem lax_ext_mu {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (m n : F.LaxMonoidal) (h : ∀ X Y, m.μ X Y = n.μ X Y) : m = n := by
  let Rm : MonObj (F.obj (𝟙_ C)) := by
    letI := m
    exact F.monObjObj (𝟙_ C)
  let Rn : MonObj (F.obj (𝟙_ C)) := by
    letI := n
    exact F.monObjObj (𝟙_ C)
  have hmul : Rm.mul = Rn.mul :=
    congrArg (fun t ↦ t ≫ F.map (λ_ (𝟙_ C)).hom) (h (𝟙_ C) (𝟙_ C))
  have hε := congrArg (fun p : MonObj (F.obj (𝟙_ C)) ↦ p.one) (MonObj.ext Rm Rn hmul)
  change m.ε ≫ F.map (𝟙 (𝟙_ C)) = n.ε ≫ F.map (𝟙 (𝟙_ C)) at hε
  exact Functor.LaxMonoidal.ext
    ((cancel_mono (F.map (𝟙 (𝟙_ C)))).mp hε) (funext fun X ↦ funext (h X))

section
universe a b r w z
variable {B : Type a} [Category.{b} B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B] [BraidedCategory B]
  [HasColimitsOfSize.{0, 0} B] [IsGrothendieckAbelian.{b} B]
  [Abelian.HasFunctorialFlatResolution B]
  {S : Type r} [CommRing S]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{z} (ModuleCat.{r} S)]
  (G : B ⥤ ModuleCat.{r} S) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private theorem cup_ext_ordinary (d₁ d₂ : ExactSectionsDerivedCup G)
    (h : d₁.ordinary = d₂.ordinary) : d₁ = d₂ := by
  have hchain : d₁.chain = d₂.chain := by
    funext K L
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    exact (d₁.chain_summand K L p q n hpq).trans
      ((congrArg (fun t : G.LaxMonoidal ↦
        t.μ (K.X p) (L.X q) ≫ G.map (HomologicalComplex.ιTensorObj K L p q n hpq)) h).trans
          (d₂.chain_summand K L p q n hpq).symm)
  have hunit : d₁.chainUnit = d₂.chainUnit := by
    apply HomologicalComplex.from_single_hom_ext
    exact d₁.chainUnit_zero.trans
      ((congrArg (fun t : G.LaxMonoidal ↦
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{r} S))).hom ≫
          t.ε ≫ G.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ B)).inv) h).trans
        d₂.chainUnit_zero.symm)
  have hderived : d₁.derived = d₂.derived := by
    apply lax_ext_mu
    intro M N
    obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_kFlat_iso N
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    let eL : DerivedCategory.Q.obj L ≅ N :=
      ((DerivedCategory.quotientCompQhIso B).app L).symm ≪≫ eP
    let K := DerivedCategory.Q.objPreimage M
    let eK := DerivedCategory.Q.objObjPreimageIso M
    have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K L) := by
      have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
          ((HomotopyCategory.quotient B (.up ℤ)).obj K)
          ((HomotopyCategory.quotient B (.up ℤ)).obj L)) :=
        DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
          (HomotopyCategory.quasiIso B (.up ℤ)) _ _ hP
      change IsIso ((_ ⊗ₘ _) ≫
        (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
      infer_instance
    have key : d₁.derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
        d₂.derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) := by
      apply (cancel_mono (G.mapDerivedCategory.map
        (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
          G.mapDerivedCategoryFactors.hom.app (K ⊗ L))).mp
      rw [d₁.tensor_normalization, d₂.tensor_normalization, hchain]
    have nat₁ := @Functor.LaxMonoidal.μ_natural _ _ _ _ _ _
      G.mapDerivedCategory d₁.derived _ _ _ _ eK.hom eL.hom
    have nat₂ := @Functor.LaxMonoidal.μ_natural _ _ _ _ _ _
      G.mapDerivedCategory d₂.derived _ _ _ _ eK.hom eL.hom
    apply (cancel_epi
      (G.mapDerivedCategory.map eK.hom ⊗ₘ G.mapDerivedCategory.map eL.hom)).mp
    exact nat₁.trans ((congrArg (fun t ↦ t ≫
      G.mapDerivedCategory.map (eK.hom ⊗ₘ eL.hom)) key).trans nat₂.symm)
  cases d₁
  cases d₂
  simp only [ExactSectionsDerivedCup.mk.injEq]
  exact ⟨h, hderived, hchain, hunit⟩
end

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
  [PreservesFiniteLimits (condensedRingCoefficientSections Λ (Spec (.of k)))]
  [PreservesFiniteColimits (condensedRingCoefficientSections Λ (Spec (.of k)))]

-- Keep the algebraically closed point hypothesis of the published statement.
set_option linter.unusedSectionVars false in
theorem tensorData_unique :
    ∀ d₁ d₂ : ExactSectionsDerivedCup (condensedRingCoefficientSections Λ (Spec (.of k))),
      (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k))))
        (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj M)
        (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj N),
        (d₁.ordinary.μ M N).hom (x ⊗ₜ[Γ Λ] y) = (λ_ _).inv ≫ (x ⊗ₘ y)) →
      (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k))))
        (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj M)
        (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj N),
        (d₂.ordinary.μ M N).hom (x ⊗ₜ[Γ Λ] y) = (λ_ _).inv ≫ (x ⊗ₘ y)) →
      d₁ = d₂ := by
  intro d₁ d₂ h₁ h₂
  apply cup_ext_ordinary
  apply lax_ext_mu
  intro M N
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact (h₁ M N x y).trans (h₂ M N x y).symm

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
