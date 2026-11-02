/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
import WeilConjectures.CategoryTheory.DerivedCategory.AsFunctorLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryStrictSquare
import WeilConjectures.CategoryTheory.Comma.StructuredArrowUniversalIso
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients

/-! # Universality of the localized quotient arrows

Source: Stacks Project, Tags 06YY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The localization of a termwise consecutive arrow of fixed-scalar coordinates, as an arrow
to derived restriction of scalars. -/
def finitePerfectAdicStrictLocalizedArrow
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (V : X.Etale) (n : ℕ)
    (δ : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n)
    (P : CochainComplex (CompletedAdicModules X d) ℤ) :
    DerivedCategory.Q.obj (((finitePerfectAdicQuotientStrictCoordinates X d φ V
        (n + 1)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      (normalizationRestrict (ProEt.topology V.left)
        (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj
        (DerivedCategory.Q.obj
          (((finitePerfectAdicQuotientStrictCoordinates X d φ V n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) :=
  Functor.strictSquareArrow (finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1))
    (finitePerfectAdicQuotientStrictCoordinates X d φ V n)
    (finitePerfectAdicStepRestrict X d V n) δ P

private theorem homotopyModelIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ)
    (hε : IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))) :
    Nonempty (L.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) := by
  have := hε
  exact ⟨L.mapIso ((DerivedCategory.quotientCompQhIso C).app P).symm ≪≫
    asIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso D).app _⟩

/-- Derived scalar extension is computed termwise on K-flat complexes. -/
theorem completedAdicDerivedChange_kFlat_iso
    (X : Scheme.{t}) {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S)
    (P : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ)
    (hk : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    Nonempty ((completedAdicDerivedChange X φ).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let E := completedAdicChange X φ
  let L := completedAdicDerivedChange X φ
  have hEAdd : E.Additive := inferInstance
  obtain ⟨ε, hu, ht, hc⟩ :=
    (completedAdicChangeData X φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec
  change DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh at ε
  have hε : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hc P hk
  change Nonempty (L.obj (DerivedCategory.Q.obj P) ≅
    DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
  clear hu ht hc
  clear_value E L
  as_aux_lemma => exact homotopyModelIso E L ε P hε

/-- The ordinary quotient arrow localizes, on every K-flat complex, to a universal arrow for
derived restriction of scalars along the consecutive quotient map.
Source: Stacks Project, Tag 06YY (tensor balancing) and Tag 09C6.

Proof sketch: scalar extension along the finite projection preserves K-flatness, and since `φ`
is an isomorphism the terms of the fixed-scalar coordinates are flat over the constant ring.
Derived extension of scalars along the quotient map is therefore computed termwise, and the
transpose of the localized arrow is the balancing isomorphism
`A_n ⊗ (P ⊗ R_(n+1)) ≅ P ⊗ R_n`. -/
theorem finitePerfectAdic_quotient_transition_universal
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (V : X.Etale) (n : ℕ)
    (δ : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n)
    (hδ : FinitePerfectAdicQuotientTransition X d φ V n δ)
    (P : CochainComplex (CompletedAdicModules X d) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing X d) P) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (finitePerfectAdicStrictLocalizedArrow X d φ V n δ P))) := by
  sorry

end AlgebraicGeometry.Scheme
