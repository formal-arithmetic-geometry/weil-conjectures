/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionModelFamily
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
import WeilConjectures.AlgebraicGeometry.AdicResidueSliceCompleteness

/-! # Finite-level local models in the general adic lifting argument

Source: Stacks Project, proetale.tex, Tag 09C6, first half of the proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

private theorem adicResidue_complete_of_iso
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {B k : Sheaf T CommRingCat.{w}} (q : B ⟶ k)
    {M N : CategoryTheory.ConstantCompletion.D B} (e : M ≅ N)
    (h : CategoryTheory.ConstantCompletion.IsComplete q N) :
    CategoryTheory.ConstantCompletion.IsComplete q M := by
  let : HasDerivedCategory.{w + 1} (SheafOfModules.{w} (siteModuleRings B)) :=
    HasDerivedCategory.standard _
  let hD (U : D) : HasDerivedCategory.{w + 1}
      (SheafOfModules.{w} ((siteModuleRings B).over U)) :=
    HasDerivedCategory.standard _
  intro U f hf
  exact (h U f hf).of_iso
    ((derivedInternalHom.{w, w + 1} (T.over U) (B.over U)).mapIso
      ((Iso.refl _).op.prod
        ((ringedDerivedRestriction.{w, w + 1, w + 1} B U).mapIso e)))

set_option maxHeartbeats 500000 in
-- Comparing the two termwise constant presentations unfolds their sheafification maps.
private theorem adicResidue_constant_complete
    (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q))
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0)
      ((adicResidueRestriction
        (CategoryTheory.ConstantCompletion.completed
          (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
            (adicResidueConstantPerfect X J P)) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := CategoryTheory.ConstantCompletion.completed T A J
  let : HasDerivedCategory.{(max v (u + 1)) + 1}
      (CategoryTheory.ConstantCompletion.Mod B) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{(max v (u + 1)) + 1}
      (CategoryTheory.ConstantCompletion.Mod (B.over U)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{(max v (u + 1)) + 1}
      (SheafOfModules.{max v (u + 1)} ((siteModuleRings B).over U)) :=
    HasDerivedCategory.standard _
  let K := AdicPerfectModel.model T J P
  let F := SheafOfModules.overFunctor.{max v (u + 1)} (siteModuleRings B) U
  let e : (adicResidueRestriction B U).obj (adicResidueConstantPerfect X J P) ≅
      (CategoryTheory.ConstantCompletion.Q (B.over U)).obj
        ((AdicPerfectModel.overComplex B U).obj K) := by
    let α : SheafOfModules.strictPerfectConstantSheaf T A ⋙
        SheafOfModules.restrictScalars (CategoryTheory.constantModuleHomRingIso T A).inv ≅
        commutativeSiteConstantModuleFunctor T A :=
      AdicPerfectModel.constantPresentationIso (J := T) (A := A)
    let β := Functor.isoWhiskerRight α
      (CategoryTheory.ConstantCompletion.change
        (CategoryTheory.ConstantCompletion.coefficientMap T A J))
    let γ := (NatIso.mapHomologicalComplex β (.up ℤ)).app P
    exact (adicResidueRestriction B U).mapIso
      ((CategoryTheory.ConstantCompletion.Q B).mapIso γ) ≪≫
        F.mapDerivedCategoryFactors.app K
  exact adicResidue_complete_of_iso _ e
    (AdicPerfectModel.complete_slice_model X J P hP U)

private theorem adicResidue_restriction_factor
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    (B : Sheaf T CommRingCat.{w}) {U V : D} (g : U ⟶ V) :
    ∃ R : CategoryTheory.ConstantCompletion.D (B.over V) ⥤
        CategoryTheory.ConstantCompletion.D (B.over U),
      Nonempty (adicResidueRestriction B V ⋙ R ≅ adicResidueRestriction B U) := by
  let O : Sheaf T RingCat.{w} :=
    (sheafCompose T (forget₂ CommRingCat.{w} RingCat.{w})).obj B
  let : HasDerivedCategory.{w + 1} (SheafOfModules.{w} O) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{w + 1} (SheafOfModules.{w} (O.over V)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{w + 1} (SheafOfModules.{w} (O.over U)) :=
    HasDerivedCategory.standard _
  let F := SheafOfModules.overFunctor.{w} O V
  let G := SheafOfModules.overMap.{w} O g
  let H := SheafOfModules.overFunctor.{w} O U
  let : F.Additive := ringedSite_overFunctor_additive T B V
  let : PreservesFiniteLimits F := ringedSite_overFunctor_limits T B V
  let : PreservesFiniteColimits F := ringedSite_overFunctor_colimits T B V
  let : G.Additive := ringedSite_overMap_additive T B g
  let : PreservesFiniteLimits G := ringedSite_overMap_limits T B g
  let : PreservesFiniteColimits G := ringedSite_overMap_colimits T B g
  let : H.Additive := ringedSite_overFunctor_additive T B U
  let : PreservesFiniteLimits H := ringedSite_overFunctor_limits T B U
  let : PreservesFiniteColimits H := ringedSite_overFunctor_colimits T B U
  refine ⟨G.mapDerivedCategory, ⟨?_⟩⟩
  let c : (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso F G).symm
  exact c.symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (C := SheafOfModules.{w} O) (D := SheafOfModules.{w} (O.over U))
      (F := F ⋙ G) (G := H) (SheafOfModules.overFunctorMap.{w} O g)

/-- A single local finite-projective model for all finite reductions, without compatible
markings or an isomorphism over completed coefficients
(Stacks, Tags 09C6, 09C2, 09BI, 09AW and 099Q). -/
theorem adicResidue_finite_local_models
    (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A]
    (M : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J))
    (_hcomplete : CategoryTheory.ConstantCompletion.IsComplete
      (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X) A
        J 0) M)
    (C : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A J 0))
    (_hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (_hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (A ⧸ J ^ (0 + 1))
      ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (a b : ℤ) (_hab : a ≤ b)
    (_htor : ∀ P : CategoryTheory.ConstantCompletion.Cx
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := smallModelComparisonEtaleTopology.{u, v} X)
        (R := CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) P →
      Nonempty ((CategoryTheory.ConstantCompletion.Q
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)).obj P ≅ C) →
      ∀ (N : CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0))
        (q : ℤ), q < a ∨ b < q →
        IsZero (adicResidueTensorCohomology.{max v (u + 1)}
          (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X)
            A J 0) P N q))
    (_hres : Nonempty
      ((CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X)
          A J 0)).obj M ≅
        (adicResidueComparison.{u, v} X (A ⧸ J ^ (0 + 1))).obj C)) :
    ∃ S : Sieve ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj
        (⊤_ X.ProEt)),
      S ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ (U : coefficientProEtaleSiteModel.{u, v} X)
        (f : U ⟶ (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj
          (⊤_ X.ProEt)), S f →
        ∃ (V : coefficientProEtaleSiteModel.{u, v} X)
          (R : AdicResidueLocalDerived.{u, v} X J V ⥤
            AdicResidueLocalDerived.{u, v} X J U)
          (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ),
          P.IsStrictlyGE c ∧ P.IsStrictlyLE d ∧
          (∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) ∧
          IsAffine ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj V).left ∧
          AdicResidueSliceWeaklyContractible.{u, v} X V ∧
          let B := CategoryTheory.ConstantCompletion.completed
            (coefficientProEtaleModelTopology.{u, v} X) A J
          let T := (adicResidueRestriction B V).obj (adicResidueConstantPerfect X J P)
          let L := (adicResidueRestriction B V).obj M
          Nonempty (R.obj L ≅ (adicResidueRestriction B U).obj M) ∧
          Nonempty (R.obj T ≅ (adicResidueRestriction B U).obj
            (adicResidueConstantPerfect X J P)) ∧
          CategoryTheory.ConstantCompletion.IsComplete
            (adicResidueLocalProjection.{u, v} X J V 0) T ∧
          CategoryTheory.ConstantCompletion.IsComplete
            (adicResidueLocalProjection.{u, v} X J V 0) L ∧
          ∀ n : ℕ, Nonempty
            ((adicResidueLocalReduction.{u, v} X J V n).obj T ≅
              (adicResidueLocalReduction.{u, v} X J V n).obj L) := by
  classical
  obtain ⟨I, V, f, hcover, hmodels⟩ := adicResidue_finite_reduction_model_family.{u, v}
    X J M _hcomplete C _hbounded _hlisse a b _hab _htor _hres
  have hrestrict := adicResidue_slice_completeness.{u, v} X J
  refine ⟨Sieve.ofArrows V f, hcover, ?_⟩
  intro U g hg
  obtain ⟨i, r, _⟩ := Sieve.ofArrows.exists hg
  obtain ⟨hAffine, hWeak, P, c, d, hc, hd, hP, hfinite⟩ := hmodels i
  let B := CategoryTheory.ConstantCompletion.completed
    (coefficientProEtaleModelTopology.{u, v} X) A J
  obtain ⟨R, ⟨e⟩⟩ := adicResidue_restriction_factor B r
  exact ⟨V i, R, P, c, d, hc, hd, hP, hAffine, hWeak, ⟨e.app M⟩,
    ⟨e.app (adicResidueConstantPerfect X J P)⟩, adicResidue_constant_complete X J P hP (V i),
    hrestrict M _hcomplete (V i), hfinite⟩

end AlgebraicGeometry.Scheme
