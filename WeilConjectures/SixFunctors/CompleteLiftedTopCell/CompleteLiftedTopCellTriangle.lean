/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
import all WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Supporting.StrictDvrReductionTriangles
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedEpimorphicTopDerivedLimit
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SixFunctors.Sf.SfWeaklyContractibleProjective
import WeilConjectures.ProperBaseChange.BoundedAboveFlatSheafKFlatSupplement
import all WeilConjectures.SixFunctors.Supporting.ProjectiveCohomologySplitModel
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.SixFunctors.Completed.CompletedFreeCellOrdinaryLimit
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomExactUniverses
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement

/-! # Lifting a prescribed top residue basis

Source: Stacks Project, proetale.tex, Tag 09C3, final induction paragraph
(blueprint: lem-sf-complete-lifted-top-cell-triangle).

The free cell is the existing single complex in degree b, namely P[-b]. The residue
identification is normalized by the actual coefficient quotient on its generators.
The scheme universe t and coefficient universe u are independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CompleteLiftedTopCell

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{t})

/-- The standard rank-r residue module, including the empty product, which is zero.
Source: Stacks Tag 09C3 (blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
abbrev residueFree (r : ℕ) : scalarReductionTarget l E T 0 :=
  ∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0)

/-- The residue free cell in degree b, i.e. k^r[-b].
Source: Stacks Tag 09C3 (blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
abbrev residueCell (r : ℕ) (b : ℤ) :=
  (DerivedCategory.singleFunctor (scalarReductionTarget l E T 0) b).obj
    (residueFree l E T r)

/-- The coefficient quotient on each standard generator of the finite free module.
Restriction preserves products; its canonical product comparison identifies the target.
Source: Stacks Tag 09C3 (blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
def freeQuotient (r : ℕ) :
    (∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) ⟶
        (scalarReductionRestriction l E T 0).obj (residueFree l E T r) :=
  let := scalarReductionRestrictionLimits l E T 0
  Limits.Pi.map (fun _ : Fin r ↦ CompletedCoefficientFree.quotientProjection l E T 0) ≫
    inv (piComparison (scalarReductionRestriction l E T 0)
      (fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0)))

/-- The canonical free-cell quotient in the completed-coefficient derived category.
Source: Stacks Tag 09C3 (blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
def freeCellQuotient (r : ℕ) (b : ℤ) :
    DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b) ⟶
      (scalarReductionDerivedRestriction l E T 0).obj (residueCell l E T r b) :=
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  (DerivedCategory.singleFunctor (scalarReductionSource l E T) b).map
      (freeQuotient l E T r) ≫
    ((scalarReductionRestriction l E T 0).mapDerivedCategorySingleFunctor b).inv.app
      (residueFree l E T r)

/-- The actual top cohomology reduction, with the exact restriction comparison.
Source: Stacks Tags 06YY and 09C3
(blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
def topReduction (M : DerivedCategory (scalarReductionSource l E T)) (b : ℤ) :
    (DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).obj M ⟶
      (scalarReductionRestriction l E T 0).obj
        ((DerivedCategory.homologyFunctor (scalarReductionTarget l E T 0) b).obj
          ((scalarReductionDerivedExtension l E T 0).obj M)) :=
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  (DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).map
      (CompletedCoefficientFree.reductionMap l E T 0 M) ≫
    ((scalarReductionRestriction l E T 0).mapDerivedCategoryHomologyFunctorIso b).inv.app
      ((scalarReductionDerivedExtension l E T 0).obj M)

/-- The existing Tor-amplitude predicate on an actual slice of the small site.
All size and localization instances are supplied canonically, not assumed of M.
Source: Stacks Tags 08FZ and 09C3
(blueprint: lem-sf-complete-lifted-top-cell-triangle). -/
def residueTorTest (M : DerivedCategory (scalarReductionSource l E T))
    (a b : ℤ) (V : T.ProEt) : Prop :=
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  letI : EssentiallySmall.{max u (t + 1)} (Over V) := essentiallySmallSelf _
  letI := scalarReductionTargetDerived.{t, u} l E T 0
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    ((integralCoefficientSheaf l E T 0).over V))
  let := HasDerivedCategory.standard (ringedSiteModules.{max u (t + 1)}
    ((sheafCompose ((ProEt.topology T).over V)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((integralCoefficientCommRingSheaf l E T 0).over V)))
  HasRingedSiteTorAmplitudeOfUniverses.{t + 1, t, max u (t + 1)}
    ((integralCoefficientCommRingSheaf l E T 0).over V)
    ((ringedDerivedRestrictionGeneral.{t + 1, t, max u (t + 1), max u (t + 1)}
      (integralCoefficientSheaf l E T 0) V).obj
        ((scalarReductionDerivedExtension l E T 0).obj M)) a b

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

-- Prefer the same standard localizations used by the scalar-reduction functors.
attribute [local instance 3000] scalarReductionSourceDerived scalarReductionTargetDerived

private theorem tensor_unit_cohomology
    {C : Type (t + 1)} [Category.{t} C] [EssentiallySmall.{max u (t + 1)} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max u (t + 1)})
    [HasSheafify J AddCommGrpCat.{max u (t + 1)}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)}]
    [HasDerivedCategory (SheafOfModules.{max u (t + 1)}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (K : DerivedCategory (SheafOfModules.{max u (t + 1)}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    Nonempty ((SheafOfModules.siteDerivedTensorIndependentCoefficients J R).obj
      (K, (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ≅ K) := by
  let A := SheafOfModules.KFlatFixedTensor.Modules R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let U := (CochainComplex.singleFunctor A 0).obj (MonoidalCategory.tensorUnit A)
  have huf (i : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R) (U.X i) := by
    have hf : ObjectProperty.flat (U.X i) := by
      by_cases hi : i = 0
      · subst i
        exact ObjectProperty.prop_of_iso _
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm
          (ObjectProperty.prop_unit ObjectProperty.flat)
      · exact ObjectProperty.prop_of_isZero _
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hf.2
  have hu : CochainComplex.IsKFlatIndependentCoefficients (R := R) U :=
    SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R U 0 huf
  obtain ⟨P, q, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := R) (DerivedCategory.Q.objPreimage K)
  let := hq
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hpf (i : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X i) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R _).symm (hf i)
  exact ⟨(SheafOfModules.siteDerivedTensorIndependentCoefficients J R).mapIso
      (e.symm.prod (Iso.refl _)) ≪≫
    (SheafOfModules.KFlatFixedTensor.representativeIso R P U hp hu hpf huf).symm ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫ e⟩

private theorem residue_cohomology_bounds
    (M : DerivedCategory (scalarReductionSource l E T)) (a b : ℤ)
    (hTor : ∀ V : T.ProEt, residueTorTest l E T M a b V) (j : ℤ)
    (hj : j < a ∨ b < j) :
    IsZero ((DerivedCategory.homologyFunctor (scalarReductionTarget l E T 0) j).obj
      ((scalarReductionDerivedExtension l E T 0).obj M)) := by
  let R := integralCoefficientSheaf l E T 0
  let V : T.ProEt := ProEt.mk (𝟙 T)
  let F := SheafOfModules.overFunctor.{max u (t + 1)} R V
  let : F.Additive :=
    (ringedOverFunctor_exactGeneral.{t + 1, t, max u (t + 1), max u (t + 1)} R V).1
  let : PreservesFiniteLimits F :=
    (ringedOverFunctor_exactGeneral.{t + 1, t, max u (t + 1), max u (t + 1)} R V).2.1
  let : PreservesFiniteColimits F :=
    (ringedOverFunctor_exactGeneral.{t + 1, t, max u (t + 1), max u (t + 1)} R V).2.2
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (R.over V))
  let := HasDerivedCategory.standard (ringedSiteModules.{max u (t + 1)}
    ((sheafCompose ((ProEt.topology T).over V)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((integralCoefficientCommRingSheaf l E T 0).over V)))
  let : EssentiallySmall.{max u (t + 1)} (Over V) := essentiallySmallSelf _
  let K := (scalarReductionDerivedExtension l E T 0).obj M
  have ht := hTor V
  obtain ⟨e⟩ := tensor_unit_cohomology.{t, u}
    ((integralCoefficientCommRingSheaf l E T 0).over V) (F.mapDerivedCategory.obj K)
  have hz := ht.2 (SheafOfModules.unit (R.over V)) j hj
  have hz' : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (F.mapDerivedCategory.obj K)) :=
    hz.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso e).symm
  have hf : IsZero (F.obj ((DerivedCategory.homologyFunctor _ j).obj K)) :=
    hz'.of_iso ((F.mapDerivedCategoryHomologyFunctorIso j).app K)
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  have hh := hf.eq_zero_of_src (𝟙 _)
  have hh' := congrArg (fun f ↦ f.val.app
    (op (Over.mk (MorphismProperty.Over.homMk W.unop.hom (Category.comp_id _)
      : W.unop ⟶ V)))) hh
  exact hh'

attribute [local irreducible] unrestrictedIntegralReductionExistence
  integralReductionExistence integralReductionDerivedExistence
  unrestrictedTowerUnit unrestrictedTowerTransition unrestrictedTowerResolutionIso
  unrestrictedTowerFiniteComparison unrestrictedTowerComparison
  strictDvrReductionComparison

private theorem complete_bounds
    (M : DerivedCategory (scalarReductionSource l E T))
    (hcomplete : IsDerivedCompleteUnrestricted l E T M)
    (a b : ℤ) (hab : a ≤ b)
    (hTor : ∀ V : T.ProEt, residueTorTest l E T M a b V) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E T) j).obj M) := by
  classical
  let K := M
  let X := T
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} X
  obtain ⟨D, hl, P₀, G, q, hq, e₀, hprod, δ₀, hlim⟩ := hcomplete
  obtain ⟨P, e, hP, hflat, c, hc, i, hi, htri⟩ := strictDvrReductionTriangles.{t, u} l E X K
  have hres : ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) j).obj
        (strictDvrDerivedReduction l E X K 0)) := by
    intro j hj
    have hz := residue_cohomology_bounds l E X K a b hTor j hj
    exact ((scalarReductionRestriction l E X 0).map_isZero hz).of_iso
      (((scalarReductionRestriction l E X 0).mapDerivedCategoryHomologyFunctorIso j).symm.app _)
  have hbounds : ∀ (n : ℕ) (j : ℤ), j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) j).obj
        (strictDvrDerivedReduction l E X K n)) := by
    intro n
    induction n with
    | zero => exact hres
    | succ n hn =>
      obtain ⟨hz, hex, δ, hT⟩ := htri n
      intro j hj
      exact (DerivedCategory.HomologySequence.exact₂ _ hT j).isZero_of_both_isZero
        (hres j hj) (hn j hj)
  have htop : ∀ n : ℕ, Epi
      ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) b).map
        (strictDvrDerivedQuotientTransition l E X P hP e n)) := by
    intro n
    obtain ⟨hz, hex, δ, hT⟩ := htri n
    exact (DerivedCategory.HomologySequence.exact₃ _ hT b (b + 1) rfl).epi_f
      ((hres (b + 1) (Or.inr (by omega))).eq_zero_of_tgt _)
  let C := scalarReductionSource l E X
  let Q := DerivedCategory.Q (C := C)
  let H := DerivedCategory.homologyFunctor C
  obtain ⟨T, s, hs, t, hst⟩ := DerivedCategory.right_fac (e.hom ≫ e₀.inv)
  let : IsIso (Q.map s) := hs
  have ht : Q.map t = Q.map s ≫ e.hom ≫ e₀.inv := by
    rw [hst, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have : IsIso (Q.map t) := by rw [ht]; infer_instance
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hs
  have : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance
  obtain ⟨S, r, hS, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max u (t + 1), t + 1, t}
      (R := completedIntegralCommRingSheafUnrestricted l E X) T
  have : QuasiIso r := hr
  have hsr : CochainComplex.IsKFlatResolutionIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E X) (r ≫ s) :=
    ⟨inferInstance, hS⟩
  have htr : CochainComplex.IsKFlatResolutionIndependentCoefficients.{t + 1, t, max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E X) (r ≫ t) :=
    ⟨inferInstance, hS⟩
  let c (n : ℕ) :=
    (unrestrictedTowerComparison.{t, u} l E X n (r ≫ s) (𝟙 P) hsr
      ⟨inferInstance, hP⟩).symm ≪≫
      unrestrictedTowerComparison.{t, u} l E X n (r ≫ t) q htr hq
  have hct (n : ℕ) :
      Q.map (unrestrictedTowerTransition l E X P n) ≫ (c n).hom =
        (c (n + 1)).hom ≫ Q.map (integralTowerTransition l E X D hl P₀ n) := by
    have h₁ := (unrestrictedReductionTowerWellDefined.{t, u} l E X (r ≫ s) (𝟙 P)
      hsr ⟨inferInstance, hP⟩).2 n
    have h₂ := (unrestrictedReductionTowerWellDefined.{t, u} l E X (r ≫ t) q htr hq).2 n
    rw [integralTowerTransition_eq]
    dsimp only [c, Iso.trans_hom, Iso.symm_hom]
    apply (cancel_epi
      (unrestrictedTowerComparison.{t, u} l E X (n + 1) (r ≫ s) (𝟙 P)
        hsr ⟨inferInstance, hP⟩).hom).mp
    dsimp only [Q]
    simp only [← Category.assoc, ← h₁, Iso.hom_inv_id]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp] using h₂
  have hzP (n : ℕ) (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((H j).obj (Q.obj (unrestrictedTowerComplex l E X n P))) :=
    (hbounds n j hj).of_iso ((H j).mapIso (strictDvrReductionComparison l E X P hP e n))
  have heP (n : ℕ) : Epi ((H b).map
      (Q.map (unrestrictedTowerTransition l E X P n))) := by
    have := htop n
    have heq : (H b).map (Q.map (unrestrictedTowerTransition l E X P n)) =
        (H b).map (strictDvrReductionComparison l E X P hP e (n + 1)).hom ≫
          (H b).map (strictDvrDerivedQuotientTransition l E X P hP e n) ≫
            (H b).map (strictDvrReductionComparison l E X P hP e n).inv := by
      simp [strictDvrDerivedQuotientTransition, ← Functor.map_comp, Category.assoc, Q]
    rw [heq]
    infer_instance
  have hz₀ (n : ℕ) (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((integralTowerComplex l E X D hl n P₀).homology j) :=
    (hzP n j hj).of_iso
      (((DerivedCategory.homologyFunctorFactors C j).app
          (integralTowerComplex l E X D hl n P₀)).symm ≪≫ ((H j).mapIso (c n)).symm)
  have he₀ (n : ℕ) :
      Epi (HomologicalComplex.homologyMap (integralTowerTransition l E X D hl P₀ n) b) := by
    have := heP n
    have heq := congrArg ((H b).map) (hct n)
    simp only [Functor.map_comp] at heq
    have : Epi ((H b).map (Q.map (integralTowerTransition l E X D hl P₀ n))) := by
      have : Epi ((H b).map (c (n + 1)).hom ≫
          (H b).map (Q.map (integralTowerTransition l E X D hl P₀ n))) := by
        rw [← heq]
        infer_instance
      exact epi_of_epi ((H b).map (c (n + 1)).hom) _
    have : Epi ((H b).map (Q.map (integralTowerTransition l E X D hl P₀ n)) ≫
        (DerivedCategory.homologyFunctorFactors C b).hom.app
          (integralTowerComplex l E X D hl n P₀)) := inferInstance
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality] at this
    exact epi_of_epi
      ((DerivedCategory.homologyFunctorFactors C b).hom.app
        (integralTowerComplex l E X D hl (n + 1) P₀)) _
  let : HasProduct (fun n : ℕ ↦ Q.obj (integralTowerComplex l E X D hl n P₀)) := hprod
  have hL : IsDerivedLimit
      (K := fun n : ℕ ↦ Q.obj (integralTowerComplex l E X D hl n P₀))
      (fun n : ℕ ↦ Q.map (integralTowerTransition l E X D hl P₀ n)) K := by
    refine ⟨Pi.lift (fun n ↦
      ((integralReductionTowerCone l E X D hl q hq).extend e₀.inv).π.app
        (Opposite.op n)), δ₀, ?_⟩
    have htower :
        (fun n : ℕ ↦ (integralReductionTower l E X D hl P₀).map
          (homOfLE n.le_succ).op) =
        (fun n : ℕ ↦ Q.map (integralTowerTransition l E X D hl P₀ n)) := by
      funext n
      exact Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [htower] at hlim
    exact hlim
  exact ProEt.bounded_epimorphic_top_derivedLimit.{t, u} X
    (completedIntegralCoefficientSheafUnrestricted l E X)
    (completedIntegralCoefficient_mul_commUnrestricted l E X)
    (fun n ↦ integralTowerComplex l E X D hl n P₀)
    (fun n ↦ integralTowerTransition l E X D hl P₀ n) K hL a b hab hz₀ he₀

private theorem topReduction_epi
    (M : DerivedCategory (scalarReductionSource l E T))
    (hc : IsDerivedCompleteUnrestricted l E T M) (a b : ℤ) (hab : a ≤ b)
    (hTor : ∀ V : T.ProEt, residueTorTest l E T M a b V) :
    Epi (topReduction l E T M b) := by
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  obtain ⟨δ, hδ⟩ :=
    (CompletedCoefficientFree.completed_coefficient_free_resolution l E T).2.2 0 M
  have hz := complete_bounds l E T M hc a b hab hTor (b + 1) (Or.inr (by omega))
  have : Epi ((DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).map
      (CompletedCoefficientFree.reductionMap l E T 0 M)) :=
    (DerivedCategory.HomologySequence.exact₃ _ hδ b (b + 1) rfl).epi_f
      (hz.eq_zero_of_tgt _)
  unfold topReduction
  infer_instance

attribute [local instance] scalarReductionExtensionAdditive
  scalarReductionRestrictionLimits scalarReductionRestrictionColimits

private theorem normalized_product_quotient
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) (R : B ⥤ A) [F.Additive] [R.Additive]
    (η : 𝟭 A ⟶ F ⋙ R) (X : A) (Y : B) (e : F.obj X ≅ Y) (p : X ⟶ R.obj Y)
    (he : η.app X ≫ R.map e.hom = p) (r : ℕ) :
    ∃ eP : F.obj (∏ᶜ fun _ : Fin r ↦ X) ≅ ∏ᶜ fun _ : Fin r ↦ Y,
      η.app _ ≫ R.map eP.hom ≫ piComparison R (fun _ : Fin r ↦ Y) =
        Limits.Pi.map (fun _ : Fin r ↦ p) := by
  let eP := PreservesProduct.iso F (fun _ : Fin r ↦ X) ≪≫
    Limits.Pi.mapIso (fun _ : Fin r ↦ e)
  refine ⟨eP, ?_⟩
  apply Limits.Pi.hom_ext
  intro i
  simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
  rw [← R.map_comp]
  have heP : eP.hom ≫ Pi.π (fun _ : Fin r ↦ Y) i =
      F.map (Pi.π (fun _ : Fin r ↦ X) i) ≫ e.hom := by
    simp only [eP, Iso.trans_hom, Category.assoc, Limits.Pi.mapIso_hom_π,
      PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  rw [heP, R.map_comp, ← Category.assoc]
  rw [← show Pi.π (fun _ : Fin r ↦ X) i ≫ η.app X =
    η.app _ ≫ R.map (F.map (Pi.π (fun _ : Fin r ↦ X) i)) from η.naturality _]
  simpa only [Functor.id_map, Category.assoc] using congrArg
    (fun f ↦ Pi.π (fun _ : Fin r ↦ X) i ≫ f) he

private theorem ordinary_free_reduction (r : ℕ) :
    ∃ e : (scalarReductionExtension l E T 0).obj
        (∏ᶜ fun _ : Fin r ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) ≅
        residueFree l E T r,
      (scalarReductionExtension_adjunction l E T 0).choose.unit.app _ ≫
        (scalarReductionRestriction l E T 0).map e.hom = freeQuotient l E T r := by
  let X := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
  let Y := SheafOfModules.unit (integralCoefficientSheaf l E T 0)
  let e₁ := (extensionUnit_normalized l E T 0).choose
  have he₁ := (extensionUnit_normalized l E T 0).choose_spec
  let H := @normalized_product_quotient
    (scalarReductionSource l E T) (scalarReductionTarget l E T 0) _ _ _ _
    (scalarReductionExtension l E T 0) (scalarReductionRestriction l E T 0)
    (scalarReductionExtensionAdditive l E T 0) inferInstance
  have hp := H (scalarReductionExtension_adjunction l E T 0).choose.unit X Y e₁
    (coefficientUnitProjection l E T 0) he₁ r
  obtain ⟨e, he⟩ := hp
  refine ⟨e, ?_⟩
  let : PreservesFiniteProducts (scalarReductionRestriction l E T 0) := inferInstance
  let : IsIso (piComparison (scalarReductionRestriction l E T 0)
    (fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0))) :=
      inferInstance
  apply (cancel_mono (piComparison (scalarReductionRestriction l E T 0)
    (fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0)))).1
  simpa only [X, Y, freeQuotient, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, coefficientUnitProjection,
    CompletedCoefficientFree.quotientProjection, CompletedCoefficientFree.residueModule] using he

private theorem complete_local_iff (K : IntegralOnSlice.D l E T none) :
    IsDerivedCompleteUnrestricted l E T K ↔
      IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T) K := by
  classical
  obtain ⟨P₀, q, hP₀, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := IntegralOnSlice.ring l E T none) (DerivedCategory.Q.objPreimage K)
  let : QuasiIso q := hq
  let P : (IntegralOnSlice.Good l E T none).FullSubcategory :=
    ⟨P₀, hP₀, fun i ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (IntegralOnSlice.ring l E T none) _).symm
        (hflat i)⟩
  let e : DerivedCategory.Q.obj P.obj ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  exact (roosIntrinsicCompletenessEquivalence p l (by omega) E T d hd K P e).out 0 1

private theorem complete_cone (Δ : Triangle (DerivedCategory (scalarReductionSource l E T)))
    (hΔ : Δ ∈ distTriang _) (h₁ : IsDerivedCompleteUnrestricted l E T Δ.obj₁)
    (h₂ : IsDerivedCompleteUnrestricted l E T Δ.obj₂) :
    IsDerivedCompleteUnrestricted l E T Δ.obj₃ := by
  apply (complete_local_iff l E T Δ.obj₃).mpr
  have h₁' := (complete_local_iff l E T Δ.obj₁).mp h₁
  have h₂' := (complete_local_iff l E T Δ.obj₂).mp h₂
  intro U s hs
  let : HasSheafify (IntegralOnSlice.topology T (some U))
      CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  let R := IntegralOnSlice.rings l E T none
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (R.over U))
  let F := SheafOfModules.overFunctor.{max u (t + 1)} R U
  let : PreservesFiniteLimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).1
  let : PreservesFiniteColimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).2
  let A := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalizationOfUniverses (IntegralOnSlice.ring l E T (some U)) s)
  let H := (Functor.curry.obj (IntegralOnSlice.hom l E T (some U))).obj (op A)
  obtain ⟨hshift, htri⟩ :=
    (CategoryTheory.RingedHomUniverses.ringedInternalHom_exact
      (IntegralOnSlice.topology T (some U)) (IntegralOnSlice.ring l E T (some U))).2 A
  let : H.CommShift ℤ := hshift
  let : H.IsTriangulated := htri
  let G := F.mapDerivedCategory ⋙ H
  have e (K : IntegralOnSlice.D l E T none) :
      IntegralPrincipalCone.localTest l E T K U s ≅ G.obj K :=
    (IntegralOnSlice.hom l E T (some U)).mapIso
      ((Iso.refl _).prod (SheafOfModules.overFunctor_derivedRestrictionIso R U K))
  exact ((Pretriangulated.Triangle.isZero₃_of_isZero₁₂ _
    (G.map_distinguished Δ hΔ) ((e Δ.obj₁).isZero_iff.mp (h₁' U s hs))
      ((e Δ.obj₂).isZero_iff.mp (h₂' U s hs)))).of_iso (e Δ.obj₃)

private theorem normalized_homology
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (P : C) (S : D) (b : ℤ) (K : DerivedCategory D)
    (β : (DerivedCategory.singleFunctor C b).obj P ⟶ R.mapDerivedCategory.obj K)
    (e : K ≅ (DerivedCategory.singleFunctor D b).obj S) (q : P ⟶ R.obj S)
    (he : β ≫ R.mapDerivedCategory.map e.hom =
      (DerivedCategory.singleFunctor C b).map q ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app S) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).inv.app P ≫
        (DerivedCategory.homologyFunctor C b).map β ≫
        (R.mapDerivedCategoryHomologyFunctorIso b).inv.app K =
      q ≫ R.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso D b).inv.app S ≫
        (DerivedCategory.homologyFunctor D b).map e.inv) := by
  let HB := DerivedCategory.homologyFunctor C b
  let Hk := DerivedCategory.homologyFunctor D b
  let εB := DerivedCategory.singleFunctorCompHomologyFunctorIso C b
  let εk := DerivedCategory.singleFunctorCompHomologyFunctorIso D b
  have hsingle := R.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor b S
  have hcompat : HB.map ((R.mapDerivedCategorySingleFunctor b).inv.app S) ≫
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app
        ((DerivedCategory.singleFunctor _ b).obj S) ≫ R.map (εk.hom.app S) =
        (εB.hom.app (R.obj S)) := by
    apply (cancel_epi (HB.map ((R.mapDerivedCategorySingleFunctor b).hom.app S))).1
    rw [← HB.map_comp_assoc, Iso.hom_inv_id_app, HB.map_id, Category.id_comp]
    apply (cancel_epi ((R.mapDerivedCategoryHomologyFunctorIso b).hom.app
      ((DerivedCategory.singleFunctor _ b).obj S))).1
    rw [Iso.hom_inv_id_app_assoc]
    exact hsingle.symm
  have hq : εB.inv.app P ≫
      HB.map ((DerivedCategory.singleFunctor C b).map q ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app S) ≫
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app
        ((DerivedCategory.singleFunctor _ b).obj S) ≫ R.map (εk.hom.app S) =
      q := by
    rw [HB.map_comp]
    simp only [Category.assoc]
    rw [hcompat]
    have hh := εB.hom.naturality (q)
    change HB.map ((DerivedCategory.singleFunctor _ b).map _) ≫ εB.hom.app _ =
      εB.hom.app P ≫ q at hh
    exact (congrArg (fun f ↦ εB.inv.app P ≫ f) hh).trans
      (Iso.inv_hom_id_app_assoc εB P _)
  have hn := (R.mapDerivedCategoryHomologyFunctorIso b).inv.naturality e.hom
  change HB.map (R.mapDerivedCategory.map e.hom) ≫
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app
        ((DerivedCategory.singleFunctor _ b).obj S) =
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app _ ≫ R.map (Hk.map e.hom) at hn
  apply (cancel_mono (R.map (Hk.map e.hom ≫ εk.hom.app S))).1
  change (εB.inv.app P ≫ (HB.map β ≫ (R.mapDerivedCategoryHomologyFunctorIso b).inv.app K)) ≫
      R.map (Hk.map e.hom ≫ εk.hom.app S) =
    (q ≫ R.map (εk.inv.app S ≫ Hk.map e.inv)) ≫
      R.map (Hk.map e.hom ≫ εk.hom.app S)
  simp only [Category.assoc]
  rw [← R.map_comp]
  have hi : (εk.inv.app S ≫ Hk.map e.inv) ≫ (Hk.map e.hom ≫ εk.hom.app S) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (Hk.map e.inv),
      ← Hk.map_comp, e.inv_hom_id, Hk.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rw [hi]
  erw [R.map_id, Category.comp_id]
  rw [R.map_comp]
  rw [← reassoc_of% hn]
  rw [← HB.map_comp_assoc, he]
  exact hq

private theorem quotient_epi (r : ℕ) : Epi (freeQuotient l E T r) := by
  let := scalarReductionRestrictionLimits l E T 0
  have : Epi (CompletedCoefficientFree.quotientProjection l E T 0) :=
    (CompletedCoefficientFree.coefficient_shortExact l E T 0).epi_g
  let : HasFiniteBiproducts (SheafOfModules.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E T)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : ∀ _ : Fin r, Epi (CompletedCoefficientFree.quotientProjection l E T 0) :=
    fun _ ↦ inferInstance
  change Epi (Limits.Pi.map
    (fun _ : Fin r ↦ CompletedCoefficientFree.quotientProjection l E T 0) ≫
      inv (piComparison (scalarReductionRestriction l E T 0)
        (fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0))))
  have hπ : IsIso (piComparison (scalarReductionRestriction l E T 0)
    (fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0))) :=
      inferInstance
  have hmap : Epi (Limits.Pi.map
      (fun _ : Fin r ↦ CompletedCoefficientFree.quotientProjection l E T 0)) :=
    Limits.Pi.map_epi _
  infer_instance

private theorem single_unit_extension
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
    (η : 𝟭 C ⟶ F ⋙ R) (X : C) (Y : D) (e : F.obj X ≅ Y) (p : X ⟶ R.obj Y)
    (he : η.app X ≫ R.map e.hom = p) (b : ℤ) :
    (NatTrans.mapHomologicalComplex η (.up ℤ)).app
        ((CochainComplex.singleFunctor C b).obj X) ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) b).hom.app X) ≫
          (CochainComplex.singleFunctor D b).map e.hom) ≫
      (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) b).hom.app Y =
        (CochainComplex.singleFunctor C b).map p := by
  dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors] at *
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc]
  simp only [Iso.inv_hom_id_assoc, R.map_comp, Category.assoc]
  have hn := η.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) b X).hom
  change (HomologicalComplex.singleObjXSelf (.up ℤ) b X).hom ≫ η.app X =
    η.app _ ≫ R.map (F.map (HomologicalComplex.singleObjXSelf (.up ℤ) b X).hom) at hn
  rw [← reassoc_of% hn]
  erw [reassoc_of% he]
  simp only [← R.map_comp_assoc, Iso.inv_hom_id, R.map_id, Category.id_comp]

private theorem derived_single_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (η : 𝟭 C ⟶ F ⋙ R) (X : C) (Y : D) (e : F.obj X ≅ Y) (p : X ⟶ R.obj Y)
    (he : η.app X ≫ R.map e.hom = p) (b : ℤ)
    (K : DerivedCategory D)
    (c : K ≅ DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor C b).obj X)))
    (β : (DerivedCategory.singleFunctor C b).obj X ⟶ R.mapDerivedCategory.obj K)
    (hc : β ≫ R.mapDerivedCategory.map c.hom ≫ R.mapDerivedCategoryFactors.hom.app _ =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex η (.up ℤ)).app
        ((CochainComplex.singleFunctor C b).obj X))) :
    let eC := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) b).app X ≪≫
      (CochainComplex.singleFunctor D b).mapIso e
    β ≫ R.mapDerivedCategory.map (c.hom ≫ DerivedCategory.Q.map eC.hom) =
      (DerivedCategory.singleFunctor C b).map p ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app Y := by
  intro eC
  apply (cancel_mono ((R.mapDerivedCategorySingleFunctor b).hom.app Y)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  have hs : (R.mapDerivedCategorySingleFunctor b).hom.app Y =
      R.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor D b).obj Y) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) b).hom.app Y) := by
    simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
      Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Iso.refl_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
      Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
    erw [Category.id_comp]
  rw [hs, Functor.map_comp]
  simp only [Category.assoc]
  have hn := R.mapDerivedCategoryFactors.hom.naturality eC.hom
  change R.mapDerivedCategory.map (DerivedCategory.Q.map eC.hom) ≫
    R.mapDerivedCategoryFactors.hom.app _ = R.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map eC.hom) at hn
  rw [reassoc_of% hn]
  erw [reassoc_of% hc, Category.comp_id]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  exact congrArg DerivedCategory.Q.map (single_unit_extension F R η X Y e p he b)

private theorem free_reduction (r : ℕ) (b : ℤ) :
    ∃ e : (scalarReductionDerivedExtension l E T 0).obj
        (DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b)) ≅
          residueCell l E T r b,
      CompletedCoefficientFree.reductionMap l E T 0
          (DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b)) ≫
        (scalarReductionDerivedRestriction l E T 0).map e.hom =
          freeCellQuotient l E T r b := by
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  let F := scalarReductionExtension l E T 0
  let : F.Additive := scalarReductionExtensionAdditive l E T 0
  let R := scalarReductionRestriction l E T 0
  let B : scalarReductionSource l E T := ∏ᶜ fun _ : Fin r ↦
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
  let P := CompletedCoefficientFree.freeCell l E T r b
  let c := CompletedCoefficientFree.reductionComplexCounit l E T 0 P
  have : IsIso c := CompletedCoefficientFree.reductionComplexCounit_isIso l E T 0 P
    (CompletedCoefficientFree.freeCell_good l E T r b).1
  obtain ⟨e₀, he₀⟩ := ordinary_free_reduction l E T r
  let eC := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) b).app B ≪≫
    (CochainComplex.singleFunctor _ b).mapIso e₀
  let e := asIso c ≪≫ DerivedCategory.Q.mapIso eC
  refine ⟨e, ?_⟩
  have hc := CompletedCoefficientFree.reductionMap_complex l E T 0 P
    (CompletedCoefficientFree.freeCell_good l E T r b).1
  exact @derived_single_normalization
    (scalarReductionSource l E T) (scalarReductionTarget l E T 0) _ _ _ _
    (scalarReductionSourceDerived l E T) (scalarReductionTargetDerived l E T 0) F R
    (scalarReductionExtensionAdditive l E T 0) inferInstance
    (scalarReductionRestrictionLimits l E T 0) (scalarReductionRestrictionColimits l E T 0)
    (scalarReductionExtension_adjunction l E T 0).choose.unit B _ e₀ _ he₀ b _
    (asIso c) (CompletedCoefficientFree.reductionMap l E T 0 _) hc

private theorem projective_normalized_lift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (R : D ⥤ C) [R.Faithful] [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (η : 𝟭 _ ⟶ F ⋙ R.mapDerivedCategory) (P : C) [Projective P]
    (S : D) (b : ℤ) (q : P ⟶ R.obj S) [Epi q]
    (e : F.obj ((DerivedCategory.singleFunctor C b).obj P) ≅
      (DerivedCategory.singleFunctor D b).obj S)
    (he : η.app _ ≫ R.mapDerivedCategory.map e.hom =
      (DerivedCategory.singleFunctor C b).map q ≫
        (R.mapDerivedCategorySingleFunctor b).inv.app S)
    (M : DerivedCategory C)
    (θ : S ≅ (DerivedCategory.homologyFunctor D b).obj (F.obj M))
    (hEpi : Epi ((DerivedCategory.homologyFunctor C b).map (η.app M) ≫
      (R.mapDerivedCategoryHomologyFunctorIso b).inv.app (F.obj M))) :
    ∃ f : (DerivedCategory.singleFunctor C b).obj P ⟶ M,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D b).inv.app S ≫
        (DerivedCategory.homologyFunctor D b).map (e.inv ≫ F.map f) = θ.hom := by
  let HB := DerivedCategory.homologyFunctor C b
  let Hk := DerivedCategory.homologyFunctor D b
  let εB := DerivedCategory.singleFunctorCompHomologyFunctorIso C b
  let εk := DerivedCategory.singleFunctorCompHomologyFunctorIso D b
  let top (N : DerivedCategory C) := HB.map (η.app N) ≫
    (R.mapDerivedCategoryHomologyFunctorIso b).inv.app (F.obj N)
  have hn {N N' : DerivedCategory C} (f : N ⟶ N') :
      HB.map f ≫ top N' = top N ≫ R.map (Hk.map (F.map f)) := by
    have hη := η.naturality f
    have hH := (R.mapDerivedCategoryHomologyFunctorIso b).inv.naturality (F.map f)
    change f ≫ η.app N' = η.app N ≫ R.mapDerivedCategory.map (F.map f) at hη
    dsimp only [top]
    rw [← Category.assoc, ← HB.map_comp, hη, HB.map_comp, Category.assoc]
    simpa only [HB, Hk, Functor.comp_map, Functor.id_obj, Category.assoc] using
      congrArg (fun g ↦ HB.map (η.app N) ≫ g) hH
  let : Epi (top M) := hEpi
  let x := Projective.factorThru (q ≫ R.map θ.hom) (top M)
  have hx : x ≫ top M = q ≫ R.map θ.hom := Projective.factorThru_comp _ _
  obtain ⟨f, hf⟩ := (WeilConjectures.sfProjectiveHomologyBijective P M b).2
    (εB.hom.app P ≫ x)
  change HB.map f = εB.hom.app P ≫ x at hf
  have hf' : εB.inv.app P ≫ HB.map f = x := by rw [hf, Iso.inv_hom_id_app_assoc]
  have hnorm := normalized_homology R P S b _ (η.app _) e q he
  change εB.inv.app P ≫ top _ = q ≫ R.map (εk.inv.app S ≫ Hk.map e.inv) at hnorm
  refine ⟨f, ?_⟩
  apply R.map_injective
  apply (cancel_epi q).1
  calc
    _ = (q ≫ R.map (εk.inv.app S ≫ Hk.map e.inv)) ≫ R.map (Hk.map (F.map f)) := by
      change q ≫ R.map (εk.inv.app S ≫ Hk.map (e.inv ≫ F.map f)) = _
      simp only [Hk.map_comp, R.map_comp, Category.assoc]
    _ = (εB.inv.app P ≫ top _) ≫ R.map (Hk.map (F.map f)) :=
      congrArg (fun g ↦ g ≫ R.map (Hk.map (F.map f))) hnorm.symm
    _ = (εB.inv.app P ≫ HB.map f) ≫ top M := by
      rw [Category.assoc, ← hn, ← Category.assoc]
    _ = _ := by rw [hf', hx]

private theorem restriction_faithful
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{v}} (φ : R ⟶ S) :
    (SheafOfModules.restrictScalars.{v} φ).Faithful where
  map_injective := by
    intro M N f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun k ↦ (k.val.app U) x) h

/-- A prescribed top residue basis lifts to a finite free cell with complete cone.
Source: Stacks Project, proetale.tex, Tag 09C3, final induction paragraph
(blueprint: lem-sf-complete-lifted-top-cell-triangle).

Proof:
1. Test the residue Tor interval with the tensor unit on the terminal slice. The
   right unitor and faithful slice restriction give the residue cohomology bounds.
2. Propagate these bounds through the strict DVR quotient triangles. Compare this
   tower with the chosen complete tower by a common K-flat roof. The bounded
   epimorphic derived-limit theorem gives H^(b+1)(M)=0.
3. The canonical reduction triangle of completed_coefficient_free_resolution and
   its homology sequence make topReduction epic. Exact terminal evaluation makes
   it surjective on sections; weak contractibility makes the finite free P projective.
4. Normalize extension of the coefficient unit, then its finite products, by the
   actual quotient maps. The K-flat counit computes reduction of the single free
   complex. Its unit square is exactly freeCellQuotient.
5. Lift the prescribed homology map using projectivity of P and the bijection from
   maps P[-b] to maps on H^b. Naturality of the unit and the restriction-homology
   comparison give H^b(f_1)=theta after cancelling the epic coefficient quotient.
6. Complete f to a distinguished triangle. The free source is quotient-tower
   complete. The unit-compatible Roos/intrinsic equivalence translates completeness
   to vanishing of local principal-localization internal-Hom tests. Exact restriction
   and internal Hom preserve triangles, so the cone has the same vanishing tests.
7. The empty product is zero and its derived single complex is zero. This gives
   the rank-zero assertion; no step requires a<b or a nonempty scheme. -/
theorem complete_lifted_top_cell_triangle
    (hT : ∀ (F G : Sheaf (ProEt.topology T) (Type (max u (t + 1))))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 T)))))
    [CompactSpace T]
    (M : DerivedCategory (scalarReductionSource l E T))
    (hcomplete : IsDerivedCompleteUnrestricted l E T M)
    (a b : ℤ) (hab : a ≤ b)
    (hTor : ∀ V : T.ProEt, residueTorTest l E T M a b V)
    (r : ℕ)
    (θ : residueFree l E T r ≅
      (DerivedCategory.homologyFunctor (scalarReductionTarget l E T 0) b).obj
        ((scalarReductionDerivedExtension l E T 0).obj M)) :
    Epi (topReduction l E T M b) ∧
    Function.Surjective ((topReduction l E T M b).val.app (op (ProEt.mk (𝟙 T)))) ∧
    ∃ (f : DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b) ⟶ M)
      (L : DerivedCategory (scalarReductionSource l E T))
      (g : M ⟶ L)
      (δ : L ⟶ (DerivedCategory.Q.obj
        (CompletedCoefficientFree.freeCell l E T r b))⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang _ ∧ IsDerivedCompleteUnrestricted l E T L ∧
      ∃ e : (scalarReductionDerivedExtension l E T 0).obj
          (DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b)) ≅
            residueCell l E T r b,
        CompletedCoefficientFree.reductionMap l E T 0
            (DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b)) ≫
          (scalarReductionDerivedRestriction l E T 0).map e.hom =
            freeCellQuotient l E T r b ∧
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (scalarReductionTarget l E T 0) b).inv.app (residueFree l E T r) ≫
          (DerivedCategory.homologyFunctor (scalarReductionTarget l E T 0) b).map
            (e.inv ≫ (scalarReductionDerivedExtension l E T 0).map f) = θ.hom ∧
        (r = 0 → IsZero (DerivedCategory.Q.obj
          (CompletedCoefficientFree.freeCell l E T r b)) ∧
            ∀ f' : DerivedCategory.Q.obj
              (CompletedCoefficientFree.freeCell l E T r b) ⟶ M, f' = f) := by
  classical
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  let R := scalarReductionRestriction l E T 0
  let D := scalarReductionDerivedExtension l E T 0
  let C := scalarReductionSource l E T
  let k := scalarReductionTarget l E T 0
  let P : C := ∏ᶜ fun _ : Fin r ↦
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)
  have hepi : Epi (topReduction l E T M b) :=
    topReduction_epi l E T M hcomplete a b hab hTor
  let := hepi
  have hsurj : Function.Surjective
      ((topReduction l E T M b).val.app (op (ProEt.mk (𝟙 T)))) := by
    let ev := SheafOfModules.evaluation.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E T) (op (ProEt.mk (𝟙 T)))
    let : ev.PreservesHomology :=
      (sf_weakly_contractible_projective T hT
        (completedIntegralCommRingSheafUnrestricted l E T)).1
    exact (ModuleCat.epi_iff_surjective (ev.map (topReduction l E T M b))).mp
      inferInstance
  let : Projective P :=
    (sf_weakly_contractible_projective T hT
      (completedIntegralCommRingSheafUnrestricted l E T)).2 r
  let : R.Faithful := restriction_faithful _
  let : Epi (freeQuotient l E T r) := quotient_epi l E T r
  obtain ⟨e, he⟩ := free_reduction l E T r b
  obtain ⟨f, hθ⟩ := @projective_normalized_lift C k _ _ _ _
    (scalarReductionSourceDerived l E T) (scalarReductionTargetDerived l E T 0) R
    inferInstance inferInstance
    (scalarReductionRestrictionLimits l E T 0)
    (scalarReductionRestrictionColimits l E T 0) D
    (derivedScalarExtensionRestrictionAdjunction l E T 0).choose.unit P inferInstance
    (residueFree l E T r) b (freeQuotient l E T r) inferInstance e he M θ hepi
  obtain ⟨L, g, δ, hΔ⟩ := distinguished_cocone_triangle f
  have hcP : IsDerivedCompleteUnrestricted l E T
      (DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b)) :=
    (CompletedCoefficientFree.completed_coefficient_free_resolution l E T).2.1 r b
  refine ⟨hepi, hsurj, f, L, g, δ, hΔ,
    complete_cone l E T _ hΔ hcP hcomplete, e, he, hθ, ?_⟩
  intro hr
  subst r
  have hz : IsZero (∏ᶜ fun _ : Fin 0 ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) := by
    rw [IsZero.iff_id_eq_zero]
    apply Limits.Pi.hom_ext
    intro i
    exact Fin.elim0 i
  have hzero : IsZero (DerivedCategory.Q.obj
      (CompletedCoefficientFree.freeCell l E T 0 b)) :=
    (DerivedCategory.singleFunctor C b).map_isZero hz
  exact ⟨hzero, fun f' ↦ hzero.eq_of_src f' f⟩

end WeilConjectures.CompleteLiftedTopCell
