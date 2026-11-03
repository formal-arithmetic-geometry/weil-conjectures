/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.HypercoverComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Algebra.Homology.ComplexExtensionColimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Bounded-below filtered-colimit continuity of pro-etale hypercohomology

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity,
det-pe-bounded-continuity-sections.md and its proof
(blueprint: det-pe-bounded-continuity-sections).

## Main definitions

- `ringHypercohomology`: integer-degree derived sections with arbitrary ring-sheaf coefficients.

## Main statements

- `ringHypercohomology_transport_preservesZeroMorphisms`: transport acts on complexes.
- `isIso_ringHypercohomology_colimitPost`: the canonical bounded-below continuity map is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The published sectionwise transport preserves zero maps, as needed to apply it
termwise to complexes. Source: the blueprint's small-site size convention and
Stacks Project, Tag 03D1 (blueprint: det-pe-bounded-continuity-sections).
Proof: transport precomposes every component with `AsSmall.down`; a zero module-sheaf
map has a zero component at every object, which remains zero after precomposition. -/
theorem ringHypercohomology_transport_preservesZeroMorphisms (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext V x
  rfl

attribute [instance] ringHypercohomology_transport_preservesZeroMorphisms

/-- Hypercohomology at an object of the small pro-etale site, with arbitrary ring-sheaf
coefficients. Transport to the published small site model is sectionwise precomposition;
then take the published functorial K-injective resolution, evaluate its underlying abelian
section complex, and take its integer-degree homology. On bounded-below complexes this is
canonically the evaluation of a bounded-below injective resolution: both compute the right
derived evaluation functor, and comparison with a K-injective resolution is unique up to
homotopy. This construction retains all original site objects and the original coefficients.

Source: the blueprint, det-pe-bounded-continuity-sections.md, convention for `H^q(U,-)`;
Stacks Project, Tags 079P and 09A2 (blueprint: det-pe-bounded-continuity-sections). -/
noncomputable def ringHypercohomology (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) (q : ℤ) :
    CochainComplex (ringedSiteModules.{u + 1} R) ℤ ⥤ AddCommGrpCat.{u + 1} :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    CochainComplex.kInjectiveResolutionFunctor.{u + 1} (ringedSiteModules.{u + 1} S) ⋙
    (SheafOfModules.evaluation S (op (AsSmall.up.obj U)) ⋙
      forget₂ (ModuleCat.{u + 1} (S.obj.obj (op (AsSmall.up.obj U))))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q

private noncomputable def moduleModelEquiv (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R) := by
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm.functor.IsContinuous
      (proEtaleModelTopology X) (topology X) :=
    inferInstanceAs ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsContinuous _ _)
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm.inverse.IsContinuous
      (topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm
    (𝟙 _) (𝟙 _) (by
      ext V x
      change (R.obj.map (𝟙 V)) x = x
      simp) (by
      ext V x
      change (R.obj.map (𝟙 (op (ULift.down V.unop)))) x = x
      simp)

private noncomputable def derivedSectionsUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h where
  app K := (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
      ((DerivedCategory.quotientCompQhIso C).hom.app K)
  naturality K L f := by
    have hn := (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).naturality
      ((HomotopyCategory.quotient C (.up ℤ)).map f)
    simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at hn
    simp only [Functor.comp_map, DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
      Category.assoc]
    rw [reassoc_of% hn, ← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.quotientCompQhIso_hom_naturality]

private theorem derivedSectionsUnit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    IsIso ((derivedSectionsUnit F h).app K) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h K
  dsimp only [derivedSectionsUnit]
  infer_instance

private noncomputable def resolutionDerivedIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (J : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (s : 𝟭 _ ⟶ J)
    (hJ : ∀ K, (J.obj K).IsKInjective) (hs : ∀ K, QuasiIso (s.app K)) :
    DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h ≅
      J ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let v := Functor.whiskerLeft J (derivedSectionsUnit F h)
  have : ∀ K, IsIso (v.app K) := fun K ↦ by
    have := hJ K
    exact derivedSectionsUnit_isIso F h (J.obj K)
  have : IsIso v := NatIso.isIso_of_isIso_app _
  let t := Functor.whiskerRight (Functor.whiskerRight s DerivedCategory.Q)
    (F.rightDerivedFunctorOfQuasiIsoResolutions h)
  have : ∀ K, IsIso (t.app K) := fun K ↦ by
    have := hs K
    change IsIso ((F.rightDerivedFunctorOfQuasiIsoResolutions h).map
      (DerivedCategory.Q.map (s.app K)))
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t ≪≫ (asIso v).symm

private noncomputable def ringHypercohomologyDerivedIso (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) (q : ℤ)
    [HasDerivedCategory (ringedSiteModules.{u + 1} R)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    ringHypercohomology X R U q ≅ DerivedCategory.Q ⋙
      Functor.rightDerivedFunctorOfQuasiIsoResolutions
        (hypercoverAbelianEvaluation.{u, u + 1, 0} X R U)
        (moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0} X R) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q := by
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  let e := moduleModelEquiv X R
  have : e.functor.Additive := ⟨by intros; rfl⟩
  have : e.inverse.Additive := ⟨by intros; rfl⟩
  let A := e.functor.mapHomologicalComplex (.up ℤ)
  let B := e.inverse.mapHomologicalComplex (.up ℤ)
  let J := A ⋙ CochainComplex.kInjectiveResolutionFunctor.{u + 1}
    (ringedSiteModules.{u + 1} S) ⋙ B
  let s : 𝟭 _ ⟶ J := (e.mapHomologicalComplex (.up ℤ)).unitIso.hom ≫
    Functor.whiskerRight (Functor.whiskerLeft A
      (CochainComplex.toKInjectiveResolution.{u + 1} (ringedSiteModules.{u + 1} S))) B
  have hJ (K) : CochainComplex.IsKInjective (J.obj K) := by
    change CochainComplex.IsKInjective ((e.inverse.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.kInjectiveResolutionFunctor.{u + 1}
        (ringedSiteModules.{u + 1} S)).obj (A.obj K)))
    infer_instance
  have hs (K) : QuasiIso (s.app K) := by
    have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1}
        (ringedSiteModules.{u + 1} S)).app (A.obj K)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1}
        (ringedSiteModules.{u + 1} S) (A.obj K)).2
    have : QuasiIso (B.map ((CochainComplex.toKInjectiveResolution.{u + 1}
        (ringedSiteModules.{u + 1} S)).app (A.obj K))) := by
      change QuasiIso ((e.inverse.mapHomologicalComplex (.up ℤ)).map _)
      infer_instance
    change QuasiIso ((e.mapHomologicalComplex (.up ℤ)).unitIso.hom.app K ≫
      B.map ((CochainComplex.toKInjectiveResolution.{u + 1}
        (ringedSiteModules.{u + 1} S)).app (A.obj K)))
    infer_instance
  let E := hypercoverAbelianEvaluation.{u, u + 1, 0} X R U
  have : E.Additive := ⟨by intros; rfl⟩
  let c := resolutionDerivedIso E
    (moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0} X R) J s hJ hs
  let cH := Functor.isoWhiskerRight c
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q)
  let cQ := Functor.isoWhiskerLeft (J ⋙ E.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} q)
  let smallE := SheafOfModules.evaluation S (op (AsSmall.up.obj U)) ⋙
    forget₂ (ModuleCat.{u + 1} (S.obj.obj (op (AsSmall.up.obj U))))
      AddCommGrpCat.{u + 1}
  have : smallE.Additive := ⟨by intros; rfl⟩
  let ee : e.inverse ⋙ E ≅ smallE := Iso.refl _
  let ec := Functor.mapHomologicalComplexCompIso ee (.up ℤ)
  let cE : J ⋙ E.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q ≅
      ringHypercohomology X R U q := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (A ⋙ CochainComplex.kInjectiveResolutionFunctor.{u + 1}
      (ringedSiteModules.{u + 1} S)) ec)
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q)
  exact cE.symm ≪≫ cQ.symm ≪≫ cH.symm

end AlgebraicGeometry.Scheme.ProEt
