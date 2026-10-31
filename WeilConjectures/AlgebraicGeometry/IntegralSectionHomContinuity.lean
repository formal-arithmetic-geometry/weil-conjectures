/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.InternalHomLocalizationComparison
import all WeilConjectures.Algebra.Homology.InternalHomLocalizationComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.ConstructibleInternalHomContinuity
import all WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import all WeilConjectures.AlgebraicGeometry.IntegralCoefficientExtComparison
import all WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.Algebra.Homology.ScalarInternalHomAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory

/-! # Constructible-source continuity for the actual integral section coefficients

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
with the exact coefficient and section-module transport.
(blueprint: lem-sfb-integral-section-hom-continuity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.homComplexFunctor
  WeilConjectures.coefficientHomResolution WeilConjectures.coefficientHomResolutionIso
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence
  CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf
  CategoryTheory.InternalAbelianSheafModule.sectionScalarMap
  CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.localizationHomComplex
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
universe u v
open CategoryTheory CategoryTheory.Limits SheafOfModules Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical small Grothendieck-derived localization for section modules.
Source: Stacks 07A5, via the existing Grothendieck module-sheaf construction.
(blueprint: lem-sfb-integral-section-hom-continuity). -/
noncomputable local instance integralSectionContinuityDerived (X : Scheme.{u})
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 1, u + 1, u + 2}
        (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) R) :=
  fun R ↦ HasDerivedCategory.ofIsGrothendieckAbelian
    (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) R)

private theorem native_continuity
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (CondensedRing.supportModules
      (FiniteConstantModel.integralCoefficients l E) X))
    (hK : constantModelBoundedConstructible
      (FiniteConstantModel.integralCoefficients l E) X K) :
    HomContinuous ((CondensedRing.derivedHom
      (FiniteConstantModel.integralCoefficients l E) X).obj (op K)) := by
  let Λ := Mon.mk (FiniteConstantModel.integralCoefficients l E)
  let P : ObjectProperty (DerivedCategory (CondensedRing.supportModules Λ.X X)) :=
    NativeContinuous Λ X
  let := (nativeContinuous_closure Λ X).1
  let := (nativeContinuous_closure Λ X).2
  have hgen : ∀ (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
      (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
      (L : CondensedRing.supportModules Λ.X S), HasFiniteConstantLocalModel Λ.X S L →
      P ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek Λ.X v).obj
          ((CondensedRing.lowerStar Λ.X t).obj L))) := by
    intro V S v _ t _ _ L hL
    have : TopologicalSpace.NoetherianSpace V :=
      v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let A := (DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.lowerStar Λ.X t).obj L)
    have hA := closedModelContinuous l E Λ (Or.inl rfl) t L hL
    have hopen := openContinuous Λ X V v A hA
    exact P.prop_of_iso
      ((CondensedRing.openImmersionLowerShriek Λ.X v).mapDerivedCategorySingleFunctor 0 |>.app
        ((CondensedRing.lowerStar Λ.X t).obj L)) hopen
  exact (CondensedRing.bounded_finiteModel_generation Λ.X X P hgen K hK).1.continuity

private def fix_hom_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) (U : B ⥤ A)
    (H : Aᵒᵖ × A ⥤ A) (H' : Bᵒᵖ × B ⥤ B)
    (e : (F.op.prod (𝟭 B)) ⋙ H' ⋙ U ≅ ((𝟭 Aᵒᵖ).prod U) ⋙ H) (X : A) :
    (Functor.curry.obj H').obj (op (F.obj X)) ⋙ U ≅
      U ⋙ (Functor.curry.obj H).obj (op X) := by
  refine NatIso.ofComponents (fun N ↦ e.app (op X, N)) ?_
  intro N N' f
  have h := e.hom.naturality (Prod.mkHom (𝟙 (op X)) f)
  change U.map (H'.map (Prod.mkHom (𝟙 (op (F.obj X))) f)) ≫
      e.hom.app (op X, N') =
    e.hom.app (op X, N) ≫ H.map (Prod.mkHom (𝟙 (op X)) (U.map f))
  simpa only [Functor.comp_map, Functor.prod_map, Functor.op_map,
    Functor.id_map, unop_id, CategoryTheory.Functor.map_id, op_id] using h

private theorem continuity_scalar_equivalence
    (X : Scheme.{u})
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    [(SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a).IsEquivalence]
    (K : DerivedCategory (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X) S))
    (hc : HomContinuous
      ((Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) R)).obj
          (op ((SheafOfModules.scalarRestriction a).mapDerivedCategory.obj K)))) :
    HomContinuous
      ((Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) S)).obj (op K)) := by
  let U := SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a
  let H0 := Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
    (Scheme.ProEt.topology X) R)
  let H1 := Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
    (Scheme.ProEt.topology X) S)
  obtain ⟨M, μ, ⟨α⟩⟩ := scalarInternalHomAdjunction_exists.{u + 1, u, u, u + 1}
    (J := Scheme.ProEt.topology X)
  let F := (M.scalar a).derived
  have hU : scalarDerivedRestriction.{u + 1, u, u + 1, u + 1} a =
      U.mapDerivedCategory := by
    unfold scalarDerivedRestriction Functor.mapDerivedCategory
    rfl
  let adj : F ⊣ U.mapDerivedCategory := hU ▸ (M.scalar a).adjunction
  have : U.mapDerivedCategory.IsEquivalence := inferInstance
  have : U.mapDerivedCategory.Full := inferInstance
  have : U.mapDerivedCategory.Faithful := inferInstance
  have hεall : IsIso adj.counit := Adjunction.counit_isIso_of_R_fully_faithful adj
  have hε : IsIso (adj.counit.app K) :=
    (NatTrans.isIso_iff_isIso_app adj.counit).mp hεall K
  let qK : F.obj (U.mapDerivedCategory.obj K) ≅ K :=
    @asIso _ _ _ _ (adj.counit.app K) hε
  let z : H1.obj (op (F.obj (U.mapDerivedCategory.obj K))) ⋙ U.mapDerivedCategory ≅
      U.mapDerivedCategory ⋙ H0.obj (op (U.mapDerivedCategory.obj K)) := by
    let e := α.iso a
    dsimp only [scalarHomSource, scalarHomTarget] at e
    rw [hU] at e
    exact fix_hom_square F U.mapDerivedCategory _ _ e (U.mapDerivedCategory.obj K)
  let e : H1.obj (op K) ⋙ U.mapDerivedCategory ≅
      U.mapDerivedCategory ⋙ H0.obj (op (U.mapDerivedCategory.obj K)) :=
    Functor.isoWhiskerRight (H1.mapIso qK.op) U.mapDerivedCategory ≪≫ z
  have : U.asEquivalence.functor.Additive := inferInstanceAs U.Additive
  have : U.asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (continuous_equivalence_iff U.asEquivalence _ _ e).mpr hc

private theorem sequential_model_continuity
    {A : Type*} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    (F : DerivedCategory A ⥤ DerivedCategory A)
    (G : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (eG : DerivedCategory.Q ⋙ F ≅ G ⋙ DerivedCategory.Q) (hF : HomContinuous F)
    (D : ℕ ⥤ CochainComplex A ℤ)
    (hD : ∃ c : ℤ, ∀ n : ℕ, (D.obj n).IsStrictlyGE c) :
    IsIso (DerivedCategory.Q.map (colimit.post D G)) := by
  obtain ⟨c, hc⟩ := hD
  let j := (ULift.orderIso : ULift.{v} ℕ ≃o ℕ).equivalence.functor
  have hsmall := (continuous_model_iff _ G eG).mp hF
    (ULift.{v} ℕ) (j ⋙ D) c (fun n ↦ by
      change (DerivedCategory.Q.obj (D.obj n.down)).IsGE c
      have := hc n.down
      exact (DerivedCategory.isGE_Q_obj_iff _ c).mpr inferInstance)
  have : IsIso (DerivedCategory.Q.map (colimit.post (j ⋙ D) G)) := hsmall
  have hpre := congrArg DerivedCategory.Q.map (colimit.pre_post j D G)
  rw [Functor.map_comp, Functor.map_comp] at hpre
  have : IsIso (DerivedCategory.Q.map (colimit.pre (D ⋙ G) j) ≫
      DerivedCategory.Q.map (colimit.post D G)) := by
    rw [← hpre]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp this

/-- General-lfp constructibility implies the sequential continuity hypothesis for
ambient internal Hom in the exact section-module presentation.

Source: Bhatt--Scholze, Lemma 6.8.12; Hemo--Richarz--Scholbach, Lemma 5.3(2).
(blueprint: lem-sfb-integral-section-hom-continuity).

Proof. The quasi-compact locally Noetherian scheme has Noetherian topology. The
integral local-model comparison identifies its constructible modules with finite
constant models, in every cohomological degree. Apply constructible internal-Hom
continuity to each uniformly bounded-below sequence. The coefficient isomorphism
from the lifted spectral-norm integers to the specified algebraic-closure integers transports
both constructibility and the canonical Hom comparison. The exact internal-module
and section-module equivalence then transports the mapped colimit cocones. Exact
filtered colimits commute with cohomology, so the comparison of any functorial
complex Hom model is an isomorphism in the ordinary derived category. In particular
this applies to the existing localizationHomComplex model and its canonical map. -/
theorem integralSectionHomContinuity
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (K : DerivedCategory (scalarModules.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (ModuleObjectRingedComparison.ring (Profinite.padicIntegersRingObj l E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X)
      (((ModuleObjectRingedComparison.equivalence
        (Profinite.padicIntegersRingObj l E.1) X).inverse.mapDerivedCategory).obj K)) :
    HasLocalizationHomContinuity.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X)
      (ModuleObjectRingedComparison.ring (Profinite.padicIntegersRingObj l E.1) X) K := by
  classical
  have : IsNoetherian X := ⟨⟩
  let E0 := ULift.{u} E.1
  let : FiniteDimensional (Padic l) E0 :=
    (ULift.moduleEquiv (R := Padic l) (M := E.1)).symm.finiteDimensional
  let Λ0 := Mon.mk (FiniteConstantModel.integralCoefficients l E0)
  let Λ1 := Mon.mk (Profinite.padicIntegersRingObj l E.1)
  let eiR := (integerRingSheafIso.{u} l E).symm
  let eiAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eiR
  have : IsMonHom eiAb.hom := Sheaf.isMonHom_sheafCompose_map _ eiR.hom
  have : IsMonHom eiAb.inv := Sheaf.isMonHom_sheafCompose_map _ eiR.inv
  let ei : Λ0 ≅ Λ1 :=
    { hom := Mon.ofHom eiAb.hom
      inv := Mon.ofHom eiAb.inv
      hom_inv_id := by apply Mon.Hom.ext; exact eiAb.hom_inv_id
      inv_hom_id := by apply Mon.Hom.ext; exact eiAb.inv_hom_id }
  let φ := (upperStarFromPoint X).map ei.hom.hom
  have : IsIso ei.hom.hom := by
    change IsIso eiAb.hom
    infer_instance
  have : IsIso φ := inferInstanceAs (IsIso ((upperStarFromPoint X).map ei.hom.hom))
  let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  let ER := ModuleObjectRingedComparison.equivalence Λ0.X X
  let ES := ModuleObjectRingedComparison.equivalence Λ1.X X
  let Ki := ES.mapDerivedCategory.inverse.obj K
  let K0 := V.mapDerivedCategory.obj Ki
  have hc1 : constantModelBoundedConstructible Λ1.X X Ki := by
    rw [← (adicConstructibilityPredicateComparison l X Λ1.X
      (CondensedRing.IsEllAdicCoefficient.integral E.1)).2]
    exact hK
  have hc0 : constantModelBoundedConstructible Λ0.X X K0 := by
    refine ⟨V.bounded_mapDerivedCategory_obj hc1.1, ?_⟩
    intro n
    exact constructible_iso ((V.mapDerivedCategoryHomologyFunctorIso n).app Ki)
      (constructible_comap ei.hom.hom X _ (hc1.2 n))
  have hraw := native_continuity l E0 X K0 hc0
  obtain ⟨eHom⟩ := nativeHomComparison Λ0 X K0
  dsimp only [ModuleObjectRingedComparison.forward, ModuleObjectRingedComparison.hom] at eHom
  simp only [ModuleObjectRingedComparison.sectionForward_eq] at eHom
  let H0 := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X)
      (ModuleObjectRingedComparison.ring Λ0.X X)))
  let H1 := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X)
      (ModuleObjectRingedComparison.ring Λ1.X X)))
  have hraw' : HomContinuous (H0.obj (op (ER.mapDerivedCategory.functor.obj K0))) :=
    (continuous_equivalence_iff ER _ _ eHom).mp hraw
  let a := sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) φ
  let U := SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a
  let r0 := scalarRestrictionIso (Scheme.ProEt.topology X) φ
  have : V.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso φ).functor.IsEquivalence
  have : (ES.functor ⋙ U).IsEquivalence := Functor.isEquivalence_of_iso r0
  have : U.IsEquivalence := Functor.isEquivalence_of_comp_left ES.functor U
  let r := (Functor.mapDerivedCategoryCompIso V ER.functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso r0 ≪≫
      Functor.mapDerivedCategoryCompIso ES.functor U
  let q : ER.mapDerivedCategory.functor.obj K0 ≅ U.mapDerivedCategory.obj K :=
    r.app Ki ≪≫ U.mapDerivedCategory.mapIso (ES.mapDerivedCategory.counitIso.app K)
  have hraw'' : HomContinuous (H0.obj (op (U.mapDerivedCategory.obj K))) :=
    continuous_iso (H0.mapIso q.symm.op) hraw'
  have hactual : HomContinuous (H1.obj (op K)) :=
    continuity_scalar_equivalence X a K hraw''
  let G := localizationHomComplex.{u + 1, u, u, u + 1}
    (Scheme.ProEt.topology X) (ModuleObjectRingedComparison.ring Λ1.X X) K
  let eG : DerivedCategory.Q ⋙ H1.obj (op K) ≅ G ⋙ DerivedCategory.Q :=
    (NatIso.ofComponents (fun P ↦ localizationHomResolutionIso _ K P)
      (fun f ↦ localizationHomResolutionIso_naturality _ K f)).symm
  intro D hD
  exact sequential_model_continuity (H1.obj (op K)) G eG hactual D hD

end AlgebraicGeometry.ProEtale
