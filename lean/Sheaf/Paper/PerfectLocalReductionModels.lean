/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.CompletedConstantSheafReduction
import all Sheaf.Paper.CompletedConstantSheafReduction
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.IntegralStratifiedPerfectModels
import Sheaf.Paper.PerfectChartTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import Sheaf.CategoryTheory.ConstantModuleFlat
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Reduction of one perfect model on a stratum chart -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private def localRestrictionComparison {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) :
    (ringedDerivedRestrictionGeneral
      ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U).obj
        ((adicTowerPullback g R).obj K) ≅ integralLocalDerived g R U K := by
  let B := (adicLisseForget S).obj ((adicTowerInverseImage g).obj R)
  let F := SheafOfModules.overFunctor.{u + 1} B U
  have := (ringedOverFunctor_exactGeneral B U).1
  have := (ringedOverFunctor_exactGeneral B U).2.1
  have := (ringedOverFunctor_exactGeneral B U).2.2
  exact F.mapDerivedCategory.mapIso
    (DerivedCategory.Q.objObjPreimageIso ((adicTowerPullback g R).obj K)).symm ≪≫
      F.mapDerivedCategoryFactors.app _

private def localMapIso {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    {K L : DerivedCategory (pbcModules T R)} (e : K ≅ L) :
    integralLocalDerived g R U K ≅ integralLocalDerived g R U L :=
  (localRestrictionComparison g R U K).symm ≪≫
    (ringedDerivedRestrictionGeneral
      ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U).mapIso
        ((adicTowerPullback g R).mapIso e) ≪≫ localRestrictionComparison g R U L

private def localHomologyIso {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) (q : ℤ) := by
  let R' := (adicTowerInverseImage g).obj R
  let B := (adicLisseForget S).obj R'
  let F := proEtaleRingModulePullback g R R' (Iso.refl _)
  let G := SheafOfModules.overFunctor.{u + 1} B U
  have := (ringedOverFunctor_exactGeneral B U).1
  have := (ringedOverFunctor_exactGeneral B U).2.1
  have := (ringedOverFunctor_exactGeneral B U).2.2
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl R')).choose
  exact (G.mapIso (θ ((proEtaleModuleInverseImage g R).obj
    ((DerivedCategory.homologyFunctor (pbcModules T R) q).obj K)))).symm ≪≫
    G.mapIso ((F.mapDerivedCategoryHomologyFunctorIso q).app K) ≪≫
      ((G.mapDerivedCategoryHomologyFunctorIso q).app (F.mapDerivedCategory.obj K)) ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso (localRestrictionComparison g R U K)

private instance proEt_small (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private theorem constant_kflat (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (C : CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : ℤ) [C.IsStrictlyLE b]
    (hC : ∀ q, Module.Projective A (C.X q)) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := adicLisseConstantRing X A)
      ((CompletedConstantReduction.constantComplex X A).obj C) := by
  let F := adicLisseConstantModules X A
  have : F.Additive := CompletedConstantReduction.constant_additive X A
  have : ((CompletedConstantReduction.constantComplex X A).obj C).IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff _ b).2 fun q hq ↦
      F.map_isZero (C.isZero_of_isStrictlyLE b q hq)
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite.{u + 1, u, u + 1}
    (adicLisseConstantRing X A) _ b
  intro q
  have : Module.Projective A (C.X q) := hC q
  exact isFlatOnSite_constantModule.{u + 1, u} (ProEt.topology X) A (C.X q) inferInstance

/-- A perfect completed-constant model on one chart has a common support interval
before and after every finite reduction, and finite constant cohomology after reduction.
Source: Bhatt--Scholze, Lemma 6.5.8(1), Lemma 6.6.10(1), and the local calculation
in Proposition 6.6.11; Stacks Tags 06YS, 06YT, 06YU, 093J.
(blueprint: lem-weil-pbc-perfect-local-reduction-models).

Proof: choose a bounded finite-projective representative C of P. Each term is a
retract of a finite free A-module; constants and scalar extension preserve these
splittings. Hence its completed realization is a bounded complex of flat modules,
and is K-flat. Exact inverse image to the stratum and exact slice restriction
preserve K-flatness and commute with cohomology. Restriction commutes with reduction,
so apply the local-model isomorphism and compute the derived reduction on C.
Associativity of scalar extension identifies its n-th reduction with the constant
complex C tensor_A A/I^(n+1): the balancing map is
(b tensor x) tensor c ↦ x tensor pi_n(b)c. It is an isomorphism on finite free
modules, hence on their retracts, and respects the differentials. These complexes
have exactly the original term support interval, enlarged to contain zero if
necessary. Exactness of constant module sheafification identifies cohomology with
the constant module H^q(C tensor_A A/I^(n+1)). Every term is a retract of a finite
power of the finite quotient ring; its cycles and their quotient are finite sets.
They therefore supply the asserted finite constant models on the original chart.
Outside the term interval both completed and reduced cohomology vanish. -/
theorem perfect_local_reduction_models
    {X Y : Scheme.{u}} (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : d.derived X) (U : Y.ProEt)
    (P : @DerivedCategory (ModuleCat.{u + 1} A) _ _ (HasDerivedCategory.standard _))
    (hP : @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P)
    (e : Nonempty (integralLocalDerived g (d.completedRing X) U K ≅
      integralLocalDerived g (d.completedRing X) U
        ((pbcDerivedExtend (CompletedConstantReduction.base X d.ideal ≫
          (pbcCompletedComparison X d).hom)).obj
            (DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X A).obj
              ((@DerivedCategory.Q (ModuleCat.{u + 1} A) _ _
                (HasDerivedCategory.standard _)).objPreimage P)))))) :
    ∃ a b : ℤ, a ≤ b ∧
      (∀ q : ℤ, q < a ∨ b < q →
        IsZero ((SheafOfModules.overFunctor _ U).obj
          ((proEtaleModuleInverseImage g (d.completedRing X)).obj
            ((DerivedCategory.homologyFunctor _ q).obj K)))) ∧
      (∀ n q, q < a ∨ b < q →
        IsZero ((SheafOfModules.overFunctor _ U).obj
          ((proEtaleModuleInverseImage g
            (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
              ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
                ((DerivedCategory.homologyFunctor _ q).obj ((d.reduction X n).obj K)))))) ∧
      ∀ n q, ∃ M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)), Finite M ∧
        Nonempty ((SheafOfModules.overFunctor _ U).obj
          ((proEtaleModuleInverseImage g
            (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
              ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
                ((DerivedCategory.homologyFunctor _ q).obj ((d.reduction X n).obj K)))) ≅
          (SheafOfModules.overFunctor _ U).obj
            ((proEtaleModuleInverseImage g
              (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
                ((adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1))).obj M))) := by
  classical
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  obtain ⟨C, a, b, ha, hb, hC, ⟨ep⟩⟩ := hP
  have := ha
  have := hb
  let c := CompletedConstantReduction.base X d.ideal ≫ (pbcCompletedComparison X d).hom
  let F := adicLisseConstantModules X A
  have : F.Additive := CompletedConstantReduction.constant_additive X A
  have : PreservesFiniteLimits F := (CompletedConstantReduction.constant_exact X A).1
  have : PreservesFiniteColimits F := (CompletedConstantReduction.constant_exact X A).2
  let ec : DerivedCategory.Q.obj
      ((CompletedConstantReduction.constantComplex X A).obj
        (DerivedCategory.Q.objPreimage P)) ≅
      DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X A).obj C) :=
    (F.mapDerivedCategoryFactors.app _).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso P ≪≫ ep) ≪≫
        F.mapDerivedCategoryFactors.app C
  obtain ⟨e⟩ := e
  let e' := e ≪≫ localMapIso g (d.completedRing X) U
    ((pbcDerivedExtend c).mapIso ec)
  let C₀ := (CompletedConstantReduction.constantComplex X A).obj C
  have hflat := constant_kflat X C b (fun q ↦ (hC q).1)
  have : IsIso (pbcComplexCounit c C₀) := by
    have := pbcExtensionCounit_isIso c C₀ hflat
    dsimp only [pbcComplexCounit]
    infer_instance
  let ec₀ := e' ≪≫ localMapIso g (d.completedRing X) U (asIso (pbcComplexCounit c C₀))
  have en := perfect_chart_tensor_comparison g d K U C a b ha hb hC ⟨e'⟩
  let a₀ : ℤ := min a 0
  let b₀ : ℤ := max b 0
  have hbound (q : ℤ) (hq : q < a₀ ∨ b₀ < q) : IsZero (C.X q) := by
    rcases hq with hq | hq
    · exact C.isZero_of_isStrictlyGE a q (lt_of_lt_of_le hq (min_le_left _ _))
    · exact C.isZero_of_isStrictlyLE b q (lt_of_le_of_lt (le_max_left _ _) hq)
  let D := ((pbcExtend c).mapHomologicalComplex (.up ℤ)).obj
    ((CompletedConstantReduction.constantComplex X A).obj C)
  have hcompleted (q : ℤ) (hq : q < a₀ ∨ b₀ < q) :
      IsZero ((SheafOfModules.overFunctor _ U).obj
        ((proEtaleModuleInverseImage g (d.completedRing X)).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) := by
    have hzD : IsZero (D.X q) :=
      (pbcExtend c).map_isZero (F.map_isZero (hbound q hq))
    have hzH : IsZero (D.homology q) :=
      (HomologicalComplex.ExactAt.of_isZero hzD).isZero_homology
    let G := proEtaleModuleInverseImage g (d.completedRing X) ⋙
      SheafOfModules.overFunctor _ U
    have : G.Additive := by
      have := (ringedOverFunctor_exactGeneral
        ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj (d.completedRing X))) U).1
      infer_instance
    have hz := G.map_isZero hzH
    exact hz.of_iso (localHomologyIso g (d.completedRing X) U K q ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso ec₀ ≪≫
        (localHomologyIso g (d.completedRing X) U (DerivedCategory.Q.obj D) q).symm ≪≫
          G.mapIso ((DerivedCategory.homologyFunctorFactors _ q).app D))
  have hfinite (n : ℕ) :
    (∀ q : ℤ, q < a₀ ∨ b₀ < q →
        IsZero ((SheafOfModules.overFunctor _ U).obj
          ((proEtaleModuleInverseImage g
            (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
              ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
                ((DerivedCategory.homologyFunctor _ q).obj ((d.reduction X n).obj K)))))) ∧
      ∀ q, ∃ M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)), Finite M ∧
        Nonempty ((SheafOfModules.overFunctor _ U).obj
          ((proEtaleModuleInverseImage g
            (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
              ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
                ((DerivedCategory.homologyFunctor _ q).obj ((d.reduction X n).obj K)))) ≅
          (SheafOfModules.overFunctor _ U).obj
            ((proEtaleModuleInverseImage g
              (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
                ((adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1))).obj M))) := by
    let B := A ⧸ d.ideal ^ (n + 1)
    let r := Ideal.Quotient.mk (d.ideal ^ (n + 1))
    let E := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} r
    have : E.Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r).left_adjoint_additive
    let Cn := (E.mapHomologicalComplex (.up ℤ)).obj C
    let Fn := adicLisseConstantModules X B
    have : Fn.Additive := CompletedConstantReduction.constant_additive X B
    have : PreservesFiniteLimits Fn := (CompletedConstantReduction.constant_exact X B).1
    have : PreservesFiniteColimits Fn := (CompletedConstantReduction.constant_exact X B).2
    let G := proEtaleModuleInverseImage g (adicLisseConstantRing X B) ⋙
      SheafOfModules.overFunctor _ U
    have : G.Additive := by
      have := (ringedOverFunctor_exactGeneral
        ((adicLisseForget Y).obj
          ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) U).1
      infer_instance
    let N := (d.reduction X n).obj K
    let T := pbcRestrict (pbcLevelConstantComparison X d n).hom
    let en' := (en n).some
    let eH (q : ℤ) :=
      G.mapIso ((T.mapDerivedCategoryHomologyFunctorIso q).app N) ≪≫
        localHomologyIso g (adicLisseConstantRing X B) U (T.mapDerivedCategory.obj N) q ≪≫
          (DerivedCategory.homologyFunctor _ q).mapIso en' ≪≫
            (localHomologyIso g (adicLisseConstantRing X B) U
              (DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X B).obj Cn))
                q).symm ≪≫
            G.mapIso ((DerivedCategory.homologyFunctorFactors _ q).app
              ((CompletedConstantReduction.constantComplex X B).obj Cn)) ≪≫
            G.mapIso ((Cn.sc q).mapHomologyIso Fn)
    have hbCn (q : ℤ) (hq : q < a₀ ∨ b₀ < q) : IsZero (Cn.homology q) :=
      (HomologicalComplex.ExactAt.of_isZero (E.map_isZero (hbound q hq))).isZero_homology
    have hM (q : ℤ) : Finite (Cn.homology q) := by
      have : Finite B := d.quotientFinite n
      have : Module.Finite A (C.X q) := (hC q).2
      have : Module.Finite B (Cn.X q) := inferInstanceAs
        (Module.Finite B (TensorProduct A B (C.X q)))
      have : Finite (Cn.X q) := Module.finite_of_finite (R := B)
      have : Finite (Cn.cycles q) := Finite.of_injective (Cn.iCycles q)
        ((ModuleCat.mono_iff_injective _).1 inferInstance)
      exact Finite.of_surjective (Cn.homologyπ q)
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    exact ⟨(fun q hq ↦ (G.map_isZero (Fn.map_isZero (hbCn q hq))).of_iso (eH q)),
      fun q ↦ ⟨Cn.homology q, hM q, ⟨eH q⟩⟩⟩
  refine ⟨a₀, b₀, le_trans (min_le_right _ _) (le_max_right _ _), hcompleted, ?_, ?_⟩
  · intro n
    exact (hfinite n).1
  · intro n
    exact (hfinite n).2

end AlgebraicGeometry.Scheme
