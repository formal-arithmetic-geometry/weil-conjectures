/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections

import WeilConjectures.AlgebraicGeometry.AdicCompletion.IntegralCoefficientQuotientLimit
import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBoundTorsion
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LatticeSupportedHomFiniteComparison
import all WeilConjectures.SixFunctors.IntegralDualTorsionHeartSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionProducts
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # The integral lattice bound for proper direct image

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-construction/sec-proper-direct-image-of-unbounded-complexes/
sk-lem-proper-heart-bound/sk-lem-proper-heart-bound-lattice.md and its proof
(blueprint: det-proper-heart-bound-lattice).

Global sections are right derived on the category of internal module objects.
The coefficient object is the continuous condensed valuation ring
`DerivedNakayama.integerRing ℓ E` of the recorded coefficient extension
(`Padic.coefficientExtensionIntegers`), the ring of the torsion situation
`properHeartBoundTorsion`. The test scheme V is not assumed Noetherian.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Abelian
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  Mod.monoidalCategoryStruct Mod.monoidalClosed DerivedCategory.monoidalClosed

namespace LatticeBound

-- Adapted from the product-preservation proof in ProEtaleUnboundedDerivedProducts.
private theorem rightDerived_preserves_products
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    {J : Type*} [HasLimitsOfShape (Discrete J) C]
    [HasLimitsOfShape (Discrete J) D]
    [HasExactLimitsOfShape (Discrete J) D]
    (F : C ⥤ D) [F.Additive]
    [PreservesLimitsOfShape (Discrete J) F] :
    PreservesLimitsOfShape (Discrete J) F.rightDerivedFunctor := by
  classical
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso D).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
        F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  have hfamily (K : J → DerivedCategory C) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    have hex (j : J) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K j)
    choose I hI he using hex
    let e (j : J) := (Classical.choice (he j)).symm
    have : ∀ j, (I j).IsKInjective := hI
    let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
    obtain ⟨hPI, ⟨hPL⟩⟩ :=
      CochainComplex.termwise_product_isKInjective_and_isLimit I
    have : CochainComplex.IsKInjective P.pt := hPI
    have hFPL := isLimitOfPreserves DerivedCategory.Q
      (isLimitOfPreserves G (HomologicalComplex.isLimitConeOfHasLimitEval
        (Discrete.functor I)))
    let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun (j : Discrete J) ↦ e j.as)
    let c := (Cone.postcompose α.hom).obj (DerivedCategory.Q.mapCone P)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv α _).symm hPL
    apply preservesLimit_of_preserves_limit_cone hc
    let αβ : (Discrete.functor I ⋙ G) ⋙ DerivedCategory.Q ≅
        (Discrete.functor I ⋙ DerivedCategory.Q) ⋙ F.rightDerivedFunctor :=
      Discrete.natIso (fun (j : Discrete J) ↦ asIso (β.app (I j.as)))
    have hmap : IsLimit (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P)) :=
      (IsLimit.equivOfNatIsoOfIso αβ
        (DerivedCategory.Q.mapCone (G.mapCone P))
        (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
        (Cone.ext (asIso (β.app P.pt)) (fun j ↦ by
          simpa [αβ] using β.naturality (P.π.app j)))).1 hFPL
    exact (IsLimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight α F.rightDerivedFunctor)
      (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
      (F.rightDerivedFunctor.mapCone c)
      (Cone.ext (Iso.refl _) (fun j ↦ by simp [c]))).1 hmap
  exact preservesLimitsOfShape_of_discrete _


-- The vanishing consequence of the epimorphic-tower Milnor sequence.
private theorem limit_bound
    {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions C]
    [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C]
    [HasLimitsOfShape ℕᵒᵖ C]
    [HasDerivedCategory Ab.{u}] [Abelian.HasKInjectiveResolutions Ab.{u}]
    (hC : EpiπAppZeroOfEpi C)
    (F : C ⥤ Ab.{u}) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (D : ℕᵒᵖ ⥤ C) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ n, Epi (D.map (homOfLE (Nat.le_succ n)).op))
    (q : ℤ)
    (hv : ∀ n (r : ℤ), r = q ∨ r = q - 1 →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u} r).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj
          (D.obj (op n)))))) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} q).obj
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj c.pt))) := by
  have : PreservesLimitsOfShape (Discrete ℕ) ((CochainComplex.singleFunctors C).functor 0) :=
    inferInstanceAs (PreservesLimitsOfShape _ (HomologicalComplex.single C _ 0))
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.singleFunctor C 0) :=
    preservesLimitsOfShape_of_natIso
      (F := (CochainComplex.singleFunctors C).functor 0 ⋙ DerivedCategory.Q)
      ((SingleFunctors.evaluation _ _ 0).mapIso
        (DerivedCategory.singleFunctorsPostcompQIso C)).symm
  have : PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor :=
    rightDerived_preserves_products F
  let P : Fan (fun n : ℕ ↦ D.obj (op n)) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  let t : P.pt ⟶ P.pt := Pi.lift fun n ↦
    Pi.π _ (n + 1) ≫ D.map (homOfLE (Nat.le_succ n)).op
  have ht (n : ℕ) : t ≫ P.proj n =
      P.proj (n + 1) ≫ D.map (homOfLE (Nat.le_succ n)).op := by simp [t, P]
  let S : ShortComplex C :=
    ShortComplex.mk _ _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t ht c)
  have hK := Fan.IsLimit.isLimitKernelForkOneSub hP t ht hc
  have hS : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel hK
      mono_f := Fork.IsLimit.mono hK
      epi_g := epi_one_sub_of_epiπAppZeroOfEpi hC hD hP t ht }
  have hz (r : ℤ) (hr : r = q ∨ r = q - 1) :
      IsZero ((DerivedCategory.homologyFunctor Ab.{u} r).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj P.pt))) := by
    let G := DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor Ab.{u} r
    have hG : IsLimit (G.mapCone P) := isLimitOfPreserves G hP
    exact (IsZero.iff_id_eq_zero _).2 (hG.hom_ext fun ⟨n⟩ ↦
      (hv n r hr).eq_of_tgt _ _)
  exact (F.rightDerivedHomologySequence_exact₁ hS (q - 1) q (by omega)).isZero_X₂
    ((hz (q - 1) (Or.inr rfl)).eq_of_src _ _)
    ((hz q (Or.inl rfl)).eq_of_tgt _ _)

section SectionsComparison

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

-- The internal/sectionwise equivalence reduces this to the proved evaluation comparison.
private noncomputable def compareSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (q : ℕ) :
    (DerivedCategory.homologyFunctor.{u + 1} Ab.{u + 1} (q : ℤ)).obj
        ((Mod.forget (condensedRingObj Λ S) ⋙
          Sheaf.Γ (Scheme.ProEt.topology S) Ab.{u + 1}).rightDerivedFunctor.{u + 2, u + 2, u + 1,
            u + 1, u + 1, u + 1}.obj
          ((DerivedCategory.singleFunctor.{u + 1} _ 0).obj M)) ≅
      ((Sheaf.Γ (Scheme.ProEt.topology S) Ab.{u + 1}).rightDerived q).obj M.X := by
  let J := Scheme.ProEt.topology S
  let O : Sheaf J Ab.{u + 1} := condensedRingObj Λ S
  let R : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J O)
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let : EnoughInjectives (SheafOfModules.{u + 1} R) :=
    EnoughInjectives.of_equivalence e.inverse
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  let T := Scheme.ProEt.mk (𝟙 S)
  let A : Sheaf J Ab.{u + 1} ⥤ Ab.{u + 1} := Sheaf.sectionsFunctorAt J T
  let B : Sheaf J Ab.{u + 1} ⥤ Ab.{u + 1} := Sheaf.Γ J Ab.{u + 1}
  let F := Mod.forget O ⋙ B
  let G : SheafOfModules.{u + 1} R ⥤ Ab.{u + 1} := SheafOfModules.toSheaf R ⋙ A
  let ea : B ≅ A := Sheaf.ΓNatIsoSheafSections J _ (Scheme.ProEt.isTerminalMkId S)
  let ef : F ≅ e.functor ⋙ G := Functor.isoWhiskerLeft (Mod.forget O) ea
  exact Functor.homologyRightDerivedFunctorObjSingleFunctorIso.{u + 2, u + 2,
      u + 1, u + 1, u + 1, u + 1} F M q ≪≫
    Functor.rightDerivedObjIsoOfIso ef q M ≪≫
    Functor.compRightDerivedObjIso e.functor G
      (fun I _ ↦ G.rightAcyclic_of_injective (e.functor.obj I)) q M ≪≫
    evaluation_comparison S R (e.functor.obj M) q ≪≫
    Functor.rightDerivedObjIsoOfIso ea.symm q M.X


private noncomputable def abelianSectionsClassical (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (n : ℕ) :
    (DerivedCategory.homologyFunctor.{u + 1} Ab.{u + 1} (n : ℤ)).obj
        ((rightDerivedGlobalSections Ab.{u + 1} T).obj
          ((DerivedCategory.singleFunctor.{u + 1} _ 0).obj M)) ≅
      ((Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).rightDerived n).obj M :=
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso.{u + 2, u + 2,
    u + 1, u + 1, u + 1, u + 1} _ M n

-- Compare the underlying inverse-image module before specializing its argument.
private noncomputable def upperStar_sections_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}}
    (r : T ⟶ X) [WeaklyEtale r]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (a : ℕ) :
    ((Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).rightDerived a).obj
        ((CondensedRing.upperStar Λ r).obj N).X ≅
      ((Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).rightDerived a).obj
        ((Scheme.proEtaleSheafInverseImage r Ab.{u + 1}).obj N.X) :=
  (((Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).rightDerived a).mapIso
    ((CondensedRing.upperStarForgetIso Λ r).app N)).symm

end SectionsComparison

private theorem restriction_limits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    [WeaklyEtale f] : PreservesLimitsOfShape ℕᵒᵖ (CondensedRing.upperStar Λ f) := by
  let F := upperStar Ab.{u + 1} f
  have : PreservesLimitsOfShape ℕᵒᵖ (localizationRestriction Ab.{u + 1} f
      (inferInstance : WeaklyEtale f)) := by
    unfold localizationRestriction
    infer_instance
  have : PreservesLimitsOfShape ℕᵒᵖ F :=
    preservesLimitsOfShape_of_natIso
      (upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).symm
  have : PreservesLimitsOfShape ℕᵒᵖ
      (Mod.forget (condensedRingObj Λ X) ⋙ F) := inferInstance
  have : PreservesLimitsOfShape ℕᵒᵖ (CondensedRing.upperStar Λ f ⋙
      Mod.forget (condensedRingObj Λ Y)) :=
    preservesLimitsOfShape_of_natIso (CondensedRing.upperStarForgetIso Λ f)
  have : ReflectsLimitsOfShape ℕᵒᵖ (Mod.forget (condensedRingObj Λ Y) :
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) _ ⥤ _) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (CondensedRing.upperStar Λ f) (Mod.forget (condensedRingObj Λ Y))

private theorem open_limits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S Sbar : Scheme.{u}} [IsNoetherian Sbar]
    (j : S ⟶ Sbar) [IsOpenImmersion j] :
    PreservesLimitsOfShape ℕᵒᵖ (CondensedRing.openImmersionLowerShriek Λ j) := by
  have : QuasiCompact j := inferInstance
  let T : TopologicalSpace.Closeds Sbar :=
    ⟨(Set.range j)ᶜ, (IsOpenImmersion.isOpen_range j).isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
  have hi : Set.range i = (T : Set Sbar) :=
    (Scheme.IdealSheafData.reduced_induced_closed_subscheme Sbar T).2.2.2.2.2.1
  have hcomp : Set.range j = (Set.range i)ᶜ := by
    rw [hi]
    exact (compl_compl _).symm
  have (I : Type (u + 1)) : PreservesLimitsOfShape (Discrete I)
      (ringSheafOpenExtension j (condensedRingObj Λ Sbar)) :=
    (proEtale_openExtension_products_derivedLimits i j hcomp _).2.2.2 I
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (ringSheafOpenExtension j (condensedRingObj Λ Sbar)) :=
    preservesLimits_of_preservesEqualizers_and_products _
  have : PreservesLimitsOfSize.{0, 0}
      (ringSheafOpenExtension j (condensedRingObj Λ Sbar)) :=
    preservesSmallestLimits_of_preservesLimits _
  have : PreservesLimitsOfShape ℕᵒᵖ
      (CondensedRing.linearOpenImmersionLowerShriek Λ j) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (ringSheafOpenExtension j (condensedRingObj Λ Sbar)))
  unfold CondensedRing.openImmersionLowerShriek
  infer_instance

private theorem tensor_limits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S : Scheme.{u}}
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hL : IsLisseCoefficientModule Λ L) :
    PreservesLimitsOfShape ℕᵒᵖ (tensorLeft L) := by
  obtain ⟨hd⟩ := CondensedRing.lisse_dualizable Λ L hL
  exact (tensorLeftAdjunction L Lᘁ).rightAdjoint_preservesLimits.preservesLimitsOfShape


private theorem coefficient_tensor_obj
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (S : Scheme.{u})
    (L : AdicCompletion.Modules ℓ E S) (n : ℕ) :
    L ⊗ (AdicCompletion.coefficientSequence ℓ E S).obj (op n) =
      (torsionQuotient ℓ E S (n + 1)).obj L := rfl

-- Supply the cokernel-preservation family explicitly, avoiding a costly Pi-instance search.
private theorem preserves_epi_of_finite_colimits
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteColimits G] :
    G.PreservesEpimorphisms := by
  have hshape : PreservesColimitsOfShape WalkingParallelPair G :=
    PreservesFiniteColimits.preservesFiniteColimits WalkingParallelPair
  have : ∀ {M N : A} (f : M ⟶ N), PreservesColimit (parallelPair f 0) G :=
    fun _ ↦ hshape.preservesColimit
  exact NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels G

private theorem tensor_limit_bound
    {A B : Type*} [Category A] [MonoidalCategory A] [Category B] [Abelian B]
    [HasDerivedCategory B] [HasKInjectiveResolutions B]
    [HasCountableProducts B] [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory Ab.{u}] [HasKInjectiveResolutions Ab.{u}]
    (hB : EpiπAppZeroOfEpi B)
    (F : B ⥤ Ab.{u}) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (H : A ⥤ B) [PreservesLimitsOfShape ℕᵒᵖ H] [H.PreservesEpimorphisms]
    (L : A) [PreservesLimitsOfShape ℕᵒᵖ (tensorLeft L)]
    [(tensorLeft L).PreservesEpimorphisms]
    (D : ℕᵒᵖ ⥤ A) (c : Cone D) (hc : IsLimit c) (e : c.pt ≅ 𝟙_ A)
    (hD : ∀ n, Epi (D.map (homOfLE (Nat.le_succ n)).op))
    (q : ℤ)
    (hv : ∀ n (r : ℤ), r = q ∨ r = q - 1 →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u} r).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj
          (H.obj (L ⊗ D.obj (op n))))))) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u} q).obj
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj (H.obj L)))) := by
  have hcomb : PreservesLimitsOfShape ℕᵒᵖ (tensorLeft L ⋙ H) :=
    comp_preservesLimitsOfShape (tensorLeft L) H
  have : PreservesLimit D (tensorLeft L ⋙ H) := hcomb.preservesLimit
  let c' := (tensorLeft L ⋙ H).mapCone c
  have hc' : IsLimit c' := isLimitOfPreserves (tensorLeft L ⋙ H) hc
  let e0 : c'.pt ≅ H.obj L := H.mapIso ((tensorLeft L).mapIso e ≪≫ ρ_ L)
  let cL : Cone (D ⋙ tensorLeft L ⋙ H) := c'.extend e0.inv
  have hcL : IsLimit cL := IsLimit.extendIso e0.inv hc'
  have hD' (n : ℕ) : Epi ((D ⋙ tensorLeft L ⋙ H).map
      (homOfLE (Nat.le_succ n)).op) := by
    have := hD n
    dsimp only [Functor.comp_map]
    infer_instance
  exact limit_bound hB F (D ⋙ tensorLeft L ⋙ H) cL hcL hD' q hv

private theorem coefficient_limit_bound
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (S : Scheme.{u})
    {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] [HasKInjectiveResolutions B]
    [HasCountableProducts B] [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory Ab.{u + 1}] [HasKInjectiveResolutions Ab.{u + 1}]
    (hB : EpiπAppZeroOfEpi B)
    (F : B ⥤ Ab.{u + 1}) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (H : AdicCompletion.Modules ℓ E S ⥤ B)
    [PreservesLimitsOfShape ℕᵒᵖ H] [H.PreservesEpimorphisms]
    (L : AdicCompletion.Modules ℓ E S)
    [PreservesLimitsOfShape ℕᵒᵖ (tensorLeft L)]
    [(tensorLeft L).PreservesEpimorphisms]
    (q : ℤ)
    (hv : ∀ n (r : ℤ), r = q ∨ r = q - 1 →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} r).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj
          (H.obj (L ⊗ (AdicCompletion.coefficientSequence ℓ E S).obj (op n))))))) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj (H.obj L)))) := by
  obtain ⟨⟨hc⟩, hepi⟩ := AdicCompletion.integral_coefficient_quotient_limit ℓ E S
  exact tensor_limit_bound hB F H L
    (AdicCompletion.coefficientSequence ℓ E S) (AdicCompletion.coefficientCone ℓ E S)
    hc (Iso.refl _) hepi q hv

section

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

-- Specialize the categorical argument before supplying the geometric functors.
private theorem module_sections_bound
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (S T : Scheme.{u})
    (H : AdicCompletion.Modules ℓ E S ⥤ AdicCompletion.Modules ℓ E T)
    [PreservesLimitsOfShape ℕᵒᵖ H] [H.PreservesEpimorphisms]
    (L : AdicCompletion.Modules ℓ E S)
    [PreservesLimitsOfShape ℕᵒᵖ (tensorLeft L)]
    [(tensorLeft L).PreservesEpimorphisms]
    (q : ℤ)
    (hv : ∀ n (r : ℤ), r = q ∨ r = q - 1 →
      IsZero ((DerivedCategory.homologyFunctor.{u + 1} Ab.{u + 1} r).obj
        ((Mod.forget (AdicCompletion.ring ℓ E T) ⋙
          Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor.{u + 1} (AdicCompletion.Modules ℓ E T) 0).obj
            (H.obj (L ⊗ (AdicCompletion.coefficientSequence ℓ E S).obj (op n))))))) :
    IsZero ((DerivedCategory.homologyFunctor.{u + 1} Ab.{u + 1} q).obj
      ((Mod.forget (AdicCompletion.ring ℓ E T) ⋙
        Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor.{u + 1} (AdicCompletion.Modules ℓ E T) 0).obj
          (H.obj L)))) := by
  let C := AdicCompletion.Modules ℓ E T
  let F : C ⥤ Ab.{u + 1} := Mod.forget (AdicCompletion.ring ℓ E T) ⋙
    Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}
  have hC : EpiπAppZeroOfEpi C := Mod.epiπAppZeroOfEpi
    (Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat (S := T))
  have : CountableAB4Star C := CountableAB4Star.of_epi_π_app_zero hC
  exact coefficient_limit_bound ℓ E S hC F H L q hv

end

end LatticeBound

/-- The integral lattice bound H^q(X_V,r^*(a_!L_0)) = 0 for q > 2d+1.
Source: latest blueprint, sk-lem-proper-heart-bound-lattice.md, and its proof,
Completeness, Sections and Milnor (blueprint: det-proper-heart-bound-lattice).

Proof, following Completeness, Sections, and Milnor:
1. Finite type over k and quasi-compactness make X and its closed subscheme Sbar
   Noetherian. Hence the open factor j is quasi-compact.
2. Use the canonical coefficient quotient cone of integral_coefficient_quotient_limit.
   Tensoring with the dualizable lisse module preserves its limit and epimorphisms.
   Its cone vertex is canonically L, and its nth term is L/pi^(n+1)L.
3. Open extension preserves products and finite limits, so it preserves sequential limits.
   Closed direct image is exact and preserves limits. Weakly etale inverse image is
   localization restriction on underlying abelian sheaves and preserves limits as well.
   These functors therefore transport the cone and its epimorphic transitions to X_V.
4. Repleteness gives the Milnor short exact sequence 0 -> lim D -> product D -> product D -> 0,
   whose last map is 1-shift. Products of K-injectives imply that derived sections preserve
   products, and exact countable products make cohomology commute with these products.
5. The torsion bound kills every finite-level cohomology above 2d. Compare its underlying
   abelian sheaf with the integral-module quotient by upperStarForgetIso, and compare
   derived sections using the internal/sectionwise equivalence and evaluation comparison.
6. If q > 2d+1, both product cohomologies in degrees q and q-1 vanish. Exactness of the
   derived-section long exact sequence forces H^q of the limit to vanish. The limit cone
   was extended along the right unitor before deriving, so its vertex is the displayed object.
-/
theorem properHeartBoundLattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (k : Type u) [Field k] (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y S Sbar : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (j : S ⟶ Sbar) [IsOpenImmersion j] (i : Sbar ⟶ X) [IsClosedImmersion i]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing ℓ E) S))
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L)
    (q : ℤ) (hq : 2 * (d : ℤ) + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      (((Mod.forget (condensedRingObj (DerivedNakayama.integerRing ℓ E)
          (pullback p V.hom)) ⋙
        Sheaf.Γ (Scheme.ProEt.topology (pullback p V.hom)) Ab.{u + 1}).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.upperStar (DerivedNakayama.integerRing ℓ E)
            (pullback.fst p V.hom)).obj
            ((CondensedRing.lowerStar (DerivedNakayama.integerRing ℓ E) i).obj
              ((CondensedRing.openImmersionLowerShriek
                (DerivedNakayama.integerRing ℓ E) j).obj L)))))) := by
  have : IsLocallyNoetherian X := by
    exact LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := by
    exact QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := by
    exact ⟨⟩
  have : IsLocallyNoetherian Sbar := by
    exact LocallyOfFiniteType.isLocallyNoetherian i
  have : CompactSpace Sbar := by
    exact QuasiCompact.compactSpace_of_compactSpace i
  have : IsNoetherian Sbar := by
    exact ⟨⟩
  let Λ := DerivedNakayama.integerRing ℓ E
  let T := pullback p V.hom
  let r : T ⟶ X := pullback.fst p V.hom
  let H := torsionLocallyClosedExtension ℓ E j i ⋙ CondensedRing.upperStar Λ r
  have : PreservesLimitsOfShape ℕᵒᵖ (CondensedRing.openImmersionLowerShriek Λ j) := by
    exact LatticeBound.open_limits Λ j
  have : PreservesFiniteColimits (CondensedRing.lowerStar Λ i) := by
    exact CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite Λ i
  have : PreservesLimitsOfShape ℕᵒᵖ (CondensedRing.upperStar Λ r) := by
    exact LatticeBound.restriction_limits Λ r
  have : PreservesLimitsOfShape ℕᵒᵖ (tensorLeft L) := by
    exact LatticeBound.tensor_limits Λ L hL
  have : PreservesLimitsOfShape ℕᵒᵖ H := by
    dsimp [H, torsionLocallyClosedExtension]; infer_instance
  have : PreservesFiniteColimits H := by
    dsimp [H, torsionLocallyClosedExtension]; infer_instance
  have : H.Additive := by
    dsimp [H, torsionLocallyClosedExtension]; infer_instance
  have : H.PreservesEpimorphisms := by
    exact LatticeBound.preserves_epi_of_finite_colimits H
  have : (tensorLeft L).PreservesEpimorphisms := by
    exact LatticeBound.preserves_epi_of_finite_colimits _
  apply LatticeBound.module_sections_bound ℓ E S T H L q
  intro n a ha
  have ha' : (2 * d : ℤ) < a := by omega
  lift a to ℕ using (by omega)
  let N := (torsionLocallyClosedExtension ℓ E j i).obj
    ((torsionQuotient ℓ E S (n + 1)).obj L)
  have hobj : H.obj (L ⊗ (AdicCompletion.coefficientSequence ℓ E S).obj (op n)) =
      (CondensedRing.upperStar Λ r).obj N := by
    exact congrArg (fun M ↦ (CondensedRing.upperStar Λ r).obj
      ((torsionLocallyClosedExtension ℓ E j i).obj M))
      (LatticeBound.coefficient_tensor_obj ℓ E S L n)
  rw [hobj]
  have ht := by
    exact ((properHeartBoundTorsion ℓ E k hchar hell p d hd V hV j i
      (n + 1) (by omega)).2 ⟨L, hL⟩).2 (a : ℤ) ha'
  have hz := by
    exact ht.of_iso (LatticeBound.abelianSectionsClassical T
      ((Scheme.proEtaleSheafInverseImage r Ab.{u + 1}).obj N.X) a).symm
  have hz' := by
    exact hz.of_iso (LatticeBound.upperStar_sections_iso Λ r N a)
  exact hz'.of_iso
    (LatticeBound.compareSections Λ T ((CondensedRing.upperStar Λ r).obj N) a)

end AlgebraicGeometry.ProEtale
