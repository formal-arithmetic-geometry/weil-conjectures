/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all Sheaf.Paper.PointSectionsIntegralCohomologyControl
import all Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Integral geometric stalks and their finite reductions -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open Opposite
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [-instance] pointReductionModuleDerived

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

private theorem stalk_exact_products
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y) :
    PreservesFiniteLimits (integralCoefficientModuleStalkFunctor l E y) ∧
      PreservesFiniteColimits (integralCoefficientModuleStalkFunctor l E y) ∧
      PreservesLimitsOfShape (Discrete ℕ) (integralCoefficientModuleStalkFunctor l E y) := by
  let O := completedIntegralCommRingSheafUnrestricted l E Y
  let R := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let S := sheafToPresheaf (ProEt.topology Y) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood y)ᵒᵖ
      Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
      (proEtaleGeometricNeighbourhoodForget y).op ⋙ colim
  obtain ⟨h, j, hj, _, hι, hlim, hcolim⟩ := proEtale_classical_stalk y
  have : PreservesFiniteLimits S := hlim
  have : PreservesFiniteColimits S := hcolim
  let α := Functor.whiskerLeft
    (sheafToPresheaf (ProEt.topology Y) AddCommGrpCat.{u + 1})
    (Functor.whiskerLeft
      ((Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood y)ᵒᵖ Y.ProEtᵒᵖ
        AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget y).op)
      (colim.ι (op (StructuredArrow.mk
        (Y := @ProEt.mk Y _ (strictHenselizationStructuralMap y) h) (Over.homMk j hj)))))
  have : IsIso α := hι
  have : PreservesLimitsOfShape (Discrete ℕ)
      ((sheafSections (ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
        (op (@ProEt.mk Y _ (strictHenselizationStructuralMap y) h))) := by
    change PreservesLimitsOfShape (Discrete ℕ) (sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ _).obj _)
    infer_instance
  have : PreservesLimitsOfShape (Discrete ℕ) S :=
    preservesLimitsOfShape_of_natIso (asIso α)
  let T := integralCoefficientModuleStalkFunctor l E y
  let U := forget₂ (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfSize.{0, 0} U := by
    constructor
    intro J _
    exact ModuleCat.forget₂PreservesColimitsOfShape.{u + 1, u + 1, 0, 0}
      (J := J) _
  have : PreservesFiniteColimits U :=
    PreservesColimitsOfSize.preservesFiniteColimits U
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} R) :=
    SheafOfModules.preservesFiniteColimits_toSheaf.{u + 1, u, u + 1, u + 1} R
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} R ⋙ sheafToPresheaf _ _) :=
    comp_preservesLimitsOfShape (SheafOfModules.forget R)
      (PresheafOfModules.toPresheaf R.obj)
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} R) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  let e : T ⋙ U ≅ SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} R ⋙ S :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)
  have : PreservesFiniteLimits (T ⋙ U) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (T ⋙ U) := preservesFiniteColimits_of_natIso e.symm
  have : PreservesLimitsOfShape (Discrete ℕ) (T ⋙ U) :=
    preservesLimitsOfShape_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U,
    preservesLimitsOfShape_of_reflects_of_preserves T U⟩

private theorem integralGerm_smul
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y)
    (M : scalarReductionSource.{u, u} l E Y) (N : ProEtaleGeometricNeighbourhood y)
    (r : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (a : M.val.obj (op N.right)) :
    let η := toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
    let c := integralConstantToCompletion l E Y
    let ι := (colimit.ι ((proEtaleGeometricNeighbourhoodForget y).op ⋙ M.val.presheaf)
      (op N)).hom
    ι (c.hom.app (op N.right) (η.app (op N.right) r) • a) =
      r • (show (integralCoefficientModuleStalkFunctor l E y).obj M from ι a) := by
  dsimp only
  let O := completedIntegralCommRingSheafUnrestricted l E Y
  let R := proEtaleGeometricStalkRingDiagram y O
  let SM := (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
    (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj M.val
  let f : N ⟶ proEtaleConstantGermNeighbourhood y :=
    StructuredArrow.homMk (MorphismProperty.Over.homMk N.right.hom) (by
      apply Over.OverMorphism.ext
      exact Over.w N.hom)
  let η := toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
  let c := integralConstantToCompletion l E Y
  have hη : O.obj.map f.right.op
      (c.hom.app (op (ProEt.mk (𝟙 Y))) (η.app (op (ProEt.mk (𝟙 Y))) r)) =
      c.hom.app (op N.right) (η.app (op N.right) r) := by
    have hc := ConcreteCategory.congr_hom (c.hom.naturality f.right.op)
      (η.app (op (ProEt.mk (𝟙 Y))) r)
    have hn := ConcreteCategory.congr_hom (η.naturality f.right.op) r
    exact hc.symm.trans (congrArg (fun z ↦ c.hom.app (op N.right) z) hn.symm)
  have hr : integralConstantStalkGerm l E y r =
      colimit.ι R (op N) (c.hom.app (op N.right) (η.app (op N.right) r)) := by
    have h := ConcreteCategory.congr_hom (colimit.w R f.op)
      (c.hom.app (op (ProEt.mk (𝟙 Y))) (η.app (op (ProEt.mk (𝟙 Y))) r))
    change colimit.ι R (op N) (O.obj.map f.right.op _) = _ at h
    rw [hη] at h
    have hc := ConcreteCategory.congr_hom (colimit.ι_map
      (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget y).op c.hom)
      (op (proEtaleConstantGermNeighbourhood y)))
      (η.app (op (ProEt.mk (𝟙 Y))) r)
    change integralConstantStalkGerm l E y r =
      colimit.ι R (op (proEtaleConstantGermNeighbourhood y))
        (c.hom.app _ (η.app _ r)) at hc
    exact hc.trans h.symm
  have hsmul := (PresheafOfModules.ModuleColimit.smul_eq
    (colimit.isColimit R) (colimit.isColimit SM.presheaf)
      (U := op N) (c.hom.app (op N.right) (η.app (op N.right) r)) a).symm
  have hr' : PresheafOfModules.ModuleColimit.ιR (colimit.cocone R)
      (c.hom.app (op N.right) (η.app (op N.right) r)) =
      integralConstantStalkGerm l E y r := hr.symm
  rw [hr'] at hsmul
  exact hsmul

private theorem integralStalk_reduction_nilpotent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y) (n : ℕ)
    (X : DerivedCategory (scalarReductionTarget.{u, u} l E Y n))
    (r : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (hr : r ∈ Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}) :
    let F := integralCoefficientModuleStalkFunctor l E y
    let G := scalarReductionRestriction.{u, u} l E Y n
    ∀ [PreservesFiniteLimits F] [PreservesFiniteColimits F],
      (r ^ (n + 1)) • 𝟙
        (F.mapDerivedCategory.{u + 2, u + 1}.obj (G.mapDerivedCategory.obj X)) = 0 := by
  intro F G _ _
  let P := DerivedCategory.Q.objPreimage X
  let e := F.mapDerivedCategory.{u + 2, u + 1}.mapIso (G.mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso X).symm) ≪≫
    F.mapDerivedCategory.{u + 2, u + 1}.mapIso (G.mapDerivedCategoryFactors.app P) ≪≫
      F.mapDerivedCategoryFactors.{u + 2, u + 1}.app ((G.mapHomologicalComplex (.up ℤ)).obj P)
  let C := (F.mapHomologicalComplex (.up ℤ)).obj
    ((G.mapHomologicalComplex (.up ℤ)).obj P)
  have hq : RingHom.ulift.{u + 1, u + 1, u, u}
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
      (r ^ (n + 1)) = 0 := by
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hr
    have hrs : r.down = s.down * Padic.coefficientExtensionUniformizer l E :=
      congrArg ULift.down hs.symm
    apply ULift.ext
    change Ideal.Quotient.mk _ (r.down ^ (n + 1)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, hrs, mul_pow]
    exact dvd_mul_left _ _
  have hscalar (V : Y.ProEtᵒᵖ) :
      (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app V
        ((integralConstantToCompletion l E Y).hom.app V
          ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u}
              (Padic.coefficientExtensionIntegers l E))))).app V (r ^ (n + 1)))) = 0 := by
    have h := congrArg (fun f ↦ f.hom.app V
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E))))).app V (r ^ (n + 1))))
      (limit.lift_π (integralConstantCoefficientCone l E Y) (op n))
    change (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app V
      ((integralConstantToCompletion l E Y).hom.app V _) = _ at h
    erw [h]
    let q := CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1, u, u}
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))))
    have hn := congrArg (fun f :
        (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ⟶ _ ↦
      f.app V (r ^ (n + 1)))
      (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map q))
    let η := toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
    let η' := toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    change η'.app V (q (r ^ (n + 1))) =
      ((integralConstantCoefficientCone l E Y).π.app (op n)).hom.app V
        (η.app V (r ^ (n + 1))) at hn
    erw [← hn, hq, map_zero]
  have hC : (r ^ (n + 1)) • 𝟙 C = 0 := by
    ext i z
    let M := G.obj (P.X i)
    let O := completedIntegralCommRingSheafUnrestricted l E Y
    let D := proEtaleGeometricStalkRingDiagram y O
    let SM := (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
      (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj M.val
    obtain ⟨N, a, rfl⟩ := PresheafOfModules.ModuleColimit.ιM_jointly_surjective
      (hcR := colimit.isColimit D) (hcM := colimit.isColimit SM.presheaf) z
    change (r ^ (n + 1)) • (show F.obj M from
      (colimit.ι SM.presheaf N).hom a) = 0
    refine (integralGerm_smul l E y M N.unop (r ^ (n + 1)) a).symm.trans ?_
    let V := op N.unop.right
    let η := toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
    let c := (integralConstantToCompletion l E Y).hom.app V
      (η.app V (r ^ (n + 1)))
    have hza : c • (show M.val.obj V from a) = 0 := by
      change (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app V c •
        (show (P.X i).val.obj V from a) = 0
      rw [hscalar, zero_smul]
    change (colimit.ι SM.presheaf N).hom (c • (show M.val.obj V from a)) = 0
    rw [hza, map_zero]
  have hd : (r ^ (n + 1)) • 𝟙 (DerivedCategory.Q.obj C) = 0 := by
    rw [← DerivedCategory.Q.map_id, ← Functor.map_smul, hC, Functor.map_zero]
  exact scalar_zero_iso e _ hd

private theorem stalk_source_countableAB4Star
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    CountableAB4Star (scalarReductionSource.{u, u} l E Y) := by
  let A := scalarReductionSource.{u, u} l E Y
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{u, u, 0} Y
          (completedIntegralCommRingSheafUnrestricted l E Y)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat A

/-- Uniformly bounded reductions of a complete sheaf give a bounded complete module stalk.
Source: blueprint `fix-lem-finite-tor-perfect`, proof, integral reconstruction paragraph;
Stacks Tags 0991, 0993 and 091W.
(blueprint: lem-t5-integral-stalk-roos-control).

Proof: the classical pro-etale stalk is evaluation at the pointed strict localization.
It is exact and preserves countable products, also after restricting to the constant
integral scalars. Exact products of module sheaves and modules compute derived products.
The stalk therefore sends the defining completeness triangle to the Roos triangle of
its reduction stalks. Each reduction is killed by the corresponding uniformizer power.
Every element of the uniformizer ideal acts nilpotently on that level. The nilpotent
reduction-limit criterion makes the limit derived complete. Exact stalks and restriction
of scalars preserve the common reduction bounds. Cohomology of a product is its product
of cohomologies, so the Roos long exact sequence bounds the limit in [a,b+1]. The
comparison between the exact derived stalk and termwise stalk transports both assertions.
The empty scheme has no geometric points; zero complexes satisfy both assertions. -/
theorem integralStalk_roos_control
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ)
    (hcomplete : IsSfDerivedComplete l E Y (DerivedCategory.Q.obj K))
    (a b : ℤ) (_hab : a ≤ b)
    (hbound : ∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
        (DerivedCategory.Q.obj K)) ⊆ Set.Icc a b) :
    let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
    let I : Ideal R := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
    let C := DerivedCategory.Q.obj
      (((integralCoefficientModuleStalkFunctor l E y).mapHomologicalComplex (.up ℤ)).obj K)
    (∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj C)) ∧
      DerivedCategory.IsDerivedComplete I C := by
  classical
  dsimp only
  let A := scalarReductionSource.{u, u} l E Y
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let B := ModuleCat.{u + 1} R
  let I : Ideal R := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
  let F := integralCoefficientModuleStalkFunctor l E y
  have hF := stalk_exact_products l E y
  have : PreservesFiniteLimits F := hF.1
  have : PreservesFiniteColimits F := hF.2.1
  have : PreservesLimitsOfShape (Discrete ℕ) F := hF.2.2
  have : CountableAB4Star A := stalk_source_countableAB4Star l E
  have : CountableAB4Star B := point_module_countableAB4Star
  obtain ⟨hPA, hQA, hHA⟩ := derivedCategory_countableProducts_core.{0} A
  let := hPA
  obtain ⟨hPB, hQB, hHB⟩ := derivedCategory_countableProducts_core.{0, u + 1} B
  let := hPB
  have : PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory.{u + 2, u + 1} :=
    exact_derived_preserves_products F
  let L := fun n : ℕ ↦ (sfDerivedReductionRestricted l E Y n).obj (DerivedCategory.Q.obj K)
  let t := fun n ↦ (sfDerivedReductionTransition l E Y n).app (DerivedCategory.Q.obj K)
  obtain ⟨hprod, δ, hT⟩ := hcomplete
  let := hprod
  have hL : IsDerivedLimit t (DerivedCategory.Q.obj K) := ⟨_, δ, hT⟩
  have hFL : IsDerivedLimit
      (K := fun n ↦ F.mapDerivedCategory.{u + 2, u + 1}.obj (L n))
      (fun n ↦ F.mapDerivedCategory.{u + 2, u + 1}.map (t n))
      (F.mapDerivedCategory.{u + 2, u + 1}.obj (DerivedCategory.Q.obj K)) :=
    exact_map_roos F L t _ hL
  let M : DerivedCategory.{u + 1} B :=
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)
  have hM : IsDerivedLimit (K := fun n ↦ F.mapDerivedCategory.{u + 2, u + 1}.obj (L n))
      (fun n ↦ F.mapDerivedCategory.{u + 2, u + 1}.map (t n)) M :=
    roos_of_iso (fun n ↦ F.mapDerivedCategory.{u + 2, u + 1}.obj (L n))
      (fun n ↦ F.mapDerivedCategory.{u + 2, u + 1}.map (t n)) hFL
      (F.mapDerivedCategoryFactors.{u + 2, u + 1}.app K)
  have hz (n : ℕ) (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((DerivedCategory.homologyFunctor B i).obj
        (F.mapDerivedCategory.{u + 2, u + 1}.obj (L n))) := by
    let G := scalarReductionRestriction.{u, u} l E Y n
    let X := (scalarReductionDerivedExtension.{u, u} l E Y n).obj (DerivedCategory.Q.obj K)
    have hzero : IsZero ((DerivedCategory.homologyFunctor _ i).obj X) := by
      by_contra hn
      have hh := hbound n hn
      rcases hi with hi | hi
      · exact (not_le_of_gt hi) hh.1
      · exact (not_le_of_gt hi) hh.2
    let e := (G ⋙ F).mapDerivedCategoryHomologyFunctorIso i
    have hGF : IsZero ((DerivedCategory.homologyFunctor B i).obj
        ((G ⋙ F).mapDerivedCategory.obj X)) :=
      ((G ⋙ F).map_isZero hzero).of_iso (e.app X).symm
    exact hGF.of_iso ((DerivedCategory.homologyFunctor B i).mapIso
      ((Functor.mapDerivedCategoryCompIso G F).app X)).symm
  refine ⟨bounded_of_roos_triangle _ _ M hM a b (hHB ℕ) hz, ?_⟩
  apply DerivedCategory.isDerivedComplete_of_isDerivedLimit_of_nilpotent I
    (fun n ↦ F.mapDerivedCategory.{u + 2, u + 1}.obj (L n))
    (fun n ↦ F.mapDerivedCategory.{u + 2, u + 1}.map (t n))
    _ M hM
  intro r hr n
  exact ⟨n + 1, by omega,
    integralStalk_reduction_nilpotent l E y n
      ((scalarReductionDerivedExtension.{u, u} l E Y n).obj (DerivedCategory.Q.obj K)) r hr⟩

end WeilConjectures
