/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import all WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentRelativeProfiniteSite
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteFunctorExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentTensorNormalization
import WeilConjectures.CategoryTheory.Sites.MonObj

/-! # The abelian monoidal component factorization

Source: Hemo--Richarz--Scholbach, Construction (4.1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
private theorem pushforwardNatTrans_monoidal
    {C D A : Type*} [Category C] [Category D] [Category A]
    [MonoidalCategory A] [BraidedCategory A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
    {F F' : C ⥤ D} [F.IsContinuous J K] [F'.IsContinuous J K]
    (τ : F ⟶ F') :
    let := Sheaf.monoidalCategory J A
    let := Sheaf.monoidalCategory K A
    NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousNatTrans τ A J K) := by
  let := Sheaf.monoidalCategory J A
  let := Sheaf.monoidalCategory K A
  constructor
  · apply Sheaf.unit_hom_ext
    rw [Functor.map_comp, ← Category.assoc,
      Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous,
      Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous]
    ext U
    simpa using ((Functor.LaxMonoidal.ε (sheafToPresheaf K A)).naturality
      (τ.app U.unop).op).symm
  · intro X Y
    apply Sheaf.tensor_hom_ext
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
      Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous,
      ← Functor.LaxMonoidal.μ_natural_assoc,
      Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous]
    ext U
    change (𝟙 _ ≫ _) ≫ _ = _ ≫ 𝟙 _ ≫ _
    rw [Category.id_comp, Category.id_comp]
    convert ((Functor.LaxMonoidal.μ (sheafToPresheaf K A) X Y).naturality
      (τ.app U.unop).op).symm using 1 <;> rfl


namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

omit [(componentInverse T).Braided] [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)] in
/-- The relative component inverse image factors the point inverse image on abelian sheaves.
Source: Hemo--Richarz--Scholbach, Construction (4.1)
(blueprint: lem-zl-component-point-monoidal-factorization).

Proof: identify restriction along the composite relative-test functor with restriction
along the absolute profinite test functor. The relative universal property identifies
these functors first on finite tests, and preservation of the canonical cofiltered limits
extends the identification to all profinite tests. Take the mate of this identification
under the sheafified Kan-extension adjunctions. This gives an isomorphism on abelian
sheaves, since addition and zero are preserved by the product comparisons. The unit and
tensor equations can be checked after taking the same adjunction mates: both sides are
the identical restriction maps. Thus the isomorphism is monoidal for the fixed inverse
image structures. Empty tests are included by the empty cover. -/
private theorem canonical_point_factorization :
    ∃ β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
        (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T,
      let := (componentCanonicalMonoidal T).toLaxMonoidal
      NatTrans.IsMonoidal β.hom := by
  classical
  let : (componentInverse T).LaxMonoidal := (componentCanonicalMonoidal T).toLaxMonoidal
  let F := componentTests T
  have hF := Classical.choose_spec (component_relative_profinite_site T)
  change _ at hF
  obtain ⟨p, hp, hnat, hmap⟩ := hF.2.1
  have : PreservesFiniteLimits F := hF.2.2.2.2.2.1
  let S := affineComponentSpace T
  let J := coherentTopology Profinite.{u}
  let K := J.over S
  let L := Scheme.ProEt.topology T
  let G₀ := Over.star S ⋙ F
  let G := G₀ ⋙ Scheme.ProEt.forget T
  let H := profiniteToProEtOf T ⋙ Scheme.ProEt.forget T
  have hGc : G₀.IsContinuous J L :=
    Functor.isContinuous_comp (Over.star S) F J K L
  have : G.IsContinuous J (Scheme.proetaleTopology.over T) :=
    Functor.isContinuous_comp G₀ (Scheme.ProEt.forget T) J L _
  have hcop (A : Type u) [Finite A] : PreservesColimitsOfShape (Discrete A) G :=
    component_coproducts_of_continuous G (Scheme.proetaleTopology.over T) A
  let et : G.obj component_point ≅ Over.mk (𝟙 T) :=
    (Profinite.isTerminalPUnit.isTerminalObj G _).uniqueUpToIso Over.mkIdTerminal
  let eG := (component_finiteIso G hcop).some ≪≫
    Functor.isoWhiskerLeft (forget FintypeCat) (sigmaConst.mapIso et)
  obtain ⟨eH⟩ := (profinite_test_object_functor T).2.2.1
  have hGl (P : Profinite.{u}) : Nonempty (IsLimit (G.mapCone P.asLimitCone)) :=
    component_preserves_limits T F p hp hnat hmap (P.diagram ⋙ Over.star S)
      ((Over.star S).mapCone P.asLimitCone)
      (isLimitOfPreserves (Over.star S) P.asLimit)
  have hHl (P : Profinite.{u}) : Nonempty (IsLimit (H.mapCone P.asLimitCone)) :=
    (profinite_test_object_functor T).2.2.2.1 _ P.fintypeDiagram P.asLimitCone P.asLimit
      (fun Q ↦ DiscreteQuotient.proj_surjective Q)
  obtain ⟨e⟩ := Profinite.functor_iso_of_finite G H hGl hHl (eG ≪≫ eH.symm)
  let e₀ : G₀ ≅ profiniteToProEtOf T :=
    Functor.fullyFaithfulCancelRight (Scheme.ProEt.forget T) e
  have hHc : (profiniteToProEtOf T).IsContinuous J L :=
    Functor.isContinuous_comp profiniteToProEt
      (Scheme.proEtaleBaseChange (toSpecZ T)) J (Scheme.ProEt.topology specZ) L
  have : (profiniteToProEt ⋙ Scheme.proEtaleBaseChange (toSpecZ T)).IsContinuous J L :=
    hHc
  let qa := (Over.forgetAdjStar S).sheafPushforwardContinuous (E := Ab.{u + 1}) K J
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let : (Functor.sheafPullbackConstruction.sheafPullback F Ab.{u + 1} K L).Monoidal :=
    componentCanonicalMonoidal T
  let fa := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{u + 1} K L
  let a := qa.comp fa
  let b := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))
  let d := Functor.sheafPushforwardContinuousComp' e₀ Ab.{u + 1} J K L ≪≫
    (Functor.sheafPushforwardContinuousComp'
      (Iso.refl (profiniteToProEt ⋙ Scheme.proEtaleBaseChange (toSpecZ T))) Ab.{u + 1}
      J (Scheme.ProEt.topology specZ) L).symm
  let β := (conjugateIsoEquiv b a).symm d.symm
  refine ⟨β, ?_⟩
  have hfc : NatTrans.IsMonoidal fa.counit := by infer_instance
  have hbc : NatTrans.IsMonoidal b.unit := by infer_instance
  have : (Over.forget S ⋙ Over.star S).IsContinuous K K :=
    Functor.isContinuous_comp (Over.forget S) (Over.star S) K J K
  have hqc : NatTrans.IsMonoidal qa.counit := by
    let c := Functor.sheafPushforwardContinuousComp'
      (Iso.refl (Over.forget S ⋙ Over.star S)) Ab.{u + 1} K J K
    have hτ := pushforwardNatTrans_monoidal (A := Ab.{u + 1}) K K (Over.forgetAdjStar S).unit
    have hc : NatTrans.IsMonoidal c.hom := by infer_instance
    have hh : qa.counit = c.hom ≫
        Functor.sheafPushforwardContinuousNatTrans (Over.forgetAdjStar S).unit
          Ab.{u + 1} K K ≫
        (Functor.sheafPushforwardContinuousId' (Iso.refl _) Ab.{u + 1} K).hom := by
      apply NatTrans.ext
      funext P
      apply ObjectProperty.hom_ext
      ext U
      simp [qa, c, Adjunction.sheafPushforwardContinuous,
        Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
        Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousId]
      rfl
    rw [hh]
    infer_instance
  have hac : NatTrans.IsMonoidal a.counit := by
    change NatTrans.IsMonoidal
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ qa.counit ≫ (Functor.rightUnitor _).hom) _ ≫ fa.counit)
    infer_instance
  have hd : NatTrans.IsMonoidal d.inv := by
    dsimp only [d, Iso.trans_inv, Iso.symm_inv]
    infer_instance
  let q := J.overPullback Ab.{u + 1} S ⋙
    Functor.sheafPullbackConstruction.sheafPullback F Ab.{u + 1} K L
  let z : q ⟶ upperStarFromPoint T :=
    q.leftUnitor.inv ≫ Functor.whiskerRight b.unit q ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStarFromPoint T) (Functor.whiskerRight d.inv q) ≫
      Functor.whiskerLeft (upperStarFromPoint T) a.counit ≫
      (upperStarFromPoint T).rightUnitor.hom
  have hz : β.hom = z := by
    ext X
    simp [β, z, q, K, GrothendieckTopology.overPullback, F, upperStarFromPoint,
      conjugateIsoEquiv, conjugateEquiv, mateEquiv]
  have hzmono : NatTrans.IsMonoidal z := by
    dsimp only [z]
    infer_instance
  rw [hz]
  exact hzmono


omit [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)] in
private theorem correction_unit :
    Functor.LaxMonoidal.ε (componentInverse T) ≫
      (componentUnitCorrection T).hom.app (𝟙_ _) =
        (componentCanonicalMonoidal T).toLaxMonoidal.ε := by
  let e := componentUnitRatio T
  let ε₁ := Functor.LaxMonoidal.ε (componentInverse T)
  let s : 𝟭 (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ≅ 𝟭 _ :=
    (MonoidalCategory.leftUnitorNatIso _).symm ≪≫
      (MonoidalCategory.curriedTensor _).mapIso e ≪≫ MonoidalCategory.leftUnitorNatIso _
  have hs : s.hom.app (𝟙_ _) = e.hom := by
    change (λ_ _).inv ≫ e.hom ▷ (𝟙_ _) ≫ (λ_ _).hom = e.hom
    rw [MonoidalCategory.unitors_inv_equal, MonoidalCategory.unitors_equal,
      MonoidalCategory.rightUnitor_naturality]
    simp
  change ε₁ ≫ s.hom.app _ = _
  have hn := s.hom.naturality ε₁
  change ε₁ ≫ s.hom.app _ = s.hom.app _ ≫ ε₁ at hn
  refine hn.trans ?_
  change s.hom.app (𝟙_ _) ≫ ε₁ = _
  rw [hs]
  simp [e, componentUnitRatio, ε₁]

set_option linter.unusedSectionVars false in
/-- The relative component inverse image factors the point inverse image on abelian sheaves.
Source: Hemo--Richarz--Scholbach, Construction (4.1)
(blueprint: lem-zl-component-point-monoidal-factorization).

Proof: compare relative and absolute tests on finite sets and canonical profinite limits.
Take the adjunction mate on abelian sheaves. The canonical mate is monoidal by its
unit--restriction--counit formula. Correct the supplied structure by the scalar ratio
of its unit comparison and the canonical unit comparison; its tensor identity is
`component_unit_normalized_tensor`. Whisker this correction by slice restriction
and compose with the canonical mate. -/
theorem component_point_monoidal_factorization :
    ∃ β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
        (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T,
      NatTrans.IsMonoidal β.hom := by
  let q := (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
    (affineComponentSpace T)
  obtain ⟨β₀, hβ₀⟩ := canonical_point_factorization T
  let γ := componentUnitCorrection T
  let β := Functor.isoWhiskerLeft q γ ≪≫ β₀
  refine ⟨β, ?_⟩
  constructor
  · dsimp only [β, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [Functor.LaxMonoidal.comp_ε]
    slice_lhs 2 3 => exact γ.hom.naturality _
    simp only [← Category.assoc]
    rw [correction_unit]
    exact hβ₀.unit
  · intro X Y
    dsimp only [β, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [Functor.LaxMonoidal.comp_μ]
    slice_lhs 2 3 => exact γ.hom.naturality _
    simp only [← Category.assoc]
    rw [component_unit_normalized_tensor]
    have h := hβ₀.tensor X Y
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simpa only [Functor.LaxMonoidal.comp_μ, Category.assoc] using
      congrArg (fun f ↦ (γ.hom.app (q.obj X) ⊗ₘ γ.hom.app (q.obj Y)) ≫ f) h

end AlgebraicGeometry.ProEtale.CondensedRing
