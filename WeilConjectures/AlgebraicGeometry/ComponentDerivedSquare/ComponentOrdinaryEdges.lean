/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentLiftBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
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
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
public import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentAbsoluteTests

/-! # Coefficient-normalized ordinary component edges

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

/-- The edges and the intrinsic slice coherence, before any component square.
Source: HRS (4.1) (blueprint: lem-zl-component-ordinary-edges). -/
structure OrdinaryEdges (Λ : Profinite.CondensedRing.{u}) where
  corner : ∀ (X : Scheme.{u}) [IsAffine X], Corner Λ X
  slice : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
    Slice Λ (affineComponentMap f)
  identity : ∀ (X : Scheme.{u}) [IsAffine X], SliceIdentity Λ X (slice (𝟙 X))
  composition : ∀ {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y),
    SliceComposition Λ f g (slice f) (slice g) (slice (g ≫ f))

private theorem restriction_monoidal
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

private theorem restriction_adj_counit_monoidal
    {C D A : Type*} [Category C] [Category D] [Category A]
    [MonoidalCategory A] [BraidedCategory A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
    {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J]
    (a : F ⊣ G) :
    let := Sheaf.monoidalCategory J A
    let := Sheaf.monoidalCategory K A
    NatTrans.IsMonoidal (a.sheafPushforwardContinuous J K (E := A)).counit := by
  let := Sheaf.monoidalCategory J A
  let := Sheaf.monoidalCategory K A
  have : (F ⋙ G).IsContinuous J J := Functor.isContinuous_comp F G J K J
  let c := Functor.sheafPushforwardContinuousComp' (Iso.refl (F ⋙ G)) A J K J
  have ht := restriction_monoidal (A := A) J J a.unit
  have hh : (a.sheafPushforwardContinuous J K (E := A)).counit = c.hom ≫
      Functor.sheafPushforwardContinuousNatTrans a.unit A J J ≫
      (Functor.sheafPushforwardContinuousId' (Iso.refl _) A J).hom := by
    ext P U
    simp only [c, Iso.trans_hom, Iso.refl_hom,
      Functor.sheafPushforwardContinuousIso_hom,
      Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.comp_obj, Functor.id_obj,
      Adjunction.sheafPushforwardContinuous_counit_app_hom_app, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
      Functor.whiskerRight_app, Functor.op_obj, op_unop, NatTrans.op_app,
      Functor.sheafPushforwardContinuousId'_hom_app_hom_app, Iso.refl_inv,
      NatTrans.id_app, op_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    change P.obj.map _ = 𝟙 _ ≫ P.obj.map _ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  rw [hh]
  dsimp only [c]
  infer_instance

private theorem restriction_adj_unit_monoidal
    {C D A : Type*} [Category C] [Category D] [Category A]
    [MonoidalCategory A] [BraidedCategory A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
    {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J]
    (a : F ⊣ G) :
    let := Sheaf.monoidalCategory J A
    let := Sheaf.monoidalCategory K A
    NatTrans.IsMonoidal (a.sheafPushforwardContinuous J K (E := A)).unit := by
  let := Sheaf.monoidalCategory J A
  let := Sheaf.monoidalCategory K A
  have : (G ⋙ F).IsContinuous K K := Functor.isContinuous_comp G F K J K
  let c := Functor.sheafPushforwardContinuousComp' (Iso.refl (G ⋙ F)) A K J K
  have ht := restriction_monoidal (A := A) K K a.counit
  have hh : (a.sheafPushforwardContinuous J K (E := A)).unit =
      (Functor.sheafPushforwardContinuousId' (Iso.refl _) A K).inv ≫
      Functor.sheafPushforwardContinuousNatTrans a.counit A K K ≫ c.inv := by
    ext P U
    simp only [c, Iso.trans_inv, Iso.refl_inv,
      Functor.sheafPushforwardContinuousIso_inv,
      Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Functor.id_obj, Functor.comp_obj,
      Adjunction.sheafPushforwardContinuous_unit_app_hom_app, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
      Functor.sheafPushforwardContinuousId'_inv_app_hom_app, op_unop, Iso.refl_hom,
      NatTrans.id_app, op_id, CategoryTheory.Functor.map_id, Functor.whiskerRight_app,
      Functor.op_obj, NatTrans.op_app, Category.id_comp]
    change P.obj.map _ = P.obj.map _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
  rw [hh]
  dsimp only [c]
  infer_instance

private theorem lax_mate_monoidal
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.LaxMonoidal] [L₂.LaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    [NatTrans.IsMonoidal a.unit] [NatTrans.IsMonoidal b.counit]
    (d : R₁ ≅ R₂) [NatTrans.IsMonoidal d.hom] :
    NatTrans.IsMonoidal ((conjugateIsoEquiv a b).symm d).hom := by
  let z : L₂ ⟶ L₁ :=
    L₂.leftUnitor.inv ≫ Functor.whiskerRight a.unit L₂ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L₁ (Functor.whiskerRight d.hom L₂) ≫
      Functor.whiskerLeft L₁ b.counit ≫ L₁.rightUnitor.hom
  have hz : ((conjugateIsoEquiv a b).symm d).hom = z := by
    ext X
    simp [z, conjugateIsoEquiv, conjugateEquiv, mateEquiv]
  rw [hz]
  dsimp only [z]
  infer_instance

private local instance componentContinuous (X : Scheme.{u}) [IsAffine X] :
    (CondensedRing.componentTests X).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X) := by
  let F := CondensedRing.componentTests X
  have hF := (component_relative_profinite_site X).choose_spec
  -- Continuity is a consequence of the stated covering and limit properties.
  have : PreservesFiniteLimits F := hF.2.2.2.2.2.1
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits _
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  constructor
  intro E R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨I, hI, V, f, hf, hm⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp hR
  let E₀ : I → Over (affineComponentSpace X) := fun i ↦ Over.mk (f i ≫ E.hom)
  let a : ∀ i, E₀ i ⟶ E := fun i ↦ Over.homMk (f i) rfl
  have hjs : ∀ e : E.left, ∃ i x, (a i).left x = e :=
    ((Profinite.effectiveEpiFamily_tfae V f).out 0 2).mp hf
  have hc := hF.2.2.2.2.2.2.2.1 (ULift.{u} I) (fun i ↦ E₀ i.down) E
    (fun i ↦ a i.down) (by
      intro x
      obtain ⟨i, y, hy⟩ := hjs x
      exact ⟨⟨i⟩, y, hy⟩)
  apply (Scheme.ProEt.topology X).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hc)
  apply (Sieve.generate_le_iff _ _).mpr
  intro W g hg
  obtain ⟨i⟩ := hg
  exact ⟨E₀ i.down, a i.down, 𝟙 _, (Sieve.overEquiv_iff R (f i.down)).mp (hm i.down),
    (Category.id_comp _).symm⟩

private local instance componentMonoidal (X : Scheme.{u}) [IsAffine X] :
    (CondensedRing.componentInverse X).Monoidal := by
  let : PreservesFiniteLimits (CondensedRing.componentTests X) :=
    (component_relative_profinite_site X).choose_spec.2.2.2.2.2.1
  let : RepresentablyFlat (CondensedRing.componentTests X) := flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.sheafPullbackMonoidal _ _ _ _

private local instance componentRawMonoidal (X : Scheme.{u}) [IsAffine X] :
    (Functor.sheafPullbackConstruction.sheafPullback (CondensedRing.componentTests X)
      Ab.{u + 1} ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (Scheme.ProEt.topology X)).Monoidal := componentMonoidal X

private local instance absoluteTestsContinuous (X : Scheme.{u}) :
    (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology X) :=
  Functor.isContinuous_comp profiniteToProEt (Scheme.proEtaleBaseChange (toSpecZ X))
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)

private local instance componentBraided (X : Scheme.{u}) [IsAffine X] :
    (CondensedRing.componentInverse X).Braided :=
  { braided := (componentAdjunction X (componentContinuous X)).μ_comp_map_braiding }

private local instance componentLimits (X : Scheme.{u}) [IsAffine X] :
    PreservesFiniteLimits (CondensedRing.componentInverse X) := by
  let : PreservesFiniteLimits (CondensedRing.componentTests X) :=
    (component_relative_profinite_site X).choose_spec.2.2.2.2.2.1
  let : RepresentablyFlat (CondensedRing.componentTests X) := flat_of_preservesFiniteLimits _
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  unfold CondensedRing.componentInverse
  infer_instance

private local instance componentColimits (X : Scheme.{u}) [IsAffine X] :
    PreservesFiniteColimits (CondensedRing.componentInverse X) := by
  have : PreservesColimitsOfSize.{0, 0} (CondensedRing.componentInverse X) :=
    (componentAdjunction X (componentContinuous X)).leftAdjoint_preservesColimits
  infer_instance

private def absoluteBeta (X : Scheme.{u}) [IsAffine X]
    (e : Over.star (affineComponentSpace X) ⋙ CondensedRing.componentTests X ≅
      profiniteToProEtOf X) :
    (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} (affineComponentSpace X) ⋙
      CondensedRing.componentInverse X ≅ upperStarFromPoint X := by
  let d := Functor.sheafPushforwardContinuousComp' e Ab.{u + 1}
    (coherentTopology Profinite.{u})
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)
  exact (conjugateIsoEquiv (absoluteAdjunction X)
    ((slicePointAdjunction (affineComponentSpace X)).comp
      (componentAdjunction X (componentContinuous X)))).symm d.symm

private theorem cornerOfTests (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (e : Over.star (affineComponentSpace X) ⋙ CondensedRing.componentTests X ≅
      profiniteToProEtOf X)
    (he : ∀ S z, (prod.snd : affineComponentSpace X ⨯ S ⟶ S)
      (relativeComponentCoordinate X ((Over.star (affineComponentSpace X)).obj S) z) =
        profiniteTestProjection X S ((e.hom.app S).left z)) : Nonempty (Corner Λ X) := by
  let β := absoluteBeta X e
  have : NatTrans.IsMonoidal β.hom := absoluteBetaMonoidal X e
  let c := ((Functor.mapMonCompIso
    (F := (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} (affineComponentSpace X))
    (G := CondensedRing.componentInverse X)).symm ≪≫
      Functor.mapMonNatIso β).app (Mon.mk Λ.X)
  refine ⟨{
    inverse := CondensedRing.componentInverse X
    inverse_eq := rfl
    adjunction := componentAdjunction X (componentContinuous X)
    adjunction_eq := HEq.rfl
    tensor_canonical := fun A B ↦ rfl
    unit_canonical := rfl
    absoluteTests := e
    absolute_coordinate := he
    beta := β
    beta_mate := ?_
    coefficient := c
    coefficient_eq := ?_ }⟩
  · intro G S
    have hm : conjugateIsoEquiv
        ((slicePointAdjunction (affineComponentSpace X)).comp
          (componentAdjunction X (componentContinuous X))) (absoluteAdjunction X) β.symm =
        Functor.sheafPushforwardContinuousComp' e Ab.{u + 1}
          (coherentTopology Profinite.{u})
          ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
          (Scheme.ProEt.topology X) := by
      rw [conjugateIsoEquiv_iso_symm]
      simp only [β, absoluteBeta, Equiv.apply_symm_apply, Iso.symm_symm_eq]
    erw [hm]
    simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp]
  · change 𝟙 _ ≫ (absoluteBeta X e).hom.app Λ.X = (absoluteBeta X e).hom.app Λ.X
    exact Category.id_comp _

private theorem restriction_conjugate
    {C D A : Type*} [Category C] [Category D] [Category A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C}
    [F₁.IsContinuous J K] [F₂.IsContinuous J K]
    [G₁.IsContinuous K J] [G₂.IsContinuous K J]
    (a : F₁ ⊣ G₁) (b : F₂ ⊣ G₂) (e : F₂ ≅ F₁) :
    conjugateIsoEquiv (a.sheafPushforwardContinuous J K (E := A))
        (b.sheafPushforwardContinuous J K (E := A))
        (Functor.sheafPushforwardContinuousIso e A J K) =
      Functor.sheafPushforwardContinuousIso (conjugateIsoEquiv a b e) A K J := by
  ext P E
  simp only [conjugateIsoEquiv_apply_hom, Functor.sheafPushforwardContinuousIso_hom,
    conjugateEquiv_apply_app, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.sheafPushforwardContinuous_unit_app_hom_app,
    Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
    Functor.whiskerRight_app, Functor.op_obj, NatTrans.op_app,
    Adjunction.sheafPushforwardContinuous_counit_app_hom_app, conjugateIsoEquiv_apply_inv,
    op_comp, Category.assoc, CategoryTheory.Functor.map_comp]

private local instance absoluteBetaMonoidal (X : Scheme.{u}) [IsAffine X]
    (e : Over.star (affineComponentSpace X) ⋙ CondensedRing.componentTests X ≅
      profiniteToProEtOf X) : NatTrans.IsMonoidal (absoluteBeta X e).hom := by
  have : (profiniteToProEt ⋙ Scheme.proEtaleBaseChange (toSpecZ X)).IsContinuous
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X) := absoluteTestsContinuous X
  let c := Functor.sheafPushforwardContinuousComp profiniteToProEt
    (Scheme.proEtaleBaseChange (toSpecZ X)) Ab.{u + 1} (coherentTopology Profinite.{u})
    (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)
  have hc₀ : NatTrans.IsMonoidal c.hom := by
    let d := Functor.sheafPushforwardContinuousComp'
      (Iso.refl (profiniteToProEt ⋙ Scheme.proEtaleBaseChange (toSpecZ X))) Ab.{u + 1}
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)
    have hd : NatTrans.IsMonoidal d.hom := by dsimp only [d]; infer_instance
    have he : c.hom = d.hom := by
      ext G U
      simp [c, d, Functor.sheafPushforwardContinuousComp',
        Functor.sheafPushforwardContinuousComp]
      rfl
    rw [he]
    exact hd
  have hu₀ : (absoluteAdjunction X).IsMonoidal := by
    unfold absoluteAdjunction
    apply Adjunction.isMonoidal_ofNatIsoRight
  have hu : NatTrans.IsMonoidal (absoluteAdjunction X).unit := by infer_instance
  have hc : NatTrans.IsMonoidal
      (slicePointAdjunction (affineComponentSpace X)).counit :=
    restriction_adj_counit_monoidal (A := Ab.{u + 1})
      ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      (coherentTopology Profinite.{u}) (Over.forgetAdjStar _)
  have : NatTrans.IsMonoidal
      ((slicePointAdjunction (affineComponentSpace X)).comp
        (componentAdjunction X (componentContinuous X))).counit := by
    change NatTrans.IsMonoidal
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (slicePointAdjunction (affineComponentSpace X)).counit ≫
          (Functor.rightUnitor _).hom) _ ≫
            (componentAdjunction X (componentContinuous X)).counit)
    infer_instance
  let d := Functor.sheafPushforwardContinuousComp' e Ab.{u + 1}
    (coherentTopology Profinite.{u})
    ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
    (Scheme.ProEt.topology X)
  let : NatTrans.IsMonoidal d.symm.hom := by
    change NatTrans.IsMonoidal d.inv
    dsimp only [d]
    infer_instance
  exact lax_mate_monoidal (absoluteAdjunction X)
    ((slicePointAdjunction (affineComponentSpace X)).comp
      (componentAdjunction X (componentContinuous X))) d.symm

private local instance sliceMonoidal {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (sliceInverse h).Monoidal := by
  let : RepresentablyFlat (Over.pullback h) := flat_of_preservesFiniteLimits _
  exact Functor.sheafPullbackConstruction.sheafPullbackMonoidal _ _ _ _

private local instance sliceBraided {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (sliceInverse h).Braided :=
  { braided := (sliceAdjunction h).μ_comp_map_braiding }

private local instance sliceLimits {P Q : Profinite.{u}} (h : Q ⟶ P) :
    PreservesFiniteLimits (sliceInverse h) := by
  let : RepresentablyFlat (Over.pullback h) := flat_of_preservesFiniteLimits _
  have : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  unfold sliceInverse
  infer_instance

private local instance sliceColimits {P Q : Profinite.{u}} (h : Q ⟶ P) :
    PreservesFiniteColimits (sliceInverse h) := by
  have : PreservesColimitsOfSize.{0, 0} (sliceInverse h) :=
    (sliceAdjunction h).leftAdjoint_preservesColimits
  infer_instance

private theorem restriction_comp
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E} {G' : E ⥤ D}
    [F.IsContinuous J K] [G.IsContinuous K J]
    [F'.IsContinuous K L] [G'.IsContinuous L K]
    (a : F ⊣ G) (b : F' ⊣ G') :
    letI := Functor.isContinuous_comp F F' J K L
    letI := Functor.isContinuous_comp G' G L K J
    (b.sheafPushforwardContinuous K L (E := A)).comp
        (a.sheafPushforwardContinuous J K (E := A)) =
      (a.comp b).sheafPushforwardContinuous J L (E := A) := by
  apply Adjunction.ext
  ext P E
  simp [Adjunction.sheafPushforwardContinuous, Adjunction.comp_unit_app,
    ← Functor.map_comp, ← op_comp]

private theorem star_conjugate {P Q : Profinite.{u}} (h : Q ⟶ P) :
    conjugateIsoEquiv ((Over.mapPullbackAdj h).comp (Over.forgetAdjStar P))
      (Over.forgetAdjStar Q) (Iso.refl (Over.forget Q)) = Over.starPullbackIsoStar h := by
  apply Iso.ext
  apply NatTrans.ext
  funext S
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp [conjugateIsoEquiv, conjugateEquiv, mateEquiv,
      Adjunction.comp_counit_app, Over.starPullbackIsoStar]
  · simp [conjugateIsoEquiv, conjugateEquiv, mateEquiv,
      Adjunction.comp_counit_app, Over.starPullbackIsoStar]

private theorem restriction_comp_iso
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous J L]
    (e : F ⋙ G ≅ H) :
    letI := Functor.isContinuous_comp F G J K L
    Functor.sheafPushforwardContinuousComp' e A J K L =
      Functor.sheafPushforwardContinuousIso e A J L := by
  ext P U
  simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp]

private theorem restriction_id_iso
    {C A : Type*} [Category C] [Category A]
    (J : GrothendieckTopology C) {F : C ⥤ C} [F.IsContinuous J J]
    (e : F ≅ 𝟭 C) :
    Functor.sheafPushforwardContinuousId' e A J =
      Functor.sheafPushforwardContinuousIso e A J J := by
  ext P U
  simp [Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousId]

private theorem restriction_identity_adjunction
    {C A : Type*} [Category C] [Category A] (J : GrothendieckTopology C) :
    (Adjunction.id (C := C)).sheafPushforwardContinuous J J (E := A) =
      Adjunction.id := by
  apply Adjunction.ext
  ext P U
  simp [Adjunction.sheafPushforwardContinuous]

private abbrev sliceRestriction {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  (coherentTopology Profinite.{u}).overMapPullback Ab.{u + 1} h

private def restrictionAdjunction {P Q : Profinite.{u}} (h : Q ⟶ P) :=
  (Over.mapPullbackAdj h).sheafPushforwardContinuous
    ((coherentTopology Profinite.{u}).over Q) ((coherentTopology Profinite.{u}).over P)
    (E := Ab.{u + 1})

private def restrictionComparison {P Q : Profinite.{u}} (h : Q ⟶ P) :
    sliceInverse h ≅ sliceRestriction h :=
  (sliceAdjunction h).leftAdjointUniq (restrictionAdjunction h)

private local instance restrictionComparisonMonoidal {P Q : Profinite.{u}} (h : Q ⟶ P) :
    NatTrans.IsMonoidal (restrictionComparison h).hom := by
  have hu : NatTrans.IsMonoidal (restrictionAdjunction h).unit :=
    restriction_adj_unit_monoidal _ _ (Over.mapPullbackAdj h)
  have hd : NatTrans.IsMonoidal (Iso.refl (sliceDirect h)).hom := by
    change NatTrans.IsMonoidal (𝟙 (sliceDirect h))
    infer_instance
  have ht := lax_mate_monoidal (restrictionAdjunction h) (sliceAdjunction h)
    (Iso.refl (sliceDirect h))
  exact ht

private def restrictionPointComparison {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P ⋙ sliceRestriction h ≅
      (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} Q :=
  Functor.sheafPushforwardContinuousComp'
    (F := Over.map h) (G := Over.forget P) (Iso.refl (Over.forget Q)) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over Q)
    ((coherentTopology Profinite.{u}).over P) (coherentTopology Profinite.{u})

private def normalizedSliceBeta {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P ⋙ sliceInverse h ≅
      (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} Q :=
  Functor.isoWhiskerLeft
      ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P)
      (restrictionComparison h) ≪≫ restrictionPointComparison h

private def restrictionIdentity (P : Profinite.{u}) :
    sliceRestriction (𝟙 P) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (Over.mapId P) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over P)

private def normalizedSliceIdentity (P : Profinite.{u}) :
    sliceInverse (𝟙 P) ≅ 𝟭 _ :=
  restrictionComparison (𝟙 P) ≪≫ restrictionIdentity P

private def restrictionComposition {P Q R : Profinite.{u}}
    (f : Q ⟶ P) (g : R ⟶ Q) :
    sliceRestriction (g ≫ f) ≅ sliceRestriction f ⋙ sliceRestriction g :=
  (Functor.sheafPushforwardContinuousComp' (Over.mapComp g f).symm Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over R)
    ((coherentTopology Profinite.{u}).over Q)
    ((coherentTopology Profinite.{u}).over P)).symm

private def normalizedSliceComposition {P Q R : Profinite.{u}}
    (f : Q ⟶ P) (g : R ⟶ Q) :
    sliceInverse (g ≫ f) ≅ sliceInverse f ⋙ sliceInverse g :=
  restrictionComparison (g ≫ f) ≪≫ restrictionComposition f g ≪≫
    Functor.isoWhiskerLeft (sliceRestriction f) (restrictionComparison g).symm ≪≫
    Functor.isoWhiskerRight (restrictionComparison f).symm (sliceInverse g)

private local instance normalizedSliceBetaMonoidal {P Q : Profinite.{u}} (h : Q ⟶ P) :
    NatTrans.IsMonoidal (normalizedSliceBeta h).hom := by
  dsimp only [normalizedSliceBeta, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  have : NatTrans.IsMonoidal (restrictionPointComparison h).hom := by
    dsimp only [restrictionPointComparison]
    infer_instance
  infer_instance

private local instance normalizedSliceIdentityMonoidal (P : Profinite.{u}) :
    NatTrans.IsMonoidal (normalizedSliceIdentity P).hom := by
  have : NatTrans.IsMonoidal (restrictionIdentity P).hom := by
    dsimp only [restrictionIdentity]
    infer_instance
  dsimp only [normalizedSliceIdentity, Iso.trans_hom]
  infer_instance

private local instance normalizedSliceCompositionMonoidal {P Q R : Profinite.{u}}
    (f : Q ⟶ P) (g : R ⟶ Q) :
    NatTrans.IsMonoidal (normalizedSliceComposition f g).hom := by
  have : NatTrans.IsMonoidal (restrictionComposition f g).hom := by
    change NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousComp'
      (Over.mapComp g f).symm Ab.{u + 1} _ _ _).inv
    infer_instance
  dsimp only [normalizedSliceComposition, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

private theorem normalized_mate
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Q₁ : A ⥤ B} {Q₂ : A ⥤ C} {S₁ : B ⥤ A} {S₂ : C ⥤ A}
    {L T : B ⥤ C} {R : C ⥤ B}
    (p : Q₁ ⊣ S₁) (q : Q₂ ⊣ S₂) (a : L ⊣ R) (t : T ⊣ R)
    (c : Q₁ ⋙ T ≅ Q₂) :
    conjugateIsoEquiv (p.comp a) q
        (c.symm ≪≫ Functor.isoWhiskerLeft Q₁ (a.leftAdjointUniq t).symm) =
      conjugateIsoEquiv (p.comp t) q c.symm := by
  rw [conjugateIsoEquiv_trans (p.comp a) (p.comp t) q,
    conjugateIsoEquiv_isoWhiskerLeft]
  simp [Adjunction.leftAdjointUniq]

private theorem restriction_point_mate {P Q : Profinite.{u}} (h : Q ⟶ P) :
    conjugateIsoEquiv ((slicePointAdjunction P).comp (restrictionAdjunction h))
        (slicePointAdjunction Q) (restrictionPointComparison h).symm =
      Functor.sheafPushforwardContinuousComp' (Over.starPullbackIsoStar h)
        Ab.{u + 1} (coherentTopology Profinite.{u})
        ((coherentTopology Profinite.{u}).over P)
        ((coherentTopology Profinite.{u}).over Q) := by
  let J := coherentTopology Profinite.{u}
  let K := J.over Q
  let L := J.over P
  have hcomp := restriction_comp (A := Ab.{u + 1}) K L J
    (Over.mapPullbackAdj h) (Over.forgetAdjStar P)
  have : (Over.map h ⋙ Over.forget P).IsContinuous K J :=
    Functor.isContinuous_comp (Over.map h) (Over.forget P) K L J
  have : (Over.star P ⋙ Over.pullback h).IsContinuous J K :=
    Functor.isContinuous_comp (Over.star P) (Over.pullback h) J L K
  change conjugateIsoEquiv
    (((Over.forgetAdjStar P).sheafPushforwardContinuous L J (E := Ab.{u + 1})).comp
      ((Over.mapPullbackAdj h).sheafPushforwardContinuous K L (E := Ab.{u + 1})))
    ((Over.forgetAdjStar Q).sheafPushforwardContinuous K J (E := Ab.{u + 1})) _ = _
  rw [hcomp]
  have he : (restrictionPointComparison h).symm =
      Functor.sheafPushforwardContinuousIso (Iso.refl (Over.forget Q))
        Ab.{u + 1} K J := by
    ext G E
    simp [restrictionPointComparison, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp]
  rw [he]
  erw [restriction_conjugate]
  rw [star_conjugate]
  rw [restriction_comp_iso]

private theorem normalizedSliceBeta_mate {P Q : Profinite.{u}} (h : Q ⟶ P) :
    conjugateIsoEquiv ((slicePointAdjunction P).comp (sliceAdjunction h))
        (slicePointAdjunction Q) (normalizedSliceBeta h).symm =
      Functor.sheafPushforwardContinuousComp' (Over.starPullbackIsoStar h)
        Ab.{u + 1} (coherentTopology Profinite.{u})
        ((coherentTopology Profinite.{u}).over P)
        ((coherentTopology Profinite.{u}).over Q) := by
  unfold normalizedSliceBeta restrictionComparison
  rw [Iso.trans_symm, Functor.isoWhiskerLeft_symm]
  erw [normalized_mate]
  exact restriction_point_mate h

private theorem normalized_identity_mate
    {A : Type*} [Category A]
    {L T : A ⥤ A} {R : A ⥤ A}
    (a : L ⊣ R) (t : T ⊣ R) (c : T ≅ 𝟭 A) :
    conjugateIsoEquiv a Adjunction.id ((a.leftAdjointUniq t ≪≫ c).symm) =
      conjugateIsoEquiv t Adjunction.id c.symm := by
  rw [Iso.trans_symm, conjugateIsoEquiv_trans a t Adjunction.id]
  simp [Adjunction.leftAdjointUniq]

private theorem normalized_composition_mate
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L₁ T₁ : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ T₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₀ T₀ : A ⥤ C} {R₀ : C ⥤ A}
    (a₀ : L₀ ⊣ R₀) (t₀ : T₀ ⊣ R₀)
    (a₁ : L₁ ⊣ R₁) (t₁ : T₁ ⊣ R₁)
    (a₂ : L₂ ⊣ R₂) (t₂ : T₂ ⊣ R₂)
    (c : T₀ ≅ T₁ ⋙ T₂) :
    conjugateIsoEquiv a₀ (a₁.comp a₂)
        ((a₀.leftAdjointUniq t₀ ≪≫ c ≪≫
          Functor.isoWhiskerLeft T₁ (a₂.leftAdjointUniq t₂).symm ≪≫
          Functor.isoWhiskerRight (a₁.leftAdjointUniq t₁).symm L₂).symm) =
      conjugateIsoEquiv t₀ (t₁.comp t₂) c.symm := by
  simp only [Iso.trans_symm, ← Functor.isoWhiskerLeft_symm,
    ← Functor.isoWhiskerRight_symm, Iso.symm_symm_eq]
  rw [conjugateIsoEquiv_trans a₀ t₀ (a₁.comp a₂),
    conjugateIsoEquiv_trans t₀ (t₁.comp t₂) (a₁.comp a₂),
    conjugateIsoEquiv_trans (t₁.comp t₂) (t₁.comp a₂) (a₁.comp a₂),
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight]
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv_iso_symm]

private theorem restriction_identity_mate (P : Profinite.{u}) :
    conjugateIsoEquiv (restrictionAdjunction (𝟙 P)) Adjunction.id
        (restrictionIdentity P).symm =
      Functor.sheafPushforwardContinuousId' (Over.pullbackId (X := P)) Ab.{u + 1}
        ((coherentTopology Profinite.{u}).over P) := by
  let J := (coherentTopology Profinite.{u}).over P
  have h := restriction_conjugate (A := Ab.{u + 1}) J J
    (Over.mapPullbackAdj (𝟙 P)) Adjunction.id (Over.mapId P).symm
  rw [restriction_identity_adjunction] at h
  have he : (restrictionIdentity P).symm =
      Functor.sheafPushforwardContinuousIso (Over.mapId P).symm Ab.{u + 1} J J := by
    ext G E
    simp [restrictionIdentity, Functor.sheafPushforwardContinuousId',
      Functor.sheafPushforwardContinuousId]
  change conjugateIsoEquiv
    ((Over.mapPullbackAdj (𝟙 P)).sheafPushforwardContinuous J J (E := Ab.{u + 1}))
    Adjunction.id _ = _
  rw [he]
  erw [h]
  rw [restriction_id_iso]
  rfl

private theorem restriction_composition_mate {P Q R : Profinite.{u}}
    (f : Q ⟶ P) (g : R ⟶ Q) :
    conjugateIsoEquiv (restrictionAdjunction (g ≫ f))
        ((restrictionAdjunction f).comp (restrictionAdjunction g))
        (restrictionComposition f g).symm =
      (Functor.sheafPushforwardContinuousComp' (Over.pullbackComp g f).symm
        Ab.{u + 1} ((coherentTopology Profinite.{u}).over P)
        ((coherentTopology Profinite.{u}).over Q)
        ((coherentTopology Profinite.{u}).over R)).symm := by
  let J := coherentTopology Profinite.{u}
  have hc := restriction_comp (A := Ab.{u + 1}) (J.over R) (J.over Q) (J.over P)
    (Over.mapPullbackAdj g) (Over.mapPullbackAdj f)
  have : (Over.map g ⋙ Over.map f).IsContinuous (J.over R) (J.over P) :=
    Functor.isContinuous_comp (Over.map g) (Over.map f) (J.over R) (J.over Q) (J.over P)
  have : (Over.pullback f ⋙ Over.pullback g).IsContinuous (J.over P) (J.over R) :=
    Functor.isContinuous_comp (Over.pullback f) (Over.pullback g)
      (J.over P) (J.over Q) (J.over R)
  have h := restriction_conjugate (A := Ab.{u + 1}) (J.over R) (J.over P)
    (Over.mapPullbackAdj (g ≫ f))
    ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f)) (Over.mapComp g f).symm
  change conjugateIsoEquiv _
    (((Over.mapPullbackAdj f).sheafPushforwardContinuous _ _ (E := Ab.{u + 1})).comp
      ((Over.mapPullbackAdj g).sheafPushforwardContinuous _ _ (E := Ab.{u + 1}))) _ = _
  rw [hc]
  unfold restrictionComposition
  rw [Iso.symm_symm_eq, restriction_comp_iso]
  erw [h]
  rw [restriction_comp_iso]
  apply Iso.ext
  ext G E
  simp [Functor.sheafPushforwardContinuousIso, Over.pullbackComp]

private theorem normalizedSliceIdentity_mate (P : Profinite.{u}) :
    conjugateIsoEquiv (sliceAdjunction (𝟙 P)) Adjunction.id
        (normalizedSliceIdentity P).symm =
      Functor.sheafPushforwardContinuousId' (Over.pullbackId (X := P)) Ab.{u + 1}
        ((coherentTopology Profinite.{u}).over P) := by
  unfold normalizedSliceIdentity restrictionComparison
  rw [normalized_identity_mate]
  exact restriction_identity_mate P

private theorem normalizedSliceComposition_mate {P Q R : Profinite.{u}} (f : Q ⟶ P) (g : R ⟶ Q) :
    conjugateIsoEquiv (sliceAdjunction (g ≫ f))
        ((sliceAdjunction f).comp (sliceAdjunction g))
        (normalizedSliceComposition f g).symm =
      (Functor.sheafPushforwardContinuousComp' (Over.pullbackComp g f).symm
        Ab.{u + 1} ((coherentTopology Profinite.{u}).over P)
        ((coherentTopology Profinite.{u}).over Q)
        ((coherentTopology Profinite.{u}).over R)).symm := by
  unfold normalizedSliceComposition restrictionComparison
  erw [normalized_composition_mate]
  exact restriction_composition_mate f g

private theorem normalizedSliceBeta_app {P Q : Profinite.{u}} (h : Q ⟶ P)
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (normalizedSliceBeta h).hom.app A = (restrictionComparison h).hom.app
      (((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P).obj A) := by
  have hc : (restrictionPointComparison h).hom.app A = 𝟙 _ := by
    ext E
    simp [restrictionPointComparison, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp]
    rfl
  change (restrictionComparison h).hom.app _ ≫ (restrictionPointComparison h).hom.app A = _
  rw [hc]
  change (restrictionComparison h).hom.app _ ≫ 𝟙 _ = _
  exact Category.comp_id _

private def makeSlice (Λ : Profinite.CondensedRing.{u}) {P Q : Profinite.{u}}
    (h : Q ⟶ P) : Slice Λ h := by
  let e := normalizedSliceBeta h
  have : NatTrans.IsMonoidal e.hom := normalizedSliceBetaMonoidal h
  let c := ((Functor.mapMonCompIso
    (F := (coherentTopology Profinite.{u}).overPullback Ab.{u + 1} P)
    (G := sliceInverse h)).symm ≪≫ Functor.mapMonNatIso e).app (Mon.mk Λ.X)
  refine {
    inverse := sliceInverse h
    inverse_eq := rfl
    adjunction := sliceAdjunction h
    adjunction_eq := HEq.rfl
    tensor_canonical := fun A B ↦ rfl
    unit_canonical := rfl
    beta := e
    beta_mate := ?_
    coefficient := c
    coefficient_eq := ?_ }
  · intro G S
    have hm := normalizedSliceBeta_mate h
    change conjugateIsoEquiv ((slicePointAdjunction P).comp (sliceAdjunction h))
      (slicePointAdjunction Q) e.symm = _ at hm
    erw [hm]
    simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp]
  · change 𝟙 _ ≫ e.hom.app Λ.X = e.hom.app Λ.X
    exact Category.id_comp _

private theorem makeSlice_coefficient (Λ : Profinite.CondensedRing.{u})
    {P Q : Profinite.{u}} (h : Q ⟶ P) :
    (makeSlice Λ h).coefficient.hom.hom = (restrictionComparison h).hom.app
      (CondensedRing.profiniteCoefficient Λ.X P) :=
  (makeSlice Λ h).coefficient_eq.trans (normalizedSliceBeta_app h Λ.X)

private theorem identity_coefficient (Λ : Profinite.CondensedRing.{u}) (P : Profinite.{u}) :
    (normalizedSliceIdentity P).hom.app (CondensedRing.profiniteCoefficient Λ.X P) =
      (makeSlice Λ (𝟙 P)).coefficient.hom.hom := by
  rw [makeSlice_coefficient]
  have hc : (restrictionIdentity P).hom.app
      (CondensedRing.profiniteCoefficient Λ.X P) = 𝟙 _ := by
    ext E
    simp [restrictionIdentity, Functor.sheafPushforwardContinuousId',
      Functor.sheafPushforwardContinuousId]
    rfl
  change (restrictionComparison (𝟙 P)).hom.app _ ≫ (restrictionIdentity P).hom.app _ = _
  rw [hc, Category.comp_id]

private def moduleIdentity (Λ : Profinite.CondensedRing.{u}) (P : Profinite.{u}) :
    (makeSlice Λ (𝟙 P)).modules Λ ≅ 𝟭 _ := by
  let e := normalizedSliceIdentity P
  let c := (makeSlice Λ (𝟙 P)).coefficient
  have he : NatTrans.IsMonoidal e.hom := normalizedSliceIdentityMonoidal P
  have hc : c.inv.hom ≫ e.hom.app (CondensedRing.profiniteCoefficient Λ.X P) = 𝟙 _ := by
    rw [identity_coefficient]
    exact congrArg Mon.Hom.hom c.inv_hom_id
  refine NatIso.ofComponents (fun M ↦ Mod.isoMk (e.app M.X) ?_)
    (fun f ↦ Mod.hom_ext _ _ (e.hom.naturality f.hom))
  have h := Functor.act_comp_app_of_isMonoidal_id e.hom c.inv.hom (𝟙 _) hc M
  simp only [Mod.act_comap_obj, id_whiskerRight, Category.id_comp] at h
  change Mod.act ((Mod.comap c.inv.hom).obj
      (((sliceInverse (𝟙 P)).mapMod (CondensedRing.profiniteCoefficient Λ.X P)).obj M)).X ≫
        e.hom.app M.X =
    CondensedRing.profiniteCoefficient Λ.X P ◁ e.hom.app M.X ≫ Mod.act M.X
  exact h

private theorem normalized_composition_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ T₁ : C ⥤ D} {L₂ T₂ : D ⥤ E} {L₀ T₀ : C ⥤ E}
    (e₀ : L₀ ≅ T₀) (e₁ : L₁ ≅ T₁) (e₂ : L₂ ≅ T₂)
    (c : T₀ ≅ T₁ ⋙ T₂) (A : C) :
    (e₀ ≪≫ c ≪≫ Functor.isoWhiskerLeft T₁ e₂.symm ≪≫
        Functor.isoWhiskerRight e₁.symm L₂).hom.app A ≫
        L₂.map (e₁.hom.app A) ≫ e₂.hom.app (T₁.obj A) =
      e₀.hom.app A ≫ c.hom.app A := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun k ↦ e₀.hom.app A ≫ k) (Category.comp_id (c.hom.app A))

private theorem composition_coefficient (Λ : Profinite.CondensedRing.{u})
    {P Q R : Profinite.{u}} (f : Q ⟶ P) (g : R ⟶ Q) :
    (normalizedSliceComposition f g).hom.app (CondensedRing.profiniteCoefficient Λ.X P) ≫
        (sliceInverse g).map (makeSlice Λ f).coefficient.hom.hom ≫
        (makeSlice Λ g).coefficient.hom.hom =
      (makeSlice Λ (g ≫ f)).coefficient.hom.hom := by
  rw [makeSlice_coefficient, makeSlice_coefficient, makeSlice_coefficient]
  have hc : (restrictionComposition f g).hom.app
      (CondensedRing.profiniteCoefficient Λ.X P) = 𝟙 _ := by
    ext E
    simp [restrictionComposition, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp, Over.mapComp]
    rfl
  calc
    _ = (restrictionComparison (g ≫ f)).hom.app
        (CondensedRing.profiniteCoefficient Λ.X P) ≫
        (restrictionComposition f g).hom.app (CondensedRing.profiniteCoefficient Λ.X P) :=
      normalized_composition_app (restrictionComparison (g ≫ f))
        (restrictionComparison f) (restrictionComparison g) (restrictionComposition f g) _
    _ = _ := by rw [hc, Category.comp_id]

private def moduleComposition (Λ : Profinite.CondensedRing.{u})
    {P Q R : Profinite.{u}} (f : Q ⟶ P) (g : R ⟶ Q) :
    (makeSlice Λ (g ≫ f)).modules Λ ≅
      (makeSlice Λ f).modules Λ ⋙ (makeSlice Λ g).modules Λ := by
  let e := normalizedSliceComposition f g
  let a := (makeSlice Λ f).coefficient
  let b := (makeSlice Λ g).coefficient
  let c := (makeSlice Λ (g ≫ f)).coefficient
  let G := sliceInverse g
  have he : NatTrans.IsMonoidal e.hom := normalizedSliceCompositionMonoidal f g
  have hei : NatTrans.IsMonoidal e.inv := by infer_instance
  have hi : b.inv.hom ≫ G.map a.inv.hom ≫
      e.inv.app (CondensedRing.profiniteCoefficient Λ.X P) = c.inv.hom := by
    rw [← cancel_mono c.hom.hom]
    have hc := composition_coefficient Λ f g
    change e.hom.app _ ≫ G.map a.hom.hom ≫ b.hom.hom = c.hom.hom at hc
    have ha : a.inv.hom ≫ a.hom.hom = 𝟙 _ := congrArg Mon.Hom.hom a.inv_hom_id
    have hb : b.inv.hom ≫ b.hom.hom = 𝟙 _ := congrArg Mon.Hom.hom b.inv_hom_id
    have hc' : c.inv.hom ≫ c.hom.hom = 𝟙 _ := congrArg Mon.Hom.hom c.inv_hom_id
    calc
      _ = b.inv.hom ≫ G.map a.inv.hom ≫
          (e.inv.app _ ≫ e.hom.app _) ≫ G.map a.hom.hom ≫ b.hom.hom := by
        rw [← hc]
        simp only [Category.assoc]
      _ = 𝟙 _ := by
        rw [e.inv_hom_id_app]
        change b.inv.hom ≫ G.map a.inv.hom ≫ G.map a.hom.hom ≫ b.hom.hom = 𝟙 _
        erw [← G.map_comp_assoc, ha, G.map_id, Category.id_comp, hb]
      _ = _ := hc'.symm
  let ei : (makeSlice Λ f).modules Λ ⋙ (makeSlice Λ g).modules Λ ≅
      (makeSlice Λ (g ≫ f)).modules Λ :=
    NatIso.ofComponents
      (fun M ↦ Mod.isoMk (e.symm.app M.X)
        (Functor.act_comp_app_of_isMonoidal e.inv a.inv.hom b.inv.hom c.inv.hom hi M))
      (fun k ↦ Mod.hom_ext _ _ (e.inv.naturality k.hom))
  exact ei.symm

private structure IdentityWitness (Λ : Profinite.CondensedRing.{u}) (P : Profinite.{u})
    (h : P ⟶ P) where
  tests : Over.pullback h ≅ 𝟭 (Over P)
  tests_projection : ∀ E, (tests.hom.app E).left = pullback.fst E.hom h
  abelian : (makeSlice Λ h).inverse ≅ 𝟭 _
  abelian_mate : ∀ (G : Sheaf ((coherentTopology Profinite.{u}).over P) Ab.{u + 1}) E,
    (((conjugateIsoEquiv (makeSlice Λ h).adjunction Adjunction.id abelian.symm).hom.app
      G).hom.app (op E)) = G.obj.map (tests.inv.app E).op
  ordinary : (makeSlice Λ h).modules Λ ≅ 𝟭 _
  ordinary_underlying : ∀ M, (ordinary.hom.app M).hom = abelian.hom.app M.X

private def identityWitness (Λ : Profinite.CondensedRing.{u}) (P : Profinite.{u}) :
    IdentityWitness Λ P (𝟙 P) := by
  refine {
    tests := Over.pullbackId
    tests_projection := ?_
    abelian := normalizedSliceIdentity P
    abelian_mate := ?_
    ordinary := moduleIdentity Λ P
    ordinary_underlying := fun M ↦ rfl }
  · intro E
    simp [Over.pullbackId, conjugateIsoEquiv, Over.mapPullbackAdj_counit_app]
  · intro G E
    have h := normalizedSliceIdentity_mate P
    change conjugateIsoEquiv (makeSlice Λ (𝟙 P)).adjunction Adjunction.id
      (normalizedSliceIdentity P).symm = _ at h
    erw [h]
    simp [Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousId]

private structure CompositionWitness (Λ : Profinite.CondensedRing.{u})
    {P Q R : Profinite.{u}} (f : Q ⟶ P) (g : R ⟶ Q) (h : R ⟶ P) where
  tests : Over.pullback h ≅ Over.pullback f ⋙ Over.pullback g
  tests_fst : ∀ E, (tests.hom.app E).left ≫
    pullback.fst ((Over.pullback f).obj E).hom g ≫ pullback.fst E.hom f =
      pullback.fst E.hom h
  tests_snd : ∀ E, (tests.hom.app E).left ≫
    pullback.snd ((Over.pullback f).obj E).hom g = pullback.snd E.hom h
  abelian : (makeSlice Λ h).inverse ≅ (makeSlice Λ f).inverse ⋙ (makeSlice Λ g).inverse
  abelian_mate : ∀ (G : Sheaf ((coherentTopology Profinite.{u}).over R) Ab.{u + 1}) E,
    (((conjugateIsoEquiv (makeSlice Λ h).adjunction
      ((makeSlice Λ f).adjunction.comp (makeSlice Λ g).adjunction) abelian.symm).hom.app
        G).hom.app (op E)) = G.obj.map (tests.inv.app E).op
  ordinary : (makeSlice Λ h).modules Λ ≅
    (makeSlice Λ f).modules Λ ⋙ (makeSlice Λ g).modules Λ
  ordinary_underlying : ∀ M, (ordinary.hom.app M).hom = abelian.hom.app M.X

private def compositionWitness (Λ : Profinite.CondensedRing.{u})
    {P Q R : Profinite.{u}} (f : Q ⟶ P) (g : R ⟶ Q) :
    CompositionWitness Λ f g (g ≫ f) := by
  refine {
    tests := Over.pullbackComp g f
    tests_fst := ?_
    tests_snd := fun E ↦ ((Over.pullbackComp g f).hom.app E).w
    abelian := normalizedSliceComposition f g
    abelian_mate := ?_
    ordinary := moduleComposition Λ f g
    ordinary_underlying := fun M ↦ rfl }
  · intro E
    have h := congrArg (fun k ↦ k.left)
      (conjugateEquiv_counit (Over.mapPullbackAdj (g ≫ f))
        ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f))
        (Over.mapComp g f).symm.hom E)
    simpa [Over.pullbackComp, conjugateIsoEquiv, Adjunction.comp_counit_app,
      Over.mapPullbackAdj_counit_app, Category.assoc] using h
  · intro G E
    have h := normalizedSliceComposition_mate f g
    change conjugateIsoEquiv (makeSlice Λ (g ≫ f)).adjunction
      ((makeSlice Λ f).adjunction.comp (makeSlice Λ g).adjunction)
      (normalizedSliceComposition f g).symm = _ at h
    erw [h]
    simp [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp]

private def makeIdentity (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X] :
    SliceIdentity Λ X (makeSlice Λ (affineComponentMap (𝟙 X))) := by
  have h : affineComponentMap (𝟙 X) = 𝟙 (affineComponentSpace X) := by
    ext q
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    rfl
  let w : IdentityWitness Λ (affineComponentSpace X) (affineComponentMap (𝟙 X)) :=
    h.symm ▸ identityWitness Λ (affineComponentSpace X)
  exact {
    tests := w.tests
    tests_projection := w.tests_projection
    abelian := w.abelian
    abelian_mate := w.abelian_mate
    ordinary := w.ordinary
    ordinary_underlying := w.ordinary_underlying }

private def makeComposition (Λ : Profinite.CondensedRing.{u})
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    SliceComposition Λ f g (makeSlice Λ (affineComponentMap f))
      (makeSlice Λ (affineComponentMap g)) (makeSlice Λ (affineComponentMap (g ≫ f))) := by
  have h : affineComponentMap (g ≫ f) = affineComponentMap g ≫ affineComponentMap f := by
    ext q
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe q
    rfl
  let w : CompositionWitness Λ (affineComponentMap f) (affineComponentMap g)
      (affineComponentMap (g ≫ f)) :=
    h.symm ▸ compositionWitness Λ (affineComponentMap f) (affineComponentMap g)
  exact {
    tests := w.tests
    tests_fst := w.tests_fst
    tests_snd := w.tests_snd
    abelian := w.abelian
    abelian_mate := w.abelian_mate
    ordinary := w.ordinary
    ordinary_underlying := w.ordinary_underlying }

private theorem cornerWitness (Λ : Profinite.CondensedRing.{u})
    (X : Scheme.{u}) [IsAffine X] : Nonempty (Corner Λ X) := by
  obtain ⟨e, he⟩ := component_absolute_tests X
  exact cornerOfTests Λ X e he

/-- Construct the normalized component and slice edges, with their slice comparisons.

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9
(blueprint: lem-zl-component-ordinary-edges).

Proof: use the actual inverse images adjoint to restriction along the relative
component tests and profinite base change. The component-site theorem and the
left-exact site inverse-image theorem give braided structures and finite exactness.
Their oplax maps are the adjunction mates of the pointwise tensor maps, giving the
two canonical equations in Corner and Slice. Identify absolute tests by the unique
map preserving the base and profinite coordinates. Restricting sheaves along this
identification and taking its adjunction mate defines beta. The right comparison
is pointwise monoidal, so beta is monoidal. Apply mapMon to beta at Λ to define
the coefficient isomorphism; its underlying map is beta at Λ by construction.
For slice identities use the first pullback projection, and for composition the
unique map to the iterated pullback preserving its two projections. Their
restriction isomorphisms have exactly the prescribed section formulas. Take their
mates to define the abelian comparisons. Coordinate compatibility at P × S gives
the coefficient equations. Hence the comparisons are linear on internal modules;
lift with Mod.isoMk and forgetful faithfulness. This constructs SliceIdentity and
SliceComposition including their underlying-map equalities. No scheme square or
coherence between scheme squares is asserted here. The construction also applies
to the empty component space and to the zero ring. -/
theorem component_ordinary_edges (Λ : Profinite.CondensedRing.{u}) :
    Nonempty (OrdinaryEdges Λ) := by
  classical
  exact ⟨{
    corner := fun X _ ↦ (cornerWitness Λ X).some
    slice := fun {_ _} _ _ f ↦ makeSlice Λ (affineComponentMap f)
    identity := makeIdentity Λ
    composition := fun {_ _ _} _ _ _ f g ↦ makeComposition Λ f g }⟩

set_option maxHeartbeats 2000000 in
-- Coefficient-sheaf unification unfolds site restrictions; the cancellation is abstract.
end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
