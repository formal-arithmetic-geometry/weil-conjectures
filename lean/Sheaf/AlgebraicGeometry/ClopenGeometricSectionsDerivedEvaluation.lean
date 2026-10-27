/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import Sheaf.SixFunctors.WeaklyContractibleEtaleConstantModels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtaleFlat
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-!
# Unbounded evaluation on finitely many clopen geometric sections

Source: Stacks Project, Tags 070Y, 015F, 070H and 09T5; the finite-clopen calculation
in the geometric-fibre argument of blueprint main-20261015, prop-asd-smooth-base-change,
coherence (iii) (blueprint: lem-asd-clopen-geometric-sections-derived-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (A : Type (u + 1)) [CommRing A]

private theorem module_component_open {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) (i : I) :
    IsOpenImmersion (ι i) := by
  let e := (coproductIsCoproduct C).coconePointUniqueUpToIso hc
  have he : Sigma.ι C i ≫ e.hom = ι i := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  rw [← he]
  infer_instance

private theorem module_component_disjoint {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    (i j : I) (hij : i ≠ j) : Disjoint (Set.range (ι i).base) (Set.range (ι j).base) := by
  let e := (coproductIsCoproduct C).coconePointUniqueUpToIso hc
  have he (i : I) : Sigma.ι C i ≫ e.hom = ι i := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  rw [← he i, ← he j]
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have hxy : Sigma.ι C i x = Sigma.ι C j y := by
    apply e.hom.homeomorph.injective
    exact hx.trans hy.symm
  have h := (sigmaι_eq_iff C i j x y).mp hxy
  exact hij (Sigma.mk.inj_iff.mp h).1

private theorem module_components_cover {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    [∀ i, IsOpenImmersion (ι i)] :
    X.smallEtaleTopology.CoversTop (fun i ↦ Scheme.Etale.mk (ι i)) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal X.smallEtaleTopology
    (Scheme.Etale.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal (@Etale) X)]
  let f (i : I) : Scheme.Etale.mk (ι i) ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk (ι i) (by simp)
  apply X.smallEtaleTopology.superset_covering _
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr ?_)
  · rintro Y g ⟨i, b, e⟩
    rcases e with ⟨g', ⟨j⟩, hgj⟩
    exact ⟨j, ⟨b⟩⟩
  · apply Set.eq_univ_of_forall
    intro x
    let e := (coproductIsCoproduct C).coconePointUniqueUpToIso hc
    obtain ⟨y, hy⟩ := (sigmaOpenCover C).covers (e.inv x)
    refine Set.mem_iUnion.mpr ⟨(sigmaOpenCover C).idx (e.inv x), y, ?_⟩
    have he (i : I) : Sigma.ι C i ≫ e.hom = ι i :=
      IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
    change (Sigma.ι C _) y = e.inv x at hy
    change (ι _) y = x
    rw [← he, Scheme.Hom.comp_apply, hy]
    simp [← Scheme.Hom.comp_apply]

private theorem module_iso_of_component_iso {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    [∀ i, IsOpenImmersion (ι i)] {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (φ : F ⟶ G) (h : ∀ i, IsIso ((Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).map φ)) :
    IsIso φ := by
  apply Sheaf.isIso_of_coversTop (module_components_cover C ι hc)
  intro i
  have hQ : IsIso ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) (ι i)).map φ) := by
    let e := Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) (ι i)
      (inferInstance : Etale (ι i))
    have : IsIso ((Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).map φ) := h i
    rw [← isIso_comp_left_iff (e.hom.app F)]
    erw [← e.hom.naturality φ]
    infer_instance
  have happ : ∀ T, IsIso (((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} A)
      (Scheme.Etale.mk (ι i))).map φ).hom.app T) := by
    rintro ⟨T⟩
    let V : (C i).Etale := Scheme.Etale.mk T.hom.left
    let W : X.Etale :=
      (MorphismProperty.Over.map ⊤ (inferInstance : Etale (ι i))).obj V
    let e : W ≅ T.left := MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ T.left.hom = T.hom.left ≫ ι i
      simpa using (MorphismProperty.Over.w T.hom).symm)
    have : IsIso (φ.hom.app (op W)) :=
      inferInstanceAs (IsIso (((Etale.openImmersionRestriction
        (ModuleCat.{u + 1} A) (ι i)).map φ).hom.app (op V)))
    change IsIso (φ.hom.app (op T.left))
    rw [← isIso_comp_left_iff (F.obj.map e.inv.op), φ.hom.naturality]
    infer_instance
  have : IsIso (((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} A)
    (Scheme.Etale.mk (ι i))).map φ).hom) := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (X.smallEtaleTopology.over (Scheme.Etale.mk (ι i)))
      (ModuleCat.{u + 1} A)).map
      ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} A)
        (Scheme.Etale.mk (ι i))).map φ)) := this
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

private theorem module_clopen_reconstruction_unit {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    let R := Functor.pi' (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} A) (ι i))
    let S := Functor.pi (fun i ↦ Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)) ⋙
      Pi.functor I
    Nonempty (𝟭 _ ≅ R ⋙ S)  := by
  classical
  let (i : I) : IsOpenImmersion (ι i) := module_component_open C ι hc i
  let R := Functor.pi' (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} A) (ι i))
  let S := Functor.pi (fun i ↦ Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)) ⋙ Pi.functor I
  let η : 𝟭 _ ⟶ R ⋙ S :=
    { app := fun F ↦ Pi.lift (fun i ↦
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ι i)).unit.app F)
      naturality := by
        intro F G f
        apply Pi.hom_ext
        intro i
        dsimp [R, S]
        simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc]
        exact (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (ι i)).unit.naturality f }
  have hη (F) : IsIso (η.app F) := by
    apply module_iso_of_component_iso A C ι hc
    intro i
    let U := Etale.upperStar (ModuleCat.{u + 1} A) (ι i)
    let Gi := fun j ↦ (Etale.lowerStar (ModuleCat.{u + 1} A) (ι j)).obj ((R.obj F) j)
    have hz (j : I) (hji : j ≠ i) : IsZero (U.obj (Gi j)) := by
      exact IsZero.of_iso
        (Etale.isZero_openImmersionRestriction_lowerStar (ModuleCat.{u + 1} A)
          (ι j) (ι i) (module_component_disjoint C ι hc j i hji) ((R.obj F) j))
        ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
          (ι i) inferInstance).app (Gi j))
    have : IsIso (Pi.π (fun j ↦ U.obj (Gi j)) i) := Etale.singleProjectionIso _ i hz
    have : PreservesLimitsOfShape (Discrete I) U := by infer_instance
    have : IsIso (U.map (Pi.π Gi i)) := by
      rw [← piComparison_comp_π]
      infer_instance
    rw [← isIso_comp_right_iff _ (U.map (Pi.π Gi i)), ← U.map_comp]
    have he : η.app F ≫ Pi.π Gi i =
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ι i)).unit.app F := by
      exact Pi.lift_π _ _
    rw [he]
    infer_instance
  have : ∀ F, IsIso (η.app F) := hη
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact ⟨asIso η⟩


private theorem module_clopen_reconstruction_counit {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    let R := Functor.pi' (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} A) (ι i))
    let S := Functor.pi (fun i ↦ Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)) ⋙
      Pi.functor I
    Nonempty (S ⋙ R ≅ 𝟭 _) := by
  classical
  let S := Functor.pi (fun i ↦ Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)) ⋙ Pi.functor I
  let R := Functor.pi' (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} A) (ι i))
  let (i : I) : IsOpenImmersion (ι i) := module_component_open C ι hc i
  let ε : S ⋙ R ⟶ 𝟭 _ :=
    { app := fun G i ↦
        (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).map (Pi.π _ i) ≫
          (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ι i)).counit.app (G i)
      naturality := by
        intro G H f
        funext i
        dsimp [S, R]
        simp only [← Functor.map_comp_assoc]
        erw [Pi.map_π]
        simp only [Functor.map_comp, Category.assoc]
        exact congrArg (fun k ↦ _ ≫ k)
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
            (ι i)).counit.naturality (f i)) }
  have hε (G) (i : I) : IsIso (ε.app G i) := by
    let U := Etale.upperStar (ModuleCat.{u + 1} A) (ι i)
    let Gi := fun j ↦ (Etale.lowerStar (ModuleCat.{u + 1} A) (ι j)).obj (G j)
    have hz (j : I) (hji : j ≠ i) : IsZero (U.obj (Gi j)) := by
      exact IsZero.of_iso
        (Etale.isZero_openImmersionRestriction_lowerStar (ModuleCat.{u + 1} A)
          (ι j) (ι i) (module_component_disjoint C ι hc j i hji) (G j))
        ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
          (ι i) inferInstance).app (Gi j))
    have : IsIso (Pi.π (fun j ↦ U.obj (Gi j)) i) := Etale.singleProjectionIso _ i hz
    have : PreservesLimitsOfShape (Discrete I) U := by infer_instance
    have : IsIso (U.map (Pi.π Gi i)) := by
      rw [← piComparison_comp_π]
      infer_instance
    change IsIso (U.map (Pi.π Gi i) ≫
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ι i)).counit.app (G i))
    infer_instance
  have hεG (G) : IsIso (ε.app G) := by
    let (i : I) : IsIso (ε.app G i) := hε G i
    exact ⟨⟨(fun i ↦ inv (ε.app G i)), funext (fun i ↦ by simp),
      funext (fun i ↦ by simp)⟩⟩
  have : ∀ G, IsIso (ε.app G) := hεG
  have : IsIso ε := NatIso.isIso_of_isIso_app ε
  exact ⟨asIso ε⟩


private theorem module_clopen_equivalence {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    (Functor.pi' (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} A) (ι i))).IsEquivalence := by
  let R := Functor.pi' (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} A) (ι i))
  let S := Functor.pi (fun i ↦ Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)) ⋙ Pi.functor I
  obtain ⟨η⟩ := module_clopen_reconstruction_unit A C ι hc
  obtain ⟨ε⟩ := module_clopen_reconstruction_counit A C ι hc
  exact (CategoryTheory.Equivalence.mk R S η ε).isEquivalence_functor

private theorem module_component_closed {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) (i : I) :
    IsClosedImmersion (ι i) := by
  let := module_component_open C ι hc i
  apply IsClosedImmersion.of_isPreimmersion
  let e := (coproductIsCoproduct C).coconePointUniqueUpToIso hc
  have he : Sigma.ι C i ≫ e.hom = ι i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
  have hσ : IsClosed (Set.range (Sigma.ι C i)) := by
    simpa only [Function.comp_def, sigmaMk_mk] using
      ((sigmaMk C).isClosedEmbedding.comp
        (Topology.IsClosedEmbedding.sigmaMk (i := i))).isClosed_range
  have hh := e.hom.homeomorph.isClosedMap _ hσ
  rw [← Set.range_comp] at hh
  have heq : e.hom.homeomorph ∘ (Sigma.ι C i) = (ι i) := by
    funext x
    exact congrArg (fun f : C i ⟶ X ↦ f x) he
  rwa [heq] at hh

private theorem module_derived_disjoint_lowerStar_zero {U W V : Scheme.{u}}
    (j : U ⟶ V) (k : W ⟶ V) [IsOpenImmersion j] [IsClosedImmersion j]
    [IsOpenImmersion k] (h : Disjoint (Set.range j) (Set.range k))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsZero ((Etale.upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) := by
  let E := Etale.lowerStar (ModuleCat.{u + 1} A) j
  let F := Etale.upperStar (ModuleCat.{u + 1} A) k
  have hz : IsZero ((E ⋙ F).mapDerivedCategory.obj K) :=
    Functor.isZero_mapDerivedCategory_obj _ K (fun n ↦ IsZero.of_iso
      (Etale.isZero_openImmersionRestriction_lowerStar (ModuleCat.{u + 1} A) j k h _)
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) k inferInstance).app _))
  exact hz.of_iso ((Functor.mapDerivedCategoryCompIso E F).symm.app K)

private theorem module_derived_components_reflect_iso {I : Type u} [Finite I]
    {X : Scheme.{u}} (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hc : IsColimit (Cofan.mk X ι)) :
    JointlyReflectIsomorphisms
      (fun i ↦ (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory) := by
  let (i : I) : IsOpenImmersion (ι i) := module_component_open C ι hc i
  apply Functor.jointlyReflectIsomorphisms_mapDerivedCategory
  exact ⟨fun f _ ↦ module_iso_of_component_iso A C ι hc f (fun i ↦ inferInstance)⟩

private theorem module_derived_clopen_reconstruction_unit {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    [∀ i, IsOpenImmersion (ι i)] [∀ i, IsClosedImmersion (ι i)] :
    let R := Functor.pi' (fun i ↦ (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory)
    let S := Functor.pi (fun i ↦ (Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory) ⋙
      Pi.functor I
    Nonempty (𝟭 _ ≅ R ⋙ S)  := by
  classical
  let (i : I) : IsOpenImmersion (ι i) := module_component_open C ι hc i
  let (i : I) : IsClosedImmersion (ι i) := module_component_closed C ι hc i
  let R := Functor.pi' (fun i ↦ (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory)
  let S := Functor.pi (fun i ↦ (Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory) ⋙
    Pi.functor I
  let η : 𝟭 _ ⟶ R ⋙ S :=
    { app := fun F ↦ Pi.lift (fun i ↦
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (ι i)).mapDerivedCategoryAdjunction.unit.app F)
      naturality := by
        intro F G f
        apply Pi.hom_ext
        intro i
        dsimp [R, S]
        simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc]
        exact (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (ι i)).mapDerivedCategoryAdjunction.unit.naturality f }
  have hη (F) : IsIso (η.app F) := by
    apply (module_derived_components_reflect_iso A C ι hc).isIso_iff _ |>.mpr
    intro i
    let U := (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory
    let Gi :=
      fun j ↦ ((Etale.lowerStar (ModuleCat.{u + 1} A) (ι j)).mapDerivedCategory).obj ((R.obj F) j)
    have hz (j : I) (hji : j ≠ i) : IsZero (U.obj (Gi j)) := by
      exact module_derived_disjoint_lowerStar_zero A (ι j) (ι i)
        (module_component_disjoint C ι hc j i hji) _
    have : IsIso (Pi.π (fun j ↦ U.obj (Gi j)) i) := Etale.singleProjectionIso _ i hz
    have : PreservesLimitsOfShape (Discrete I) U := by infer_instance
    have : IsIso (U.map (Pi.π Gi i)) := by
      rw [← piComparison_comp_π]
      infer_instance
    rw [← isIso_comp_right_iff _ (U.map (Pi.π Gi i)), ← U.map_comp]
    have he : η.app F ≫ Pi.π Gi i =
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (ι i)).mapDerivedCategoryAdjunction.unit.app F := by
      exact Pi.lift_π _ _
    rw [he]
    let adj :=
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategoryAdjunction
    have : IsIso adj.counit := inferInstance
    change IsIso ((Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory.map
      (adj.unit.app F))
    rw [← isIso_comp_right_iff _ (adj.counit.app
      ((Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory.obj F)),
      ]
    exact (adj.left_triangle_components F).symm ▸ IsIso.id _
  have : ∀ F, IsIso (η.app F) := hη
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact ⟨asIso η⟩


private theorem module_derived_clopen_reconstruction_counit {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    [∀ i, IsOpenImmersion (ι i)] [∀ i, IsClosedImmersion (ι i)] :
    let R := Functor.pi' (fun i ↦ (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory)
    let S := Functor.pi (fun i ↦ (Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory) ⋙
      Pi.functor I
    Nonempty (S ⋙ R ≅ 𝟭 _) := by
  classical
  let S := Functor.pi (fun i ↦ (Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory) ⋙
    Pi.functor I
  let R := Functor.pi' (fun i ↦ (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory)
  let (i : I) : IsOpenImmersion (ι i) := module_component_open C ι hc i
  let (i : I) : IsClosedImmersion (ι i) := module_component_closed C ι hc i
  let ε : S ⋙ R ⟶ 𝟭 _ :=
    { app := fun G i ↦
        ((Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory).map (Pi.π _ i) ≫
          (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (ι i)).mapDerivedCategoryAdjunction.counit.app (G i)
      naturality := by
        intro G H f
        funext i
        dsimp [S, R]
        simp only [← Functor.map_comp_assoc]
        erw [Pi.map_π]
        simp only [Functor.map_comp, Category.assoc]
        exact congrArg (fun k ↦ _ ≫ k)
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
            (ι i)).mapDerivedCategoryAdjunction.counit.naturality (f i)) }
  have hε (G) (i : I) : IsIso (ε.app G i) := by
    let U := (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory
    let Gi := fun j ↦ ((Etale.lowerStar (ModuleCat.{u + 1} A) (ι j)).mapDerivedCategory).obj (G j)
    have hz (j : I) (hji : j ≠ i) : IsZero (U.obj (Gi j)) := by
      exact module_derived_disjoint_lowerStar_zero A (ι j) (ι i)
        (module_component_disjoint C ι hc j i hji) _
    have : IsIso (Pi.π (fun j ↦ U.obj (Gi j)) i) := Etale.singleProjectionIso _ i hz
    have : PreservesLimitsOfShape (Discrete I) U := by infer_instance
    have : IsIso (U.map (Pi.π Gi i)) := by
      rw [← piComparison_comp_π]
      infer_instance
    change IsIso (U.map (Pi.π Gi i) ≫
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (ι i)).mapDerivedCategoryAdjunction.counit.app (G i))
    infer_instance
  have hεG (G) : IsIso (ε.app G) := by
    let (i : I) : IsIso (ε.app G i) := hε G i
    exact ⟨⟨(fun i ↦ inv (ε.app G i)), funext (fun i ↦ by simp),
      funext (fun i ↦ by simp)⟩⟩
  have : ∀ G, IsIso (ε.app G) := hεG
  have : IsIso ε := NatIso.isIso_of_isIso_app ε
  exact ⟨asIso ε⟩


private theorem module_derived_clopen_equivalence {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    [∀ i, IsOpenImmersion (ι i)] [∀ i, IsClosedImmersion (ι i)] :
    (Functor.pi' (fun i ↦
      (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory)).IsEquivalence := by
  let R := Functor.pi' (fun i ↦ (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory)
  let S := Functor.pi (fun i ↦ (Etale.lowerStar (ModuleCat.{u + 1} A) (ι i)).mapDerivedCategory) ⋙
    Pi.functor I
  obtain ⟨η⟩ := module_derived_clopen_reconstruction_unit A C ι hc
  obtain ⟨ε⟩ := module_derived_clopen_reconstruction_counit A C ι hc
  exact (CategoryTheory.Equivalence.mk R S η ε).isEquivalence_functor

private theorem module_clopen_kinjective {I : Type u} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))
    (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    J.IsKInjective ↔ ∀ i, CochainComplex.IsKInjective
      (((Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapHomologicalComplex (.up ℤ)).obj J) := by
  classical
  let R := Functor.pi' (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} A) (ι i))
  have : R.IsEquivalence := module_clopen_equivalence A C ι hc
  let (i : I) : IsOpenImmersion (ι i) := module_component_open C ι hc i
  constructor
  · intro hJ i
    have := hJ
    have : (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).PreservesKInjectiveComplexes :=
      (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (ι i)).preservesKInjectiveComplexes
    infer_instance
  · intro h
    constructor
    intro K f hK
    have (i : I) := h i
    let H (i : I) := CochainComplex.IsKInjective.homotopyZero
      (((Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).mapHomologicalComplex (.up ℤ)).map f)
      (hK.map (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)))
    refine ⟨{ hom := fun p q ↦ R.preimage (fun i ↦ (H i).hom p q)
              zero := ?_
              comm := ?_ }⟩
    · intro p q hpq
      apply R.map_injective
      funext i
      change R.map (R.preimage (fun i ↦ (H i).hom p q)) i = _
      rw [R.map_preimage]
      change (H i).hom p q = (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).map 0
      simpa only [Functor.map_zero] using (H i).zero p q hpq
    · intro p
      apply R.map_injective
      change (fun i ↦ (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).map _) = _
      funext i
      have hi := (H i).comm p
      change (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).map (f.f p) =
        (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).map _
      have hpre {X Y} (g : ∀ i, (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).obj X ⟶
          (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).obj Y) :
          (Etale.upperStar (ModuleCat.{u + 1} A) (ι i)).map (R.preimage g) = g i :=
        congrFun (R.map_preimage g) i
      dsimp only [dNext, prevD,
        AddMonoidHom.mk'_apply] at hi ⊢
      simpa only [Functor.map_add, Functor.map_comp, Functor.map_zero,
        Functor.pi'_map, Functor.map_preimage, hpre, HomologicalComplex.zero_f,
        Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_d] using hi

private theorem module_clopen_extension_preservesKInjective {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] [IsClosedImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).PreservesKInjectiveComplexes := by
  have : IsIso (Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j) :=
    Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range (ModuleCat.{u + 1} A) j
      j.isClosedEmbedding.isClosed_range
  exact Functor.preservesKInjectiveComplexes_of_iso
    (asIso (Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j)).symm

private theorem module_disjoint_extension_zero {U W V : Scheme.{u}}
    (j : U ⟶ V) (k : W ⟶ V) [IsOpenImmersion j] [IsOpenImmersion k]
    (h : Disjoint (Set.range j) (Set.range k))
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsZero ((Etale.upperStar (ModuleCat.{u + 1} A) k).obj
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F)) := by
  exact IsInitial.isZero (IsInitial.ofIso
    (Etale.isInitial_openImmersionRestriction_openImmersionLowerShriek
      (ModuleCat.{u + 1} A) j k h F)
    ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) k inferInstance).app _).symm)

private theorem module_disjoint_extension_complex_zero {U W V : Scheme.{u}}
    (j : U ⟶ V) (k : W ⟶ V) [IsOpenImmersion j] [IsOpenImmersion k]
    (h : Disjoint (Set.range j) (Set.range k))
    (C : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    IsZero (((Etale.upperStar (ModuleCat.{u + 1} A) k).mapHomologicalComplex (.up ℤ)).obj
      (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj C)) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro n
  exact (module_disjoint_extension_zero A j k h (C.X n)).eq_of_src _ _

private theorem module_disjoint_extension_derived_zero {U W V : Scheme.{u}}
    (j : U ⟶ V) (k : W ⟶ V) [IsOpenImmersion j] [IsOpenImmersion k]
    (h : Disjoint (Set.range j) (Set.range k))
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsZero ((Etale.upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)) := by
  let E := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let F := Etale.upperStar (ModuleCat.{u + 1} A) k
  have hz : IsZero ((E ⋙ F).mapDerivedCategory.obj K) :=
    Functor.isZero_mapDerivedCategory_obj _ K (fun n ↦
      module_disjoint_extension_zero A j k h _)
  exact hz.of_iso ((Functor.mapDerivedCategoryCompIso E F).symm.app K)

private theorem module_clopen_complement_colimit {P V : Scheme.{u}}
    {I : Type u} [Finite I] (s : I → (P ⟶ V))
    [∀ i, IsOpenImmersion (s i)] [IsOpenImmersion (Sigma.desc s)]
    [IsClosedImmersion (Sigma.desc s)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (s i)) (Set.range (s k)))) :
    let Z := Scheme.openComplementOfIsClosedImmersion (Sigma.desc s)
    let C : Option I → Scheme.{u} := fun o ↦ o.elim Z (fun _ ↦ P)
    let ι : ∀ o, C o ⟶ V := fun o ↦ match o with
      | none => Z.ι
      | some i => s i
    Nonempty (IsColimit (Cofan.mk V ι)) := by
  refine ⟨?_⟩
  let Z := Scheme.openComplementOfIsClosedImmersion (Sigma.desc s)
  let C : Option I → Scheme.{u} := fun o ↦ o.elim Z (fun _ ↦ P)
  let ι : ∀ o, C o ⟶ V := fun o ↦ match o with
    | none => Z.ι
    | some i => s i
  have (o : Option I) : IsOpenImmersion (ι o) := by
    cases o <;> dsimp [ι] <;> infer_instance
  have hrange : Set.range (Sigma.desc s) = ⋃ i, Set.range (s i) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨i, z, rfl⟩ := (sigmaOpenCover (fun _ : I ↦ P)).exists_eq y
      exact Set.mem_iUnion.mpr ⟨i, z, by simp [← Scheme.Hom.comp_apply]⟩
    · intro hx
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨Sigma.ι (fun _ : I ↦ P) i z, by simp [← Scheme.Hom.comp_apply]⟩
  have hZ : Set.range Z.ι = (Set.range (Sigma.desc s))ᶜ := Z.range_ι
  have hcov : ⨆ o, (ι o).opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    change (⋃ o, Set.range (ι o)) = Set.univ
    rw [Set.iUnion_option]
    change Set.range Z.ι ∪ (⋃ i, Set.range (s i)) = Set.univ
    rw [hZ, ← hrange, Set.compl_union_self]
  have hdisj : Pairwise (fun o p ↦ Disjoint (ι o).opensRange (ι p).opensRange) := by
    intro o p hop
    apply TopologicalSpace.Opens.coe_disjoint.mp
    change Disjoint (Set.range (ι o)) (Set.range (ι p))
    cases o with
    | none =>
      cases p with
      | none => exact (hop rfl).elim
      | some i =>
        change Disjoint (Set.range Z.ι) (Set.range (s i))
        rw [hZ, hrange]
        exact disjoint_compl_left.mono_right (Set.subset_iUnion (fun i ↦ Set.range (s i)) i)
    | some i =>
      cases p with
      | none =>
        change Disjoint (Set.range (s i)) (Set.range Z.ι)
        rw [hZ, hrange]
        exact disjoint_compl_right.mono_left (Set.subset_iUnion (fun i ↦ Set.range (s i)) i)
      | some k => exact hdisjoint (fun h ↦ hop (congrArg some h))
  exact (nonempty_isColimit_cofanMk_of ι hcov hdisj).some

private theorem module_clopen_kinjective_complement {P V : Scheme.{u}}
    {I : Type u} [Finite I] (s : I → (P ⟶ V))
    [∀ i, IsOpenImmersion (s i)] [IsOpenImmersion (Sigma.desc s)]
    [IsClosedImmersion (Sigma.desc s)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (s i)) (Set.range (s k))))
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    J.IsKInjective ↔
      (∀ i, CochainComplex.IsKInjective
        (((Etale.upperStar (ModuleCat.{u + 1} A) (s i)).mapHomologicalComplex (.up ℤ)).obj J)) ∧
      CochainComplex.IsKInjective
        (((Etale.upperStar (ModuleCat.{u + 1} A)
          (Scheme.openComplementOfIsClosedImmersion (Sigma.desc s)).ι).mapHomologicalComplex
            (.up ℤ)).obj J) := by
  let Z := Scheme.openComplementOfIsClosedImmersion (Sigma.desc s)
  let C : Option I → Scheme.{u} := fun o ↦ o.elim Z (fun _ ↦ P)
  let ι : ∀ o, C o ⟶ V := fun o ↦ match o with
    | none => Z.ι
    | some i => s i
  have (o : Option I) : IsOpenImmersion (ι o) := by
    cases o <;> dsimp [ι] <;> infer_instance
  let hc : IsColimit (Cofan.mk V ι) := (module_clopen_complement_colimit s hdisjoint).some
  simpa only [Option.forall, ι, and_comm] using module_clopen_kinjective A C ι hc J

section AbstractSum

variable {C D : Type*} [Category C] [Category D] {I : Type*}

private theorem module_sum_colimit (B : C ⥤ D) (G : D ⥤ C) (adj : B ⊣ G)
    (T : I → C ⥤ D) [(Functor.pi' T).IsEquivalence]
    (e : ∀ i, G ⋙ T i ≅ 𝟭 D) (K : C) :
    Nonempty (IsColimit (Cofan.mk (B.obj K)
      (fun i ↦ (T i).map (adj.unit.app K) ≫ (e i).hom.app (B.obj K)))) := by
  classical
  refine ⟨?_⟩
  let R := Functor.pi' T
  have hb (N : D) : Function.Bijective
      (fun f : B.obj K ⟶ N ↦ fun i ↦
        ((T i).map (adj.unit.app K) ≫ (e i).hom.app (B.obj K)) ≫ f) := by
    let E₁ := adj.homEquiv K N
    let E₂ : (K ⟶ G.obj N) ≃ (∀ i, (T i).obj K ⟶ (T i).obj (G.obj N)) :=
      { toFun := fun f i ↦ (T i).map f
        invFun := fun f ↦ R.preimage f
        left_inv := fun f ↦ R.map_injective (R.map_preimage _)
        right_inv := fun f ↦ R.map_preimage f }
    let E₃ : (∀ i, (T i).obj K ⟶ (T i).obj (G.obj N)) ≃
        (∀ i, (T i).obj K ⟶ N) :=
      { toFun := fun f i ↦ f i ≫ (e i).hom.app N
        invFun := fun f i ↦ f i ≫ (e i).inv.app N
        left_inv := fun f ↦ by funext i; simp
        right_inv := fun f ↦ by funext i; simp }
    let E := E₁.trans (E₂.trans E₃)
    have hE : (fun f : B.obj K ⟶ N ↦ fun i ↦
        ((T i).map (adj.unit.app K) ≫ (e i).hom.app (B.obj K)) ≫ f) = E := by
      funext f i
      change _ = (T i).map (E₁ f) ≫ (e i).hom.app N
      dsimp only [E₁]
      rw [Adjunction.homEquiv_unit, Functor.map_comp]
      simp only [Category.assoc]
      exact congrArg (fun k ↦ (T i).map (adj.unit.app K) ≫ k)
        ((e i).hom.naturality f).symm
    exact hE ▸ E.bijective
  exact Cofan.IsColimit.mk _
    (fun c ↦ (hb c.pt).surjective c.inj |>.choose)
    (fun c i ↦ congrFun ((hb c.pt).surjective c.inj |>.choose_spec) i)
    (fun c m hm ↦ (hb c.pt).injective (by
      funext i
      exact (hm i).trans (congrFun ((hb c.pt).surjective c.inj |>.choose_spec) i).symm))


end AbstractSum

private theorem module_derived_clopen_complement {P V : Scheme.{u}}
    {I : Type u} [Finite I] (s : I → (P ⟶ V))
    [∀ i, IsOpenImmersion (s i)] [IsOpenImmersion (Sigma.desc s)]
    [IsClosedImmersion (Sigma.desc s)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (s i)) (Set.range (s k)))) :
    (Functor.pi' (C := fun o : Option I ↦ DerivedCategory
      (Sheaf (o.elim (Scheme.openComplementOfIsClosedImmersion (Sigma.desc s) : Scheme.{u})
        (fun _ ↦ P)).smallEtaleTopology (ModuleCat.{u + 1} A)))
      (fun o : Option I ↦ match o with
      | none => (Etale.upperStar (ModuleCat.{u + 1} A)
          (Scheme.openComplementOfIsClosedImmersion (Sigma.desc s)).ι).mapDerivedCategory
      | some i => (Etale.upperStar (ModuleCat.{u + 1} A)
          (s i)).mapDerivedCategory)).IsEquivalence := by
  let Z := Scheme.openComplementOfIsClosedImmersion (Sigma.desc s)
  let C : Option I → Scheme.{u} := fun o ↦ o.elim Z (fun _ ↦ P)
  let ι : ∀ o, C o ⟶ V := fun o ↦ match o with
    | none => Z.ι
    | some i => s i
  have (o : Option I) : IsOpenImmersion (ι o) := by
    cases o <;> dsimp [ι] <;> infer_instance
  let hc : IsColimit (Cofan.mk V ι) := (module_clopen_complement_colimit s hdisjoint).some
  let (o : Option I) : IsClosedImmersion (ι o) := module_component_closed C ι hc o
  convert module_derived_clopen_equivalence A C ι hc using 1
  congr 1
  funext o
  cases o <;> rfl


end AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The exact inverse-image comparison along a section, descended with the canonical
composition and identity comparisons. Source: Stacks, Tag 09T5
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenSectionPullbackIso (A : Type (u + 1)) [CommRing A]
    {P V : Scheme.{u}} (r : V ⟶ P) (s : P ⟶ V) (hs : s ≫ r = 𝟙 P) :
    D((r)^*[ModuleCat A]) ⋙ D((s)^*[ModuleCat A]) ≅
      𝟭 (DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat A))) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat A) s r (𝟙 P) hs.symm).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat A) P) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Restriction along a section of the total derived direct image: apply the section
comparison and restrict the canonical derived counit. Source: Stacks, Tags 070Y and 09T5
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenSectionDerivedRestriction (A : Type (u + 1)) [CommRing A]
    {P V : Scheme.{u}} (r : V ⟶ P) (s : P ⟶ V) (hs : s ≫ r = 𝟙 P) :
    R((r)_*[ModuleCat A]) ⟶ D((s)^*[ModuleCat A]) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (clopenSectionPullbackIso A r s hs).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).counit _ ≫
    (Functor.leftUnitor _).hom

private theorem clopenSectionDerivedRestriction_adj (A : Type (u + 1)) [CommRing A]
    {P V : Scheme.{u}} (r : V ⟶ P) (s : P ⟶ V) (hs : s ≫ r = 𝟙 P)
    {N : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))}
    {M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (f : (D((r)^*[ModuleCat.{u + 1} A])).obj N ⟶ M) :
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).homEquiv _ _ f ≫
        (clopenSectionDerivedRestriction A r s hs).app M =
      (clopenSectionPullbackIso A r s hs).inv.app N ≫
        (D((s)^*[ModuleCat.{u + 1} A])).map f := by
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r
  let e := clopenSectionPullbackIso A r s hs
  dsimp only [clopenSectionDerivedRestriction, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Category.comp_id]
  simp only [Category.id_comp]
  change adj.homEquiv _ _ f ≫ (e.inv.app _ ≫ _) = _
  rw [← Category.assoc]
  have hn := e.inv.naturality (adj.homEquiv _ _ f)
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [hn]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.assoc]
  erw [Category.comp_id]
  change e.inv.app N ≫
    ((D((s)^*[ModuleCat.{u + 1} A])).map ((D((r)^*[ModuleCat.{u + 1} A])).map
      (adj.homEquiv _ _ f)) ≫ (D((s)^*[ModuleCat.{u + 1} A])).map
      (adj.counit.app M)) = _
  rw [← Functor.map_comp]
  exact congrArg (fun k ↦ e.inv.app N ≫
    (D((s)^*[ModuleCat.{u + 1} A])).map k) ((adj.homEquiv N M).symm_apply_apply f)

/-- The canonical restriction to all section components, with values in their finite
product. Source: Stacks, Tags 070Y and 015F, finite-clopen calculation
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenGeometricEvaluation (A : Type (u + 1)) [CommRing A]
    {P V : Scheme.{u}} (r : V ⟶ P) {I : Type u} [Finite I]
    (s : I → (P ⟶ V)) (hs : ∀ i, s i ≫ r = 𝟙 P)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat A))) :
    (R((r)_*[ModuleCat A])).obj M ⟶ ∏ᶜ (fun i ↦ (D((s i)^*[ModuleCat A])).obj M) :=
  Pi.lift (fun i ↦ (clopenSectionDerivedRestriction A r (s i) (hs i)).app M)

/-- The union of pairwise disjoint clopen geometric sections is a clopen immersion, and
its structure map to the point is étale. Source: Stacks, finite-clopen geometric-fibre
calculation (blueprint: lem-asd-clopen-geometric-sections-derived-evaluation).
Proof: the coproduct injections identify the coproduct with the disjoint union of the
open images. Their finite union is closed. On each component the structure map is the
identity, so it is étale, also for the empty coproduct. -/
theorem clopenGeometricSections_union (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {V : Scheme.{u}} (r : V ⟶ Spec (.of Ω)) {I : Type u} [Finite I]
    (s : I → (Spec (.of Ω) ⟶ V)) [∀ i, IsOpenImmersion (s i)]
    (hclosed : ∀ i, IsClosed (Set.range (s i)))
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (s i)) (Set.range (s k))))
    (hs : ∀ i, s i ≫ r = 𝟙 _) :
    IsOpenImmersion (Sigma.desc s) ∧ IsClosedImmersion (Sigma.desc s) ∧
      Etale (Sigma.desc s ≫ r) := by
  have hj : IsOpenImmersion (Sigma.desc s) :=
    isOpenImmersion_sigmaDesc _ s hdisjoint
  refine ⟨hj, IsClosedImmersion.of_isPreimmersion _ ?_, ?_⟩
  · have hrange : Set.range (Sigma.desc s) = ⋃ i, Set.range (s i) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk (fun _ : I ↦ Spec (.of Ω))).surjective y
        exact Set.mem_iUnion.mpr ⟨i, z, by
          simp [sigmaMk_mk, ← Scheme.Hom.comp_apply]⟩
      · intro hx
        obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sigma.ι (fun _ : I ↦ Spec (.of Ω)) i z, by
          simp [← Scheme.Hom.comp_apply]⟩
    rw [hrange]
    exact isClosed_iUnion_of_finite hclosed
  · apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale)
      (sigmaOpenCover (fun _ : I ↦ Spec (.of Ω)))).mpr
    intro i
    change Etale (Sigma.ι (fun _ : I ↦ Spec (.of Ω)) i ≫ Sigma.desc s ≫ r)
    rw [← Category.assoc, Sigma.ι_desc, hs]
    infer_instance

/-- Degreewise étale sum extension on the ordinary unbounded derived categories.
The instances are supplied by its recorded exact left adjunction, without choosing
another extension functor. Source: Stacks, Tags 03S3 and 03S5
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenEtaleDerivedSum (A : Type (u + 1)) [CommRing A]
    {U P : Scheme.{u}} (v : U ⟶ P) (hv : Etale v) :
    DerivedCategory (Sheaf (U).smallEtaleTopology (ModuleCat A)) ⥤
      DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat A)) :=
  let F := etaleLowerShriek (ModuleCat A) v hv
  let adj := etaleLowerShriekUpperStarAdjunction (ModuleCat A) v hv
  letI : F.IsLeftAdjoint := adj.isLeftAdjoint
  letI : F.Additive := adj.left_adjoint_additive
  letI : F.PreservesHomology := {}
  F.mapDerivedCategory

/-- The canonical degreewise derived sum/restriction adjunction. Source: Stacks, Tags
03S5 and 015F (blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenEtaleDerivedSumAdjunction (A : Type (u + 1)) [CommRing A]
    {U P : Scheme.{u}} (v : U ⟶ P) (hv : Etale v) :
    clopenEtaleDerivedSum A v hv ⊣ D((v)^*[ModuleCat A]) :=
  let F := etaleLowerShriek (ModuleCat A) v hv
  let adj := etaleLowerShriekUpperStarAdjunction (ModuleCat A) v hv
  letI : F.IsLeftAdjoint := adj.isLeftAdjoint
  letI : F.Additive := adj.left_adjoint_additive
  letI : F.PreservesHomology := {}
  adj.mapDerivedCategoryAdjunction

/-- Identify restriction of `K` to a coproduct component with restriction of `Dj_! K`
to the same section of the ambient scheme, using the actual open-adjunction unit.
Source: Stacks, Tag 03S4 (blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenGeometricComponentIso (A : Type (u + 1)) [CommRing A]
    {P U V : Scheme.{u}} (t : P ⟶ U) (j : U ⟶ V) [IsOpenImmersion j]
    (s : P ⟶ V) (h : t ≫ j = s)
    (K : DerivedCategory (Sheaf (U).smallEtaleTopology (ModuleCat A))) :
    (D((t)^*[ModuleCat A])).obj K ≅
      (D((s)^*[ModuleCat A])).obj ((D((j)_!open[ModuleCat A])).obj K) :=
  (D((t)^*[ModuleCat A])).mapIso
      ((asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit).app K) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm.app _ ≪≫
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat A) t j s h.symm).symm).app _

/-- The canonical injection of a component into the étale sum, defined by restricting
the unit of sum extension and applying the section identity comparison.
Source: Stacks, Tags 03S5 and 09T5
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation). -/
noncomputable def clopenGeometricSumInjection (A : Type (u + 1)) [CommRing A]
    {P U V : Scheme.{u}} (t : P ⟶ U) (j : U ⟶ V) [IsOpenImmersion j]
    (s : P ⟶ V) (h : t ≫ j = s) (v : U ⟶ P) (hv : Etale v)
    (ht : t ≫ v = 𝟙 P)
    (K : DerivedCategory (Sheaf (U).smallEtaleTopology (ModuleCat A))) :
    (D((s)^*[ModuleCat A])).obj ((D((j)_!open[ModuleCat A])).obj K) ⟶
      (clopenEtaleDerivedSum A v hv).obj K :=
  (clopenGeometricComponentIso A t j s h K).inv ≫
    (D((t)^*[ModuleCat A])).map
      ((clopenEtaleDerivedSumAdjunction A v hv).unit.app K) ≫
    (clopenSectionPullbackIso A v t ht).hom.app _

section Evaluation

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (A : Type (u + 1)) [CommRing A]
  {V : Scheme.{u}} (r : V ⟶ Spec (.of Ω)) {I : Type u} [Finite I]
  (s : I → (Spec (.of Ω) ⟶ V)) [∀ i, IsOpenImmersion (s i)]
  (hclosed : ∀ i, IsClosed (Set.range (s i)))
  (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (s i)) (Set.range (s k))))
  (hs : ∀ i, s i ≫ r = 𝟙 _)

local notation "P" => Spec (CommRingCat.of Ω)
local notation "U" => ∐ (fun _ : I ↦ P)
local notation "j" => Sigma.desc s
local notation "v" => j ≫ r
local notation "t" => Sigma.ι (fun _ : I ↦ P)

/-- The derived finite-clopen calculation, its K-injective normalization, and the
specified finite-sum adjunct, including the empty family and unbounded complexes.
Source: Stacks, Tags 070H, 070I, 070K, 070Y, 015F, 03S3, 03S5 and 09T5; blueprint
main-20261015, prop-asd-smooth-base-change, coherence (iii)
(blueprint: lem-asd-clopen-geometric-sections-derived-evaluation).

Proof:
1. The sections and their open complement form a finite coproduct decomposition.
   Construct the module-sheaf restriction equivalence using component direct images;
   off-diagonal restrictions vanish. The same construction works on derived categories.
2. Restriction preserves K-injectivity by its exact left adjoint. Conversely, lift the
   component null homotopies through the fully faithful restriction equivalence.
   Resolve on U and extend through the clopen immersion, preserving K-injectivity
   and giving zero on the complement.
3. On objects with zero complementary restriction, the component equivalence and
   canonical derived adjunction identify Hom into the product with Hom into Rr_*.
   The counit and section comparisons identify this bijection with evaluation.
   Yoneda proves that evaluation is invertible, and its definition proves naturality.
4. The sum adjunction and component equivalence give the coproduct universal property
   for the injections specified by its actual unit. Colimit uniqueness gives e;
   naturality of the unit and comparisons gives its naturality.
5. Full faithfulness glues the prescribed projections and zero complement into delta.
   Its adjunct has the indicated projections by the counit formula. Product
   extensionality identifies it with e followed by the finite biproduct-to-product
   map. Both that map and evaluation are invertible, so the adjunct is invertible.
   These constructions also cover the empty family and unbounded complexes. -/
theorem clopenGeometricSections_derivedEvaluation :
    letI : IsOpenImmersion j := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).1
    letI : IsClosedImmersion j :=
      (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.1
    let hv := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.2
    let Z := Scheme.openComplementOfIsClosedImmersion j
    let E := D((j)_!open[ModuleCat A])
    let B := clopenEtaleDerivedSum A v hv
    let Ki := fun K i ↦ (D((s i)^*[ModuleCat A])).obj (E.obj K)
    (∀ J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat A)) ℤ,
      J.IsKInjective ↔
        (∀ i, CochainComplex.IsKInjective
          ((((s i)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J)) ∧
        CochainComplex.IsKInjective
          ((((Z.ι)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J)) ∧
    (∀ C : CochainComplex (Sheaf (U).smallEtaleTopology (ModuleCat A)) ℤ,
      ∃ (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat A)) ℤ)
        (q : (((j)_!open[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj C ⟶ J),
        QuasiIso q ∧ J.IsKInjective ∧
          IsZero ((((Z.ι)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J) ∧
          (∀ i, CochainComplex.IsKInjective
            ((((s i)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J))) ∧
    (∀ K, IsZero ((D((Z.ι)^*[ModuleCat A])).obj (E.obj K))) ∧
    (∀ K, IsIso (clopenGeometricEvaluation A r s hs (E.obj K))) ∧
    (∀ K L (f : K ⟶ L),
      (R((r)_*[ModuleCat A])).map (E.map f) ≫
          clopenGeometricEvaluation A r s hs (E.obj L) =
        clopenGeometricEvaluation A r s hs (E.obj K) ≫
          CategoryTheory.Limits.Pi.map (fun i ↦ (D((s i)^*[ModuleCat A])).map (E.map f))) ∧
    ((sheafSections (P).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (op (Scheme.Etale.mk (𝟙 P)))).IsEquivalence ∧
    ∃ (e : ∀ K, B.obj K ≅ ⨁ (Ki K))
      (δ : ∀ K, (D((r)^*[ModuleCat A])).obj (B.obj K) ⟶ E.obj K),
      (∀ K i, biproduct.ι (Ki K) i ≫ (e K).inv =
        clopenGeometricSumInjection A (t i) j (s i) (Sigma.ι_desc s i) v hv
          (by rw [← Category.assoc, Sigma.ι_desc]; exact hs i) K) ∧
      (∀ K L (f : K ⟶ L), B.map f ≫ (e L).hom =
        (e K).hom ≫ biproduct.map (fun i ↦ (D((s i)^*[ModuleCat A])).map (E.map f))) ∧
      (∀ K i, (D((s i)^*[ModuleCat A])).map (δ K) =
        (clopenSectionPullbackIso A r (s i) (hs i)).hom.app (B.obj K) ≫
          (e K).hom ≫ biproduct.π (Ki K) i) ∧
      (∀ K, (D((Z.ι)^*[ModuleCat A])).map (δ K) = 0) ∧
      (∀ K L (f : K ⟶ L),
        (D((r)^*[ModuleCat A])).map (B.map f) ≫ δ L = δ K ≫ E.map f) ∧
      (∀ K,
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).homEquiv _ _ (δ K) ≫
            clopenGeometricEvaluation A r s hs (E.obj K) =
          (e K).hom ≫ Pi.lift (fun i ↦ biproduct.π (Ki K) i)) ∧
      (∀ K, IsIso
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).homEquiv _ _ (δ K))) := by
  let : IsOpenImmersion j := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).1
  let : IsClosedImmersion j :=
    (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.1
  let Z := Scheme.openComplementOfIsClosedImmersion j
  have hZ : Disjoint (Set.range j) (Set.range Z.ι) := by
    rw [Z.range_ι]
    exact disjoint_compl_right
  have hki := module_clopen_kinjective_complement A s hdisjoint
  have heval : ∀ K, IsIso (clopenGeometricEvaluation A r s hs
      ((D((j)_!open[ModuleCat.{u + 1} A])).obj K)) := by
    intro K
    let T : ∀ o : Option I, DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
        DerivedCategory (Sheaf (o.elim (Z : Scheme.{u}) (fun _ ↦ P)).smallEtaleTopology
          (ModuleCat.{u + 1} A)) := fun o ↦ match o with
      | none => D((Z.ι)^*[ModuleCat.{u + 1} A])
      | some i => D((s i)^*[ModuleCat.{u + 1} A])
    let : (Functor.pi' T).IsEquivalence := module_derived_clopen_complement A s hdisjoint
    let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r
    let e := fun i ↦ clopenSectionPullbackIso A r (s i) (hs i)
    let M := (D((j)_!open[ModuleCat.{u + 1} A])).obj K
    have hM : IsZero ((T none).obj M) :=
      module_disjoint_extension_derived_zero A j Z.ι hZ K
    apply isIso_of_yoneda_map_bijective
    intro N
    let b : ((D((r)^*[ModuleCat.{u + 1} A])).obj N ⟶ M) →
        (∀ i, N ⟶ (T (some i)).obj M) :=
      fun f i ↦ (e i).inv.app N ≫ (T (some i)).map f
    have hb : Function.Bijective b := by
      constructor
      · intro f g hfg
        apply (Functor.pi' T).map_injective
        funext o
        cases o with
        | none => exact hM.eq_of_tgt _ _
        | some i =>
          apply (cancel_epi ((e i).inv.app N)).mp
          exact congrFun hfg i
      · intro f
        let g : (Functor.pi' T).obj ((D((r)^*[ModuleCat.{u + 1} A])).obj N) ⟶
            (Functor.pi' T).obj M := fun o ↦ match o with
          | none => 0
          | some i => (e i).hom.app N ≫ f i
        refine ⟨(Functor.pi' T).preimage g, ?_⟩
        funext i
        have hg := congrFun ((Functor.pi' T).map_preimage g) (some i)
        change (T (some i)).map ((Functor.pi' T).preimage g) = _ at hg
        dsimp [b]
        rw [hg]
        simp [g]
    let π : (N ⟶ ∏ᶜ (fun i ↦ (T (some i)).obj M)) ≃
        (∀ i, N ⟶ (T (some i)).obj M) :=
      { toFun := fun f i ↦ f ≫ Pi.π _ i
        invFun := Pi.lift
        left_inv := fun f ↦ by apply Pi.hom_ext; intro i; simp
        right_inv := fun f ↦ by funext i; simp }
    have hcomp : (fun f : N ⟶ (R((r)_*[ModuleCat.{u + 1} A])).obj M ↦
        π (f ≫ clopenGeometricEvaluation A r s hs M)) =
        b ∘ (adj.homEquiv N M).symm := by
      funext f i
      dsimp only [π, Equiv.coe_fn_mk, Function.comp_apply, b]
      change (f ≫ clopenGeometricEvaluation A r s hs M) ≫ Pi.π _ i = _
      simp only [clopenGeometricEvaluation, Category.assoc, Pi.lift_π]
      simpa only [adj, Equiv.apply_symm_apply] using
        clopenSectionDerivedRestriction_adj A r (s i) (hs i)
          ((adj.homEquiv N M).symm f)
    have hh : Function.Bijective (fun f ↦
        π (f ≫ clopenGeometricEvaluation A r s hs M)) := by
      rw [hcomp]
      exact hb.comp (adj.homEquiv N M).symm.bijective
    exact hh.of_comp_left π.injective
  refine ⟨hki, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C
    obtain ⟨J, hJ, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
    let E := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)
    have : (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).PreservesKInjectiveComplexes :=
      module_clopen_extension_preservesKInjective A j
    have hEJ : CochainComplex.IsKInjective (E.obj J) := inferInstance
    exact ⟨E.obj J, E.map q, inferInstance, hEJ,
      module_disjoint_extension_complex_zero A j Z.ι hZ J, (hki _).mp hEJ |>.1⟩
  · exact module_disjoint_extension_derived_zero A j Z.ι hZ
  · exact heval
  · intro K L f
    apply Pi.hom_ext
    intro i
    simp only [clopenGeometricEvaluation, Category.assoc, Pi.lift_π, Pi.map_π,
      Pi.lift_π_assoc]
    exact (clopenSectionDerivedRestriction A r (s i) (hs i)).naturality _
  · exact ((Scheme.geometricPoint_pullback_stalk Ω).2.2.2.1 A).1
  · classical
    let hv := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.2
    let E := D((j)_!open[ModuleCat.{u + 1} A])
    let B := clopenEtaleDerivedSum A v hv
    let Ki := fun K i ↦ (D((s i)^*[ModuleCat.{u + 1} A])).obj (E.obj K)
    let T := fun i ↦ D((t i)^*[ModuleCat.{u + 1} A])
    let (i : I) : IsClosedImmersion (t i) :=
      module_component_closed (fun _ : I ↦ P) t (coproductIsCoproduct _) i
    let : (Functor.pi' T).IsEquivalence :=
      module_derived_clopen_equivalence A (fun _ : I ↦ P) t (coproductIsCoproduct _)
    let ht : ∀ i, t i ≫ v = 𝟙 P := fun i ↦ by
      rw [← Category.assoc, Sigma.ι_desc]
      exact hs i
    let c := fun K i ↦ clopenGeometricComponentIso A (t i) j (s i)
      (Sigma.ι_desc s i) K
    let α := fun K i ↦ (T i).map ((clopenEtaleDerivedSumAdjunction A v hv).unit.app K) ≫
      (clopenSectionPullbackIso A v (t i) (ht i)).hom.app (B.obj K)
    let hc := fun K ↦ (module_sum_colimit B (D((v)^*[ModuleCat.{u + 1} A]))
      (clopenEtaleDerivedSumAdjunction A v hv) T
      (fun i ↦ clopenSectionPullbackIso A v (t i) (ht i)) K).some
    let β := fun K i ↦ (c K i).inv ≫ α K i
    let hd : ∀ K, IsColimit (Cofan.mk (B.obj K) (β K)) := fun K ↦
      Cofan.IsColimit.mk _
        (fun q ↦ (hc K).desc (Cofan.mk q.pt (fun i ↦ (c K i).hom ≫ q.inj i)))
        (fun q i ↦ by
          change ((c K i).inv ≫ α K i) ≫ _ = _
          rw [Category.assoc, show α K i ≫ (hc K).desc
            (Cofan.mk q.pt (fun k ↦ (c K k).hom ≫ q.inj k)) =
              (c K i).hom ≫ q.inj i from (hc K).fac _ ⟨i⟩]
          simp)
        (fun q m hm ↦ (hc K).hom_ext (by
          intro i
          obtain ⟨i⟩ := i
          change α K i ≫ m = _
          rw [(hc K).fac]
          change α K i ≫ m = (c K i).hom ≫ q.inj i
          rw [← hm i]
          simp [β]))
    let e : ∀ K, B.obj K ≅ ⨁ (Ki K) := fun K ↦
      (hd K).coconePointUniqueUpToIso (biproduct.isColimit (Ki K))
    have he (K) (i) : β K i ≫ (e K).hom = biproduct.ι (Ki K) i :=
      (hd K).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩
    have hei (K) (i) : biproduct.ι (Ki K) i ≫ (e K).inv = β K i :=
      (hd K).comp_coconePointUniqueUpToIso_inv (biproduct.isColimit (Ki K)) ⟨i⟩
    have hc_nat (K L) (f : K ⟶ L) (i) :
        (T i).map f ≫ (c L i).hom = (c K i).hom ≫
          (D((s i)^*[ModuleCat.{u + 1} A])).map (E.map f) := by
      let η := (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit
      let q := (Functor.mapDerivedCategoryCompIso
        (upperStar (ModuleCat.{u + 1} A) j) (upperStar (ModuleCat.{u + 1} A) (t i))).symm
      let p := Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) (t i) j (s i) (Sigma.ι_desc s i).symm).symm
      change (T i).map f ≫
          ((T i).map (η.app L) ≫ q.hom.app (E.obj L) ≫ p.hom.app (E.obj L)) =
        ((T i).map (η.app K) ≫ q.hom.app (E.obj K) ≫ p.hom.app (E.obj K)) ≫
          (D((s i)^*[ModuleCat.{u + 1} A])).map (E.map f)
      have hn := η.naturality f
      change f ≫ η.app L = η.app K ≫
        (D((j)^*[ModuleCat.{u + 1} A])).map (E.map f) at hn
      rw [← Category.assoc, ← Functor.map_comp, hn, Functor.map_comp]
      simp only [Category.assoc]
      have hq := q.hom.naturality (E.map f)
      change (T i).map ((D((j)^*[ModuleCat.{u + 1} A])).map (E.map f)) ≫
        q.hom.app (E.obj L) = q.hom.app (E.obj K) ≫ _ at hq
      rw [← Category.assoc ((T i).map ((D((j)^*[ModuleCat.{u + 1} A])).map (E.map f))), hq]
      simp only [Category.assoc]
      rw [p.hom.naturality]
    have ha_nat (K L) (f : K ⟶ L) (i) :
        (T i).map f ≫ α L i = α K i ≫ B.map f := by
      have hu := (clopenEtaleDerivedSumAdjunction A v hv).unit.naturality f
      change f ≫ (clopenEtaleDerivedSumAdjunction A v hv).unit.app L =
        (clopenEtaleDerivedSumAdjunction A v hv).unit.app K ≫
          (D((v)^*[ModuleCat.{u + 1} A])).map (B.map f) at hu
      have hn := (clopenSectionPullbackIso A v (t i) (ht i)).hom.naturality (B.map f)
      change (T i).map ((D((v)^*[ModuleCat.{u + 1} A])).map (B.map f)) ≫ _ =
        _ ≫ B.map f at hn
      dsimp only [α]
      rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, hn]
      simp only [Category.assoc]
    have he_nat (K L) (f : K ⟶ L) : B.map f ≫ (e L).hom =
        (e K).hom ≫ biproduct.map
          (fun i ↦ (D((s i)^*[ModuleCat.{u + 1} A])).map (E.map f)) := by
      apply (hd K).hom_ext
      rintro ⟨i⟩
      change β K i ≫ _ = β K i ≫ _
      have hβ : β K i ≫ B.map f =
          (D((s i)^*[ModuleCat.{u + 1} A])).map (E.map f) ≫ β L i := by
        apply (cancel_epi ((c K i).hom)).mp
        simp only [β, ← Category.assoc]
        rw [← hc_nat K L f i]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        exact (ha_nat K L f i).symm
      rw [← Category.assoc, hβ, Category.assoc, he,
        ← Category.assoc, he, biproduct.ι_map]
    let S : ∀ o : Option I, DerivedCategory
        (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
        DerivedCategory (Sheaf (o.elim (Z : Scheme.{u}) (fun _ ↦ P)).smallEtaleTopology
          (ModuleCat.{u + 1} A)) := fun o ↦ match o with
      | none => D((Z.ι)^*[ModuleCat.{u + 1} A])
      | some i => D((s i)^*[ModuleCat.{u + 1} A])
    let : (Functor.pi' S).IsEquivalence := module_derived_clopen_complement A s hdisjoint
    let δ := fun K ↦ (Functor.pi' S).preimage
      (show (Functor.pi' S).obj ((D((r)^*[ModuleCat.{u + 1} A])).obj (B.obj K)) ⟶
          (Functor.pi' S).obj (E.obj K) from
        fun o ↦ match o with
        | none => 0
        | some i => (clopenSectionPullbackIso A r (s i) (hs i)).hom.app (B.obj K) ≫
            (e K).hom ≫ biproduct.π (Ki K) i)
    have hδ (K) (i) : (D((s i)^*[ModuleCat.{u + 1} A])).map (δ K) =
        (clopenSectionPullbackIso A r (s i) (hs i)).hom.app (B.obj K) ≫
          (e K).hom ≫ biproduct.π (Ki K) i :=
      congrFun ((Functor.pi' S).map_preimage _) (some i)
    have hδZ (K) : (D((Z.ι)^*[ModuleCat.{u + 1} A])).map (δ K) = 0 :=
      congrFun ((Functor.pi' S).map_preimage _) none
    have hδ_nat (K L) (f : K ⟶ L) :
        (D((r)^*[ModuleCat.{u + 1} A])).map (B.map f) ≫ δ L = δ K ≫ E.map f := by
      apply (Functor.pi' S).map_injective
      funext o
      cases o with
      | none =>
        exact (module_disjoint_extension_derived_zero A j Z.ι hZ L).eq_of_tgt _ _
      | some i =>
        change (D((s i)^*[ModuleCat.{u + 1} A])).map _ =
          (D((s i)^*[ModuleCat.{u + 1} A])).map _
        rw [Functor.map_comp, Functor.map_comp, hδ, hδ]
        have hn := (clopenSectionPullbackIso A r (s i) (hs i)).hom.naturality (B.map f)
        change (D((s i)^*[ModuleCat.{u + 1} A])).map
          ((D((r)^*[ModuleCat.{u + 1} A])).map (B.map f)) ≫ _ = _ ≫ B.map f at hn
        rw [← Category.assoc, hn]
        simp only [Category.assoc]
        rw [← Category.assoc (B.map f) (e L).hom, he_nat]
        simp only [Category.assoc]
        exact congrArg (fun k ↦
          (clopenSectionPullbackIso A r (s i) (hs i)).hom.app (B.obj K) ≫
            (e K).hom ≫ k)
          (biproduct.map_π
            (fun i ↦ (D((s i)^*[ModuleCat.{u + 1} A])).map (E.map f)) i)
    have hadj (K) :
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).homEquiv _ _ (δ K) ≫
            clopenGeometricEvaluation A r s hs (E.obj K) =
          (e K).hom ≫ Pi.lift (fun i ↦ biproduct.π (Ki K) i) := by
      apply Pi.hom_ext
      intro i
      change (_ ≫ Pi.lift (fun i ↦
        (clopenSectionDerivedRestriction A r (s i) (hs i)).app (E.obj K))) ≫ Pi.π _ i =
          ((e K).hom ≫ Pi.lift (fun i ↦ biproduct.π (Ki K) i)) ≫ Pi.π _ i
      simp only [Category.assoc, Pi.lift_π]
      rw [clopenSectionDerivedRestriction_adj, hδ]
      simp only [Iso.inv_hom_id_app_assoc]
    refine ⟨e, δ, hei, he_nat, hδ, hδZ, hδ_nat, hadj, ?_⟩
    intro K
    have : IsIso (clopenGeometricEvaluation A r s hs (E.obj K)) := heval K
    have : IsIso ((mapDerivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} A) r).homEquiv _ _ (δ K) ≫
        clopenGeometricEvaluation A r s hs (E.obj K)) := by
      rw [hadj]
      rw [← biproduct.isoProduct_hom]
      change IsIso ((e K).hom ≫ (biproduct.isoProduct (Ki K)).hom)
      infer_instance
    exact IsIso.of_isIso_comp_right _ (clopenGeometricEvaluation A r s hs (E.obj K))

end Evaluation

end AlgebraicGeometry.Etale
