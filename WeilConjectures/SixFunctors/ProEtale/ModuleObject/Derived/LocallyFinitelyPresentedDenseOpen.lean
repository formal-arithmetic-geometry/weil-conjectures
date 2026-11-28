/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantRegularEnd
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.Topology.StratificationDense

/-!
# Lisse module objects: finite direct sums and dense opens

Let `Λ` be a commutative condensed ring and `X` a scheme. We show:

* a finite direct sum of pro-étale locally finitely presented ("lisse") module objects over
  `Λ_X` is lisse (`ProEtale.CondensedRing.isLocallyFinitelyPresented_biprod`,
  `ProEtale.CondensedRing.isLocallyFinitelyPresented_biproduct`): refine the covers trivialising
  the summands, finitely presented module objects being stable under direct sums;
* a constructible module object `M` is lisse on a dense open `U` of `X`
  (`ProEtale.CondensedRing.IsConstructibleModuleObject.exists_dense_isLocallyFinitelyPresented`):
  take for `U` the union of the interiors of the strata of a stratification adapted to `M`.
  The restriction of `M` to an open `W` contained in a stratum is lisse, since it becomes lisse
  after pullback along the surjective closed immersion `Xₐ ×_X W ⟶ W`
  (`ProEtale.CondensedRing.isLocallyFinitelyPresented_upperStar_ι_of_le_range`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-! ### Finite direct sums -/

/-- If the pullbacks `g^* M` and `g^* N` are finitely presented, so is `g^* (M ⊞ N)`. -/
lemma isFinitelyPresented_upperStar_biprod {W X : Scheme.{u}} (g : W ⟶ X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFinitelyPresented (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M))
    (hN : Mod.IsFinitelyPresented (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj N)) :
    Mod.IsFinitelyPresented (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj (M ⊞ N)) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (g)^*⟦Λ⟧
  exact (hM.biprod hN).of_iso ((g)^*⟦Λ⟧.mapBiprod M N).symm

/-- The direct sum of a finitely presented and a pro-étale locally finitely presented module
object is pro-étale locally finitely presented. -/
lemma isLocallyFinitelyPresented_biprod_of_isFinitelyPresented {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFinitelyPresented (condensedRingObj Λ X) M)
    (hN : IsLocallyFinitelyPresented (condensedRingObj Λ X) N) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) (M ⊞ N) := by
  obtain ⟨𝒱, h𝒱⟩ := (isLocallyFinitelyPresented_iff N).1 hN
  exact (isLocallyFinitelyPresented_iff _).2 ⟨𝒱, fun j ↦
    isFinitelyPresented_upperStar_biprod _ (IsFinitelyPresented.upperStar Λ _ hM) (h𝒱 j)⟩

/-- The direct sum of two pro-étale locally finitely presented module objects is pro-étale
locally finitely presented. -/
lemma isLocallyFinitelyPresented_biprod {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ X) M)
    (hN : IsLocallyFinitelyPresented (condensedRingObj Λ X) N) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) (M ⊞ N) := by
  obtain ⟨𝒰, h𝒰⟩ := (isLocallyFinitelyPresented_iff M).1 hM
  refine isLocallyFinitelyPresented_of_cover 𝒰 fun i ↦ ?_
  have := preservesBinaryBiproducts_of_preservesBiproducts (𝒰.f i)^*⟦Λ⟧
  exact (isLocallyFinitelyPresented_biprod_of_isFinitelyPresented (h𝒰 i)
    (IsLocallyFinitelyPresented.upperStar Λ (𝒰.f i) hN)).of_iso
      ((𝒰.f i)^*⟦Λ⟧.mapBiprod M N).symm

/-- A zero module object is pro-étale locally finitely presented. -/
lemma isLocallyFinitelyPresented_of_isZero {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsZero M) : IsLocallyFinitelyPresented (condensedRingObj Λ X) M :=
  (isLocallyFinitelyPresented_iff M).2 ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _),
    fun _ ↦ IsFinitelyPresented.upperStar Λ _ (Mod.IsFinitelyPresented.of_isZero hM)⟩

/-- Pro-étale local finite presentation, as a property of module objects over `Λ_X`, is closed
under binary products. -/
lemma isClosedUnderBinaryProducts_isLocallyFinitelyPresented (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderBinaryProducts
      (IsLocallyFinitelyPresented (A := Ab.{u + 1}) (condensedRingObj Λ X)) where
  limitsOfShape_le := by
    rintro M ⟨h⟩
    refine (isLocallyFinitelyPresented_biprod (h.prop_diag_obj ⟨.left⟩)
      (h.prop_diag_obj ⟨.right⟩)).of_iso ?_
    exact biprod.isoProd _ _ ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair h.diag)).symm ≪≫
      (h.isLimit.conePointUniqueUpToIso (limit.isLimit _)).symm

/-- A finite direct sum of pro-étale locally finitely presented module objects is pro-étale
locally finitely presented. -/
theorem isLocallyFinitelyPresented_biproduct {X : Scheme.{u}} {J : Type*} [Finite J]
    (M : J → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ j, IsLocallyFinitelyPresented (condensedRingObj Λ X) (M j)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) (⨁ M) := by
  let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)) := IsLocallyFinitelyPresented (condensedRingObj Λ X)
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.of_iso e⟩
  have : P.ContainsZero :=
    ⟨⟨0, isZero_zero _, isLocallyFinitelyPresented_of_isZero (isZero_zero _)⟩⟩
  have := isClosedUnderBinaryProducts_isLocallyFinitelyPresented (Λ := Λ) X
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_of_isLimit_fan (biproduct.isLimit M) hM

/-! ### Constructible module objects are lisse on a dense open -/

/-- Let `f : Z ⟶ X` be an immersion such that `f^* M` is pro-étale locally finitely presented.
Then the restriction of `M` to any open `W` contained in the range of `f` is pro-étale locally
finitely presented: it becomes so after pullback along the surjective closed immersion
`Z ×_X W ⟶ W`. -/
theorem isLocallyFinitelyPresented_upperStar_ι_of_le_range {X Z : Scheme.{u}} (f : Z ⟶ X)
    [IsImmersion f] {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ Z) ((f)^*⟦Λ⟧.obj M)) (W : X.Opens)
    (hW : (W : Set X) ⊆ Set.range f) :
    IsLocallyFinitelyPresented (condensedRingObj Λ W) ((W.ι)^*⟦Λ⟧.obj M) := by
  have hp : Function.Surjective (pullback.snd f W.ι) := by
    intro w
    have hw : W.ι w ∈ (W : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hW hw
    obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback z w hz
    exact ⟨t, ht⟩
  have : IsClosedImmersion (pullback.snd f W.ι) := .of_isPreimmersion _ (by
    rw [Set.range_eq_univ.2 hp]
    exact isClosed_univ)
  exact localFinitePresentation_of_surjective_closed_pullback _ hp _ _
    ((isLocallyFinitelyPresented_mapMod_iff Λ (pullback.snd f W.ι) _).2
      (isLocallyFinitelyPresented_upperStar_upperStar_of_comm Λ
        (pullback.condition (f := f) (g := W.ι)) hM))

/-- If the restriction of `M` to an open `U` is pro-étale locally finitely presented, so is its
restriction to any smaller open `V ≤ U`. -/
lemma isLocallyFinitelyPresented_upperStar_ι_of_le {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    {U V : X.Opens} (hVU : V ≤ U)
    (hU : IsLocallyFinitelyPresented (condensedRingObj Λ U) ((U.ι)^*⟦Λ⟧.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ V) ((V.ι)^*⟦Λ⟧.obj M) :=
  (IsLocallyFinitelyPresented.upperStar Λ (X.homOfLE hVU) hU).of_iso
    (((upperStarComp Λ _ _).app M).symm ≪≫ (upperStarCongr Λ (X.homOfLE_ι hVU)).app M)

/-- Let `U` be an open of `X` covered by opens `W i ≤ U` such that each restriction of `M` to
`W i` is pro-étale locally finitely presented. Then so is the restriction of `M` to `U`: the
`W i` form a Zariski, hence pro-étale, cover of `U`. -/
theorem isLocallyFinitelyPresented_upperStar_ι_of_forall_mem {X : Scheme.{u}} {ι : Type u}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (U : X.Opens) (W : ι → X.Opens) (hWU : ∀ i, W i ≤ U) (hU : ∀ x ∈ U, ∃ i, x ∈ W i)
    (hW : ∀ i, IsLocallyFinitelyPresented (condensedRingObj Λ (W i)) (((W i).ι)^*⟦Λ⟧.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ U) ((U.ι)^*⟦Λ⟧.obj M) := by
  let 𝒰 := (Cover.mkOfCovers ι (fun i ↦ (W i).toScheme) (fun i ↦ X.homOfLE (hWU i))
    (P := @IsOpenImmersion) fun x ↦
      have ⟨i, hi⟩ := hU x.1 x.2
      ⟨i, ⟨x.1, hi⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩).weaken
        zariskiPrecoverage_le_proetalePrecoverage
  refine isLocallyFinitelyPresented_of_cover 𝒰 fun i ↦ ?_
  -- We factor `𝒰.f i ≫ U.ι` through `(W i).ι` rather than identify `𝒰.f i` with the inclusion
  -- `W i ⟶ U`: the kernel struggles with the latter identification.
  have hr : Set.range (𝒰.f i ≫ U.ι) ⊆ Set.range (W i).ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    have e : ((𝒰.f i) z).1 = z.1 := Scheme.homOfLE_apply (hWU i) z
    rw [Scheme.Opens.ι_apply, e]
    exact z.2
  exact isLocallyFinitelyPresented_upperStar_upperStar_of_comm Λ
    (IsOpenImmersion.lift_fac (W i).ι _ hr) (hW i)

/-- Let `(W i)` be a family of opens of `X` such that each restriction of `M` to `W i` is
pro-étale locally finitely presented. Then so is the restriction of `M` to `⨆ i, W i`. -/
theorem isLocallyFinitelyPresented_upperStar_ι_iSup {X : Scheme.{u}} {ι : Type u}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (W : ι → X.Opens)
    (hW : ∀ i, IsLocallyFinitelyPresented (condensedRingObj Λ (W i)) (((W i).ι)^*⟦Λ⟧.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ (⨆ i, W i : X.Opens))
      (((⨆ i, W i : X.Opens).ι)^*⟦Λ⟧.obj M) :=
  isLocallyFinitelyPresented_upperStar_ι_of_forall_mem _ W (le_iSup W)
    (fun _ hx ↦ TopologicalSpace.Opens.mem_iSup.1 hx) hW

/-- **A constructible module object is lisse on a dense open**: if `M` is constructible along a
stratification `X = ∐ₐ Xₐ`, its restriction to the dense open `U = ⋃ₐ int(Xₐ)` is pro-étale
locally finitely presented. -/
theorem IsConstructibleModuleObject.exists_dense_isLocallyFinitelyPresented {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsLocallyFinitelyPresented (condensedRingObj Λ U) ((U.ι)^*⟦Λ⟧.obj M) := by
  obtain ⟨S, hS⟩ := hM
  let W : ULift.{u} (Fin S.n) → X.Opens := fun i ↦ ⟨interior (S.stratum i.down), isOpen_interior⟩
  refine ⟨⨆ i, W i, ?_, isLocallyFinitelyPresented_upperStar_ι_iSup W fun i ↦ ?_⟩
  · rw [TopologicalSpace.Opens.coe_iSup]
    exact S.dense_iUnion_interior_stratum.mono
      (Set.iUnion_subset fun i ↦ Set.subset_iUnion_of_subset (ULift.up i) subset_rfl)
  · refine isLocallyFinitelyPresented_upperStar_ι_of_le_range (S.immersion i.down)
      ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS i.down)) (W i) ?_
    rw [S.range_immersion]
    exact interior_subset

end AlgebraicGeometry.ProEtale.CondensedRing
