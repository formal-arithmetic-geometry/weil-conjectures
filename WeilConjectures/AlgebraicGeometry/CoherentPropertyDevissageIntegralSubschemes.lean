/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.CoherentPropertyIntegralIdealsOfSmallSupport
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk

/-!
# Devissage of a property of coherent modules

Stacks Project, Tag 01YM.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

private theorem ft_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (hF : F.IsFiniteType) : G.IsFiniteType := by
  have := hF
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let q' : G.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators j := (q.generators j).ofEpi
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X j)).map e.hom) }
  refine { exists_localGeneratorsData := ⟨q', ?_⟩ }
  constructor
  intro j
  have := hq.isFiniteType j
  exact inferInstanceAs ((q.generators j).ofEpi
    ((SheafOfModules.overFunctor X.ringCatSheaf (q.X j)).map e.hom)).IsFiniteType
private theorem coh_iso {X : Scheme.{u}} [IsLocallyNoetherian X] {F G : X.Modules}
    (e : F ≅ G) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    RingedSpace.IsCoherent X.toRingedSpace G := by
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mpr
    ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq, ft_iso e ht⟩
private theorem coh_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    {F : X.Modules} (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    RingedSpace.IsCoherent X.toRingedSpace (0 : X.Modules) := by
  have hk := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1 F F hF hF).1 (𝟙 F)
  exact coh_iso (isZero_kernel_of_mono (𝟙 F)).isoZero hk.1
private theorem p_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : X.Modules → Prop) (hz : P (0 : X.Modules))
    (he : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂)
    {F G : X.Modules} (e : F ≅ G) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : P G) : P F := by
  let S : ShortComplex X.Modules := ShortComplex.mk (0 : 0 ⟶ F) e.hom (by simp)
  have hs : S.ShortExact :=
    { exact := (S.exact_iff_mono rfl).mpr inferInstance }
  exact he S hs (coh_zero hF) hF (coh_iso e hF) hz hG

private theorem stalk_inj {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) [Mono f]
    (x : X) : Function.Injective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f).hom := by
  have hm := (RingedSpace.module_stalk_exact X.toRingedSpace f).1
    (fun U ↦ by
      apply (ModuleCat.mono_iff_injective _).mp
      exact Functor.map_mono (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)) f) x
  exact (ModuleCat.mono_iff_injective _).mp hm
private theorem support_mono {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) [Mono f] :
    {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} := by
  intro x hx hg
  have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G) := hg
  exact hx (Function.Injective.subsingleton (stalk_inj f x))
private theorem support_cokernel {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) :
    {x : X | ¬ Subsingleton ((cokernel f).presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} := by
  intro x hx hg
  have he := (RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.1 x
  have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G) := hg
  exact hx (Function.Surjective.subsingleton
    ((ModuleCat.epi_iff_surjective _).mp he.1))
private theorem support_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    {x : X | ¬ Subsingleton (F.presheaf.stalk x)} =
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} := by
  exact Set.Subset.antisymm (support_mono e.hom) (support_mono e.inv)
private theorem support_integral_ideal {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.IdealSheafData) (hI : I ≠ ⊥)
    (hF : RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules)) :
    {x : X | ¬ Subsingleton (((pushforward i).obj I.toModules).presheaf.stalk x)} =
      Set.range i.base := by
  let F := (pushforward i).obj I.toModules
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have := hq
  have := ht
  have hclosed := (finite_type_module_support_closed X F).2.2.2
  have hstalk := closedImmersion_pushforward_stalks i i.isClosedEmbedding I.toModules
  have hgeneric : i.base (genericPoint Z) ∈
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
    intro hzero
    have : Subsingleton (F.presheaf.stalk (i.base (genericPoint Z))) := hzero
    have hn := (integral_ideal_generic_stalk Z I).2.2.2.1.mp hI
    have : Nontrivial (I.toModules.presheaf.stalk (genericPoint Z)) := hn
    have : Subsingleton
        (((TopCat.Presheaf.pushforward Ab i.base).obj I.toModules.presheaf).stalk
          (i.base (genericPoint Z))) := hzero
    have hz : Subsingleton (I.toModules.presheaf.stalk (genericPoint Z)) :=
      (hstalk.2.1 (genericPoint Z)).1.surjective.subsingleton
    exact not_subsingleton (α := I.toModules.presheaf.stalk (genericPoint Z)) hz
  have hclosure : closure ({i.base (genericPoint Z)} : Set X) = Set.range i.base := by
    simpa only [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq]
      using ((genericPoint_spec Z).image i.continuous).def
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    exact hx (hstalk.1 x hnot)
  · rw [← hclosure]
    exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgeneric)

private theorem p_of_filtration {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : X.Modules → Prop) (hP_zero : P (0 : X.Modules))
    (hP_ext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c)
    (hbot : c 0 = ⊥) (htop : c (Fin.last m) = ⊤)
    (hcoh : ∀ j, RingedSpace.IsCoherent X.toRingedSpace (c j : X.Modules))
    (hpieces : ∀ j : Fin m,
      P (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
        (hc j.castSucc_le_succ)))) : P F := by
  have hpc : ∀ j : Fin (m + 1), P (c j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      exact p_iso P hP_zero hP_ext
        (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero) (hcoh _) hP_zero
    | succ j ih =>
      let f := Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hs : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
      have hq := (((isCoherent_kernel_cokernel_biprod_and_submodule X).1
        (c j.castSucc) (c j.succ) (hcoh _) (hcoh _)).1 f).2
      exact hP_ext S hs (hcoh _) (hcoh _) hq ih (hpieces j)
  exact p_iso P hP_zero hP_ext
    (Subobject.isoOfEq _ _ htop ≪≫ asIso (⊤ : Subobject F).arrow).symm hF (hpc _)


set_option linter.unusedVariables false in
/-- A property satisfying extension, summand, and integral-support devissage hypotheses
holds for every coherent module on a Noetherian scheme (Stacks, Tag 01YM). -/
theorem coherent_property_devissage_integral_subschemes
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : P (0 : X.Modules))
    (hP_ext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hP_sum : ∀ (F : X.Modules) (r : ℕ),
      RingedSpace.IsCoherent X.toRingedSpace F → 1 ≤ r →
      P (@biproduct (Fin r) X.Modules _ _ (fun _ : Fin r ↦ F)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ F))) → P F)
    (hP_integral : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z] (ξ : X)
      (hclosure : closure ({ξ} : Set X) = Set.range i.base),
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        ({x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base) ∧
        (∀ g : X.presheaf.stalk ξ, ∀ m : (RingedSpace.moduleStalkFunctor
          X.toRingedSpace ξ).obj G, g ∈ IsLocalRing.maximalIdeal _ → g • m = 0) ∧
        ∀ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
          [Mono ι] [J.IsQuasicoherent],
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom →
          ∃ G' : Subobject G,
            RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
            (∃ h : (G' : X.Modules) ⟶ idealModuleProduct ι G,
              G'.arrow = h ≫ idealModuleProductι ι G) ∧
            Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
              G'.arrow).hom ∧ P (G' : X.Modules)) :
    ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → P F := by
  classical
  have : IsNoetherian X := {}
  have hgood : ∀ T : TopologicalSpace.Closeds X,
      ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
        Set.range i.base ⊆ (T : Set X) →
          ∀ I : Z.IdealSheafData, P ((pushforward i).obj I.toModules) := by
    intro T
    induction T using WellFoundedLT.induction with
    | ind T ih =>
      intro Z i hi hZ hirange
      let ξ : X := i.base (genericPoint Z)
      have hclosure : closure ({ξ} : Set X) = Set.range i.base := by
        simpa only [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq]
          using ((genericPoint_spec Z).image i.continuous).def
      apply coherent_property_integral_ideals_of_small_support X P hP_zero hP_ext hP_sum
        Z i ξ hclosure
      · intro Q hQ hsupport hzero
        obtain ⟨m, c, hc, hbot, htop, hcoh, hquot⟩ :=
          exists_coherent_filtration_integral_subschemes X Q hQ
        apply p_of_filtration P hP_zero hP_ext Q hQ m c hc hbot htop hcoh
        intro k
        obtain ⟨Z', j, hj, hZ', I, hI, _, ⟨e⟩⟩ := hquot k
        have := hj
        have := hZ'
        let f := Subobject.ofLE (c k.castSucc) (c k.succ) (hc k.castSucc_le_succ)
        have hquotcoh := (((isCoherent_kernel_cokernel_biprod_and_submodule X).1
          (c k.castSucc) (c k.succ) (hcoh _) (hcoh _)).1 f).2
        have hpushcoh := coh_iso e hquotcoh
        have hrange := support_integral_ideal j I hI hpushcoh
        have hin : Set.range j.base ⊆
            {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} := by
          rw [← hrange, ← support_iso e]
          exact (support_cokernel f).trans (support_mono (c k.succ).arrow)
        have hstrict : Set.range j.base ⊂ Set.range i.base := by
          refine ⟨hin.trans hsupport, ?_⟩
          intro hreverse
          exact hin (hreverse ⟨genericPoint Z, rfl⟩) hzero
        let T' : TopologicalSpace.Closeds X :=
          ⟨Set.range j.base, j.isClosedEmbedding.isClosed_range⟩
        have hlt : T' < T := Set.ssubset_of_ssubset_of_subset hstrict hirange
        exact p_iso P hP_zero hP_ext e hquotcoh (ih T' hlt Z' j (by rfl) I)
      · exact hP_integral Z i ξ hclosure
  intro F hF
  obtain ⟨m, c, hc, hbot, htop, hcoh, hquot⟩ :=
    exists_coherent_filtration_integral_subschemes X F hF
  have hpieces (j : Fin m) :
      P (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))) := by
    obtain ⟨Z, i, hi, hZ, I, _, _, ⟨e⟩⟩ := hquot j
    have := hi
    have := hZ
    have hq := (((isCoherent_kernel_cokernel_biprod_and_submodule X).1
      (c j.castSucc) (c j.succ) (hcoh _) (hcoh _)).1
      (Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))).2
    exact p_iso P hP_zero hP_ext e hq (hgood ⊤ Z i (by simp) I)
  exact p_of_filtration P hP_zero hP_ext F hF m c hc hbot htop hcoh hpieces

end AlgebraicGeometry.Scheme.Modules
