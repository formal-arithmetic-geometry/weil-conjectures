/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Extensions of complexes with flat terms and K-flat outer objects

Source: Stacks Project, More on Algebra, Lemma `lemma-K-flat-two-out-of-three-ses`
(blueprint: lem-kun-flat-kflat-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R]

local instance : HasColimitsOfSize.{0, 0} (ModuleCat.{u} R) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

local instance : HasLimitsOfSize.{0, 0} (ModuleCat.{u} R) :=
  hasLimitsOfSizeShrink.{0, 0, u, u} _

private theorem module_tensor_shortExact
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₃ : ObjectProperty.flat S.X₃) (M : ModuleCat.{u} R) :
    (S.map (tensorLeft M)).ShortExact := by
  have := hS.epi_g
  have := (ModuleCat.flat_iff_flat S.X₃).mp h₃
  refine ShortComplex.ShortExact.mk'
    (hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance) ?_ ?_
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hS.moduleCat_surjective_g
      S.f.hom hS.moduleCat_injective_f
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) M
  · change Epi (M ◁ S.g)
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.lTensor_surjective M hS.moduleCat_surjective_g

private theorem module_flat_extension
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : ObjectProperty.flat S.X₁) (h₃ : ObjectProperty.flat S.X₃) :
    ObjectProperty.flat S.X₂ := by
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesFiniteLimits (tensorRight S.X₁) := h₁.2.1
  have : PreservesFiniteLimits (tensorRight S.X₃) := h₃.2.1
  have : (tensorRight S.X₂).PreservesMonomorphisms := ⟨fun {N N'} f hf ↦ by
    let T := S.map (tensorLeft N)
    let T' := S.map (tensorLeft N')
    have hT := module_tensor_shortExact S hS h₃ N
    have hT' := module_tensor_shortExact S hS h₃ N'
    let φ : T ⟶ T' :=
      { τ₁ := f ▷ S.X₁
        τ₂ := f ▷ S.X₂
        τ₃ := f ▷ S.X₃
        comm₁₂ := by exact (whisker_exchange f S.f).symm
        comm₂₃ := by exact (whisker_exchange f S.g).symm }
    have := hT.mono_f
    have := hT'.mono_f
    have : Mono φ.τ₁ := (tensorRight S.X₁).map_mono f
    have : Mono φ.τ₃ := (tensorRight S.X₃).map_mono f
    exact ShortComplex.mono_τ₂_of_exact_of_mono φ hT.exact⟩
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels (tensorRight S.X₂)
  have : PreservesFiniteLimits (tensorRight S.X₂) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight S.X₂).symm

private theorem tensor_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (h₃ : ∀ n : ℤ, ObjectProperty.flat (S.X₃.X n))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (S.map (tensorLeft K)).ShortExact := by
  have hL : PreservesColimitsOfShape WalkingParallelPair (tensorLeft K) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair
      ((Functor.map₂CochainComplex (curriedTensor (ModuleCat.{u} R))).obj K))
  have : HasFiniteLimits (CochainComplex (ModuleCat.{u} R) ℤ) := by infer_instance
  have : HasFiniteProducts (CochainComplex (ModuleCat.{u} R) ℤ) :=
    hasFiniteProducts_of_hasFiniteLimits _
  have : HasKernels (CochainComplex (ModuleCat.{u} R) ℤ) := by infer_instance
  have : (tensorLeft K).PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels
      (C := CochainComplex (ModuleCat.{u} R) ℤ)
      (D := CochainComplex (ModuleCat.{u} R) ℤ) (tensorLeft K)
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk'
    (hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance) ?_ ?_
  · apply HomologicalComplex.mono_of_mono_f
    intro n
    let I := {p : ℤ × ℤ // p.1 + p.2 = n}
    let A : I → ModuleCat.{u} R := fun p ↦ K.X p.val.1 ⊗ S.X₁.X p.val.2
    let B : I → ModuleCat.{u} R := fun p ↦ K.X p.val.1 ⊗ S.X₂.X p.val.2
    let t : Discrete.functor A ⟶ Discrete.functor B :=
      Discrete.natTrans (fun p ↦ K.X p.as.val.1 ◁ S.f.f p.as.val.2)
    have ht (p : Discrete I) : Mono (t.app p) :=
      (module_tensor_shortExact
        (S.map (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) p.as.val.2))
        (hS.map_of_exact _) (h₃ p.as.val.2) (K.X p.as.val.1)).mono_f
    have : Mono t := NatTrans.mono_of_mono_app t
    apply colim.map_mono' t (colimit.isColimit _) (colimit.isColimit _)
    intro j
    change HomologicalComplex.ιTensorObj K S.X₁ j.as.val.1 j.as.val.2 n
        j.as.property ≫ (K ◁ S.f).f n = _
    change HomologicalComplex.ιMapBifunctor K S.X₁ (curriedTensor (ModuleCat.{u} R))
        (.up ℤ) j.as.val.1 j.as.val.2 n j.as.property ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 K) S.f (curriedTensor (ModuleCat.{u} R))
        (.up ℤ)).f n = _
    rw [HomologicalComplex.ι_mapBifunctorMap]
    rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
    rfl
  · change Epi ((tensorLeft K).map S.g)
    infer_instance

private theorem kFlat_extension
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (h₃ : ∀ n : ℤ, ObjectProperty.flat (S.X₃.X n))
    (hk₁ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat S.X₁)
    (hk₃ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat S.X₃) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat S.X₂ := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨K, rfl⟩ := Z.quotient_obj_surjective
  have hp₁ := (HomotopyCategory.kFlat_iff_preserves_acyclic _).mp
    ((HomotopyCategory.kFlat_quotient_obj_iff _).mpr hk₁) _ hZ
  have hp₃ := (HomotopyCategory.kFlat_iff_preserves_acyclic _).mp
    ((HomotopyCategory.kFlat_quotient_obj_iff _).mpr hk₃) _ hZ
  change HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj (S.X₁ ⊗ K)) ∧
    HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj (K ⊗ S.X₁)) at hp₁
  change HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj (S.X₃ ⊗ K)) ∧
    HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj (K ⊗ S.X₃)) at hp₃
  change HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj (S.X₂ ⊗ K)) ∧
    HomotopyCategory.subcategoryAcyclic _
      ((HomotopyCategory.quotient _ _).obj (K ⊗ S.X₂))
  simp only [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hp₁ hp₃ ⊢
  have hacy := (tensor_shortExact S hS h₃ K).acyclic_X₂ hp₁.2 hp₃.2
  exact ⟨fun n ↦ (hacy n).of_iso (β_ K S.X₂), hacy⟩

/-- A short exact extension of flat-term K-flat complexes is again flat-term and K-flat.

Source: Stacks, More on Algebra, Lemma `lemma-K-flat-two-out-of-three-ses`, together
with Algebra, Lemma `lemma-flat-ses` (blueprint: lem-kun-flat-kflat-extension).

Proof: evaluate the short exact sequence in each degree. For any module `N`, flatness
of the quotient makes tensoring this sequence with `N` short exact, by flat quotient
tensor injectivity and right exactness. For an injection `N -> N'`, the corresponding
three vertical tensor maps form a diagram of these short exact rows. If a middle
element maps to zero, its image in the quotient vanishes by flatness of the third
term; lift it to the first term. Injectivity in the bottom row and flatness of the
first term kill that lift. Thus tensoring with the middle term preserves injections,
and it is flat. For any acyclic test complex `E`, tensor the short exact sequence
with `E` and totalize. It stays short exact: each degree is a direct sum of exact
module tensor rows whose quotients are flat. The first and third total tensors are
acyclic by K-flatness. The long exact homology sequence makes the middle total tensor
acyclic. This is K-flatness; the other tensor side follows from signed symmetry.
This proof also covers zero complexes and unbounded cochain degrees. -/
theorem shortExact_flat_kFlat_middle
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (h₁ : ∀ n : ℤ, ObjectProperty.flat (S.X₁.X n))
    (h₃ : ∀ n : ℤ, ObjectProperty.flat (S.X₃.X n))
    (hk₁ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat S.X₁)
    (hk₃ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat S.X₃) :
    (∀ n : ℤ, ObjectProperty.flat (S.X₂.X n)) ∧
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat S.X₂ := by
  exact ⟨fun n ↦ module_flat_extension
    (S.map (HomologicalComplex.eval _ _ n)) (hS.map_of_exact _) (h₁ n) (h₃ n),
    kFlat_extension S hS h₃ hk₁ hk₃⟩

end CochainComplex
