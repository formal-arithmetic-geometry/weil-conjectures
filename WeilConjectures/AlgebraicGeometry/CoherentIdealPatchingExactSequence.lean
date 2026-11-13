/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.CoherentIdealPatchingGenericEmbedding
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Short exact sequences for integral ideal patching

Stacks Project, Tag 01YL.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The geometric part of generic-point patching, without extension closure or descent
from positive finite sums. Each ideal pushforward has a positive finite sum containing
an object isomorphic to a module already satisfying P, with a small-support quotient.
(Stacks, Tag 01YL). -/
theorem coherent_ideal_patching_exact_sequence
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : P (0 : X.Modules))
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (hG :
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
    ∀ I : Z.IdealSheafData,
      ∃ (r : ℕ), 1 ≤ r ∧ ∃ (S : ShortComplex X.Modules),
        S.X₂ = @biproduct (Fin r) X.Modules _ _
          (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
          (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules)) ∧
        S.ShortExact ∧
        RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules) ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₁ ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₂ ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₃ ∧
        ∃ (G' : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G' ∧
          Nonempty (S.X₁ ≅ G') ∧ P G' ∧
          {x : X | ¬ Subsingleton (S.X₃.presheaf.stalk x)} ⊆ Set.range i.base ∧
          Subsingleton (S.X₃.presheaf.stalk ξ) := by
  classical
  obtain ⟨G, hGc, hGs, hGk, hGP⟩ := hG
  intro I
  obtain ⟨r, hr, hgeom⟩ :=
    coherent_ideal_patching_generic_embedding X Z i ξ hclosure G hGc hGs hGk I
  let M := @biproduct (Fin r) X.Modules _ _
    (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
    (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules))
  have : HasBiproduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules) :=
    HasBiproduct.of_hasProduct _
  have hc := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have hunit := isCoherent_unit_of_finite_to_locallyNoetherian i
  have : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have : (SheafOfModules.unit I.subscheme.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have : ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom I.subschemeι _
  have hIqc : I.toModules.IsQuasicoherent :=
    isQuasicoherent_kernel I.toPushforwardSubscheme
  have hIcoh : RingedSpace.IsCoherent Z.toRingedSpace I.toModules :=
    ((isCoherent_kernel_cokernel_biprod_and_submodule Z).2
      _ _ I.toModulesι hunit inferInstance hIqc).1
  have hIc := (isCoherent_pushforward_of_isFinite i I.toModules hIcoh).1
  have hMc : RingedSpace.IsCoherent X.toRingedSpace M :=
    hc.2.2.1 r _ (fun _ ↦ hIc)
  have hMs : {x : X | ¬ Subsingleton (M.presheaf.stalk x)} ⊆ Set.range i.base := by
    intro x hx
    by_contra hout
    have hz := (closedImmersion_pushforward_stalks i i.isClosedEmbedding I.toModules).1
      x hout
    let F := toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have : (toPresheaf X).PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    have : (toPresheaf X).Additive := Functor.additive_of_preserves_binary_products _
    have hzero : IsZero (F.obj ((pushforward i).obj I.toModules)) :=
      AddCommGrpCat.isZero_iff_subsingleton.mpr hz
    have hπ (j : Fin r) : F.map
        (biproduct.π (fun _ : Fin r ↦ (pushforward i).obj I.toModules) j) = 0 :=
      hzero.eq_of_tgt _ _
    have htotal := congrArg F.map
      (biproduct.total (f := fun _ : Fin r ↦ (pushforward i).obj I.toModules))
    simp only [Functor.map_sum, Functor.map_comp,
      hπ, zero_comp, Finset.sum_const_zero] at htotal
    change 0 = F.map (𝟙 M) at htotal
    rw [F.map_id] at htotal
    have hzM : IsZero (F.obj M) := (IsZero.iff_id_eq_zero _).mpr htotal.symm
    exact hx (AddCommGrpCat.isZero_iff_subsingleton.mp hzM)
  have finish (H : X.Modules) (f : H ⟶ M) [Mono f]
      (hH : RingedSpace.IsCoherent X.toRingedSpace H) (hP : P H)
      (hf : Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map f).hom) :
      ∃ S : ShortComplex X.Modules,
        S.X₂ = M ∧ S.ShortExact ∧
        RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules) ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₁ ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₂ ∧
        RingedSpace.IsCoherent X.toRingedSpace S.X₃ ∧
        ∃ G' : X.Modules, RingedSpace.IsCoherent X.toRingedSpace G' ∧
          Nonempty (S.X₁ ≅ G') ∧ P G' ∧
          {x : X | ¬ Subsingleton (S.X₃.presheaf.stalk x)} ⊆ Set.range i.base ∧
          Subsingleton (S.X₃.presheaf.stalk ξ) := by
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hQ : RingedSpace.IsCoherent X.toRingedSpace (cokernel f) :=
      (hc.1 H M f hH hMc).2
    have quotient_zero (x : X)
        (hz : ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M,
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map (cokernel.π f)).hom
            m = 0) : Subsingleton ((cokernel f).presheaf.stalk x) := by
      obtain ⟨hepi, _⟩ := (RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.1 x
      have hsurj := (ModuleCat.epi_iff_surjective _).mp hepi
      refine ⟨fun a b ↦ ?_⟩
      obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', rfl⟩ := hsurj b
      exact (hz a').trans (hz b').symm
    have hqs : {x : X | ¬ Subsingleton ((cokernel f).presheaf.stalk x)} ⊆
        Set.range i.base := by
      intro x hx
      by_contra hout
      have hzero : Subsingleton (M.presheaf.stalk x) := by
        by_contra hn
        exact hout (hMs hn)
      apply hx
      apply quotient_zero x
      intro m
      have hm : m = 0 := hzero.elim _ _
      rw [hm, map_zero]
    have hqξ : Subsingleton ((cokernel f).presheaf.stalk ξ) := by
      apply quotient_zero ξ
      intro m
      obtain ⟨n, rfl⟩ := hf m
      have heq := (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map_comp
        f (cokernel.π f)
      have hz := congrArg
        (fun k ↦ k.hom n)
        (show (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map f ≫
          (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map (cokernel.π f) = 0 by
            rw [← heq, cokernel.condition, Functor.map_zero])
      exact hz
    refine ⟨S, rfl, ?_, hIc, hH, hMc, hQ, H, hH, ⟨Iso.refl H⟩, hP, hqs, hqξ⟩
    exact { exact := ShortComplex.exact_cokernel f }
  refine ⟨r, hr, ?_⟩
  rcases hgeom with hzero | ⟨J, ι, hι, hJ, hιξ, τ, hτ, hτξ⟩
  · have hMξ := (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map_isZero hzero
    have hsub := ModuleCat.subsingleton_of_isZero hMξ
    apply finish (0 : X.Modules) (0 : (0 : X.Modules) ⟶ M) hc.2.2.2.1 hP_zero
    intro m
    exact ⟨0, hsub.elim _ _⟩
  · have : Mono ι := hι
    have : J.IsQuasicoherent := hJ
    have : Mono τ := hτ
    obtain ⟨G', hG'c, ⟨h, hfac⟩, hG'ξ, hG'P⟩ := hGP J ι hιξ
    have : Mono (h ≫ idealModuleProductι ι G) := by rw [← hfac]; infer_instance
    have : Mono h := mono_of_mono h (idealModuleProductι ι G)
    have hprod := ideal_module_product_stalk ι G ξ
    obtain ⟨e, he, hinjι, hinjprod, hrest⟩ := hprod
    have hhξ : Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map h).hom := by
      intro m
      obtain ⟨n, hn⟩ := hG'ξ
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
          (idealModuleProductι ι G)).hom m)
      refine ⟨n, hinjprod ?_⟩
      rw [hfac, Functor.map_comp] at hn
      exact hn
    apply finish (G' : X.Modules) (h ≫ τ) hG'c hG'P
    rw [Functor.map_comp]
    exact hτξ.2.comp hhξ

end AlgebraicGeometry.Scheme.Modules
