/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.LocallyConstantNonzeroGerms
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # A generic stalk detects kernels in a locally constant sheaf -/

@[expose] public section

universe u₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A morphism from a locally constant abelian étale sheaf is mono when its
geometric generic stalk map is mono. Local constancy is that of the underlying sheaf of sets. -/
theorem mono_of_mono_generic_stalk
    (X : Scheme.{u₂}) (hX : IsIrreducible (Set.univ : Set X))
    (hne : Nonempty X) (η : X)
    (hη : IsGenericPoint η (Set.univ : Set X))
    (Ω : Type u₂) [Field Ω] [IsAlgClosed Ω]
    (barη : Spec (.of Ω) ⟶ X) (hbarη : barη default = η)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u₂ + 1})
    (hF : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u₂ + 1})).obj F))
    (φ : F ⟶ G)
    (hφ : Mono ((pointSmallEtale barη).sheafFiber.map φ)) : Mono φ := by
  classical
  have _ := hX
  have _ := hne
  let := hφ
  apply Abelian.mono_of_kernel_ι_eq_zero
  by_contra hk
  obtain ⟨U, hU, s, hs⟩ := exists_section_everywhere_nonzero_germ X (kernel φ) F hF
    (kernel.ι φ) hk
  have hopen : IsOpen (Set.range U.hom) := U.hom.isOpenMap.isOpen_range
  have hmem : η ∈ Set.range U.hom := (hη.mem_open_set_iff hopen).2
    ⟨U.hom (Classical.choice hU), Set.mem_univ _, Set.mem_range_self _⟩
  obtain ⟨w, hw⟩ := hmem
  obtain ⟨t, ht⟩ := pointSmallEtaleFiberObjToPreimage_surjective barη hbarη U
    ⟨w, by simpa using hw⟩
  have hz : (pointSmallEtale barη).sheafFiber.map (kernel.ι φ) = 0 := by
    apply (cancel_mono ((pointSmallEtale barη).sheafFiber.map φ)).1
    simp only [← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]
  have hnat := (pointSmallEtale barη).toPresheafFiber_naturality
    (kernel.ι φ).hom U t
  have hzero : (pointSmallEtale barη).toPresheafFiber U t F.obj
      ((kernel.ι φ).hom.app (Opposite.op U) s) = 0 := by
    have heq : (kernel.ι φ).hom.app (Opposite.op U) ≫
        (pointSmallEtale barη).toPresheafFiber U t F.obj = 0 := by
      rw [← hnat]
      change (pointSmallEtale barη).toPresheafFiber U t (kernel φ).obj ≫
        (pointSmallEtale barη).sheafFiber.map (kernel.ι φ) = 0
      rw [hz, comp_zero]
    exact congrArg (fun f ↦ f s) heq
  exact hs Ω barη t hzero



end AlgebraicGeometry.Scheme
