/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.RepresentationTheory.LAdic
public import Mathlib.Algebra.Exact.Basic

import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Subquotients of continuous finite-dimensional coefficient representations

Source: Bhatt–Scholze, The pro-étale topology for schemes, Corollary 6.8.5, proof, p. 60
(blueprint: lem-sfb-continuous-representation-subquotients).

The ambient spaces carry their module topologies over the spectral-norm topology of `E`.
Subtype and quotient topologies are the inherited Mathlib topologies. Equivariance of the
inclusion and the surjective quotient map characterizes the induced actions uniquely.
-/

@[expose] public section

universe u v w z x y

namespace Representation

private def toEndRepresentation {R G M : Type*} [CommRing R] [Group G]
    [AddCommGroup M] [Module R M] (ρ : G →* (M ≃ₗ[R] M)) : Representation R G M where
  toFun g := (ρ g).toLinearMap
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

private def toAutRepresentation {R G M : Type*} [CommRing R] [Group G]
    [AddCommGroup M] [Module R M] (ρ : Representation R G M) : G →* (M ≃ₗ[R] M) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).toMonoidHom.comp ρ.asGroupHom

private theorem moduleTopology_t2 (R M : Type*) [NontriviallyNormedField R]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    [TopologicalSpace M] [IsModuleTopology R M] : T2Space M := by
  exact T2Space.of_injective_continuous (Module.finBasis R M).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (Module.finBasis R M).equivFun.toLinearMap)

private theorem coefficient_subquotients
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [tE : TopologicalSpace E]
    (hE : tE =
      (spectralNorm.nontriviallyNormedField ℚ_[l] E).toUniformSpace.toTopologicalSpace)
    (G : ProfiniteGrp.{v}) (V : Type w) [AddCommGroup V] [Module E V]
    [TopologicalSpace V] [IsModuleTopology E V]
    (ρ : G →* (V ≃ₗ[E] V)) (hV : IsContinuousCoefficient l E G V ρ) :
    (∀ (U : Submodule E V) (_hU : ∀ (g : G) (a : V), a ∈ U → ρ g a ∈ U),
      IsClosed (U : Set V) ∧ IsModuleTopology E U ∧ IsModuleTopology E (V ⧸ U) ∧
      ∃ (τ : G →* (U ≃ₗ[E] U)) (κ : G →* ((V ⧸ U) ≃ₗ[E] (V ⧸ U))),
        IsContinuousCoefficient l E G U τ ∧
        IsContinuousCoefficient l E G (V ⧸ U) κ ∧
        Continuous (fun p : G × U ↦ τ p.1 p.2) ∧
        Continuous (fun p : G × (V ⧸ U) ↦ κ p.1 p.2) ∧
        IsEquivariant E G U V τ ρ U.subtype ∧ Continuous U.subtype ∧
        IsEquivariant E G V (V ⧸ U) ρ κ U.mkQ ∧ Continuous U.mkQ) := by
  subst tE
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  have : FiniteDimensional E V := hV.1
  have : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup E V
  have : T2Space V := moduleTopology_t2 E V
  have hρ : Continuous (fun p : G × V ↦ ρ p.1 p.2) := by
    convert hV.2 using 1 <;> rw [eq_moduleTopology E V]
  intro U hU
  have : IsModuleTopology E U := isModuleTopologyOfFiniteDimensional
  let τ := toAutRepresentation ((toEndRepresentation ρ).subrepresentation U hU)
  let κ := toAutRepresentation ((toEndRepresentation ρ).quotient U hU)
  have hτ : Continuous (fun p : G × U ↦ τ p.1 p.2) := by
    exact (hρ.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hκ : Continuous (fun p : G × (V ⧸ U) ↦ κ p.1 p.2) := by
    rw [← (IsOpenQuotientMap.id.prodMap U.isOpenQuotientMap_mkQ).continuous_comp_iff]
    exact U.continuous_mkQ.comp hρ
  refine ⟨U.closed_of_finiteDimensional, inferInstance, inferInstance, τ, κ, ?_, ?_,
    hτ, hκ, ?_, continuous_subtype_val, ?_, U.continuous_mkQ⟩
  · refine ⟨inferInstance, ?_⟩
    convert hτ using 1 <;> rw [eq_moduleTopology E U]
  · refine ⟨inferInstance, ?_⟩
    convert hκ using 1 <;> rw [eq_moduleTopology E (V ⧸ U)]
  · intro g x
    rfl
  · intro g x
    rfl

/-- Subspaces, quotients, kernels, images and cokernels of continuous coefficient
representations, with their usual topologies and canonical universal properties.

Source: Bhatt–Scholze, Corollary 6.8.5, proof, p. 60
(blueprint: lem-sfb-continuous-representation-subquotients).

Proof plan:
1. A finite extension of the p-adics is complete and nontrivially normed
   (`def-weil-l-adic-coefficient-extension`). Finite-dimensional subspaces are closed by
   `lem-sfb-finite-dimensional-subspace-closed`. Their inherited topology agrees with
   the module topology by continuity of linear maps in both directions
   (`lem-sfb-finite-dimensional-linear-map-continuous`). Restrict the ambient action
   along the subtype embedding to obtain the jointly continuous action on the subspace.
2. The quotient map is a continuous open surjection
   (`lem-sfb-finite-dimensional-quotient-open`), as are its products with identity maps.
   Descend addition, scalar multiplication and the group action along these quotient maps.
   Compare the resulting vector-space topology with the module topology using continuity
   of the linear identity maps in both directions. Inclusion and projection are equivariant.
3. For an equivariant linear map, its kernel and image are invariant. Apply steps 1 and 2
   to the kernel, image and quotient by the image. The range corestriction is continuous
   by `lem-sfb-finite-dimensional-linear-map-continuous`, as is the original map.
4. The two displayed sequences are exact on vector spaces: the subtype maps are injective,
   the corestriction and quotient maps are surjective, and their images equal the kernels.
   All arrows are equivariant and continuous by the preceding steps.
5. A map annihilated by the original map factors uniquely through its kernel; a map
   annihilating its image factors uniquely through the quotient. Injectivity of inclusion
   and surjectivity of projection prove equivariance of the factors. The factors are
   continuous by `lem-sfb-finite-dimensional-linear-map-continuous`. These are precisely
   the kernel and cokernel universal properties among the representations of
   `def-pod-l-adic-representations` (2). -/
theorem continuousCoefficient_subquotients
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (E : IntermediateField ℚ_[l] Ω)
    [FiniteDimensional ℚ_[l] E] [tE : TopologicalSpace E]
    (_hE : tE =
      (spectralNorm.nontriviallyNormedField ℚ_[l] E).toUniformSpace.toTopologicalSpace)
    (G : ProfiniteGrp.{v}) (V : Type w) [AddCommGroup V] [Module E V]
    [TopologicalSpace V] [IsModuleTopology E V]
    (ρ : G →* (V ≃ₗ[E] V)) (hV : IsContinuousCoefficient l E G V ρ) :
    (∀ (U : Submodule E V) (_hU : ∀ (g : G) (a : V), a ∈ U → ρ g a ∈ U),
      IsClosed (U : Set V) ∧ IsModuleTopology E U ∧ IsModuleTopology E (V ⧸ U) ∧
      ∃ (τ : G →* (U ≃ₗ[E] U)) (κ : G →* ((V ⧸ U) ≃ₗ[E] (V ⧸ U))),
        IsContinuousCoefficient l E G U τ ∧
        IsContinuousCoefficient l E G (V ⧸ U) κ ∧
        Continuous (fun p : G × U ↦ τ p.1 p.2) ∧
        Continuous (fun p : G × (V ⧸ U) ↦ κ p.1 p.2) ∧
        IsEquivariant E G U V τ ρ U.subtype ∧ Continuous U.subtype ∧
        IsEquivariant E G V (V ⧸ U) ρ κ U.mkQ ∧ Continuous U.mkQ) ∧
    (∀ (W : Type z) [AddCommGroup W] [Module E W]
      [TopologicalSpace W] [IsModuleTopology E W]
      (σ : G →* (W ≃ₗ[E] W)) (_hW : IsContinuousCoefficient l E G W σ)
      (h : V →ₗ[E] W) (_hh : IsEquivariant E G V W ρ σ h),
      Continuous h ∧
      ∃ (τK : G →* (LinearMap.ker h ≃ₗ[E] LinearMap.ker h))
        (τI : G →* (LinearMap.range h ≃ₗ[E] LinearMap.range h))
        (τQ : G →* ((W ⧸ LinearMap.range h) ≃ₗ[E] (W ⧸ LinearMap.range h))),
        IsContinuousCoefficient l E G (LinearMap.ker h) τK ∧
        IsContinuousCoefficient l E G (LinearMap.range h) τI ∧
        IsContinuousCoefficient l E G (W ⧸ LinearMap.range h) τQ ∧
        IsModuleTopology E (LinearMap.ker h) ∧ IsModuleTopology E (LinearMap.range h) ∧
        IsModuleTopology E (W ⧸ LinearMap.range h) ∧
        Continuous (fun p : G × LinearMap.ker h ↦ τK p.1 p.2) ∧
        Continuous (fun p : G × LinearMap.range h ↦ τI p.1 p.2) ∧
        Continuous (fun p : G × (W ⧸ LinearMap.range h) ↦ τQ p.1 p.2) ∧
        IsEquivariant E G (LinearMap.ker h) V τK ρ (LinearMap.ker h).subtype ∧
        Continuous (LinearMap.ker h).subtype ∧
        IsEquivariant E G V (LinearMap.range h) ρ τI h.rangeRestrict ∧
        Continuous h.rangeRestrict ∧
        IsEquivariant E G (LinearMap.range h) W τI σ (LinearMap.range h).subtype ∧
        Continuous (LinearMap.range h).subtype ∧
        IsEquivariant E G W (W ⧸ LinearMap.range h) σ τQ (LinearMap.range h).mkQ ∧
        Continuous (LinearMap.range h).mkQ ∧
        Function.Injective (LinearMap.ker h).subtype ∧
        Function.Exact (LinearMap.ker h).subtype h.rangeRestrict ∧
        Function.Surjective h.rangeRestrict ∧
        Function.Injective (LinearMap.range h).subtype ∧
        Function.Exact (LinearMap.range h).subtype (LinearMap.range h).mkQ ∧
        Function.Surjective (LinearMap.range h).mkQ ∧
        (∀ (X : Type x) [AddCommGroup X] [Module E X]
          [TopologicalSpace X] [IsModuleTopology E X]
          (ξ : G →* (X ≃ₗ[E] X)) (_hX : IsContinuousCoefficient l E G X ξ)
          (f : X →ₗ[E] V) (_hf : IsEquivariant E G X V ξ ρ f) (_hzero : h.comp f = 0),
          ∃! f' : X →ₗ[E] LinearMap.ker h,
            IsEquivariant E G X (LinearMap.ker h) ξ τK f' ∧ Continuous f' ∧
            (LinearMap.ker h).subtype.comp f' = f) ∧
        (∀ (Y : Type y) [AddCommGroup Y] [Module E Y]
          [TopologicalSpace Y] [IsModuleTopology E Y]
          (υ : G →* (Y ≃ₗ[E] Y)) (_hY : IsContinuousCoefficient l E G Y υ)
          (g : W →ₗ[E] Y) (_hg : IsEquivariant E G W Y σ υ g) (_hzero : g.comp h = 0),
          ∃! g' : (W ⧸ LinearMap.range h) →ₗ[E] Y,
            IsEquivariant E G (W ⧸ LinearMap.range h) Y τQ υ g' ∧ Continuous g' ∧
            g'.comp (LinearMap.range h).mkQ = g)) := by
  subst tE
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  have : FiniteDimensional E V := hV.1
  have : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup E V
  have : T2Space V := moduleTopology_t2 E V
  refine ⟨coefficient_subquotients l E rfl G V ρ hV, ?_⟩
  intro W _ _ _ _ σ hW h hh
  have : FiniteDimensional E W := hW.1
  have : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup E W
  have hK : ∀ (g : G) (a : V), a ∈ LinearMap.ker h → ρ g a ∈ LinearMap.ker h := by
    intro g a ha
    change h (ρ g a) = 0
    rw [hh g a, (show h a = 0 from ha), map_zero]
  have hI : ∀ (g : G) (a : W), a ∈ LinearMap.range h → σ g a ∈ LinearMap.range h := by
    intro g a ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨ρ g b, hh g b⟩
  obtain ⟨_, hKtop, _, τK, _, hτK, _, hKcont, _, hKeq, hKinc, _, _⟩ :=
    coefficient_subquotients l E rfl G V ρ hV (LinearMap.ker h) hK
  obtain ⟨_, hItop, hQtop, τI, τQ, hτI, hτQ, hIcont, hQcont, hIeq, hIinc,
    hQeq, hQproj⟩ := coefficient_subquotients l E rfl G W σ hW (LinearMap.range h) hI
  have hcoreq : IsEquivariant E G V (LinearMap.range h) ρ τI h.rangeRestrict := by
    intro g a
    apply Subtype.ext
    exact (hh g a).trans (hIeq g (h.rangeRestrict a)).symm
  have hco : Continuous h.rangeRestrict :=
    h.continuous_of_finiteDimensional.subtype_mk _
  refine ⟨h.continuous_of_finiteDimensional, τK, τI, τQ, hτK, hτI, hτQ,
    hKtop, hItop, hQtop, hKcont, hIcont, hQcont, hKeq, hKinc, hcoreq, hco, hIeq, hIinc,
    hQeq, hQproj, Subtype.val_injective, ?_, h.surjective_rangeRestrict,
    Subtype.val_injective, LinearMap.exact_subtype_mkQ _, Submodule.mkQ_surjective _, ?_, ?_⟩
  · rw [LinearMap.exact_iff, h.ker_rangeRestrict, Submodule.range_subtype]
  · intro X _ _ _ _ ξ hX f hf hzero
    have hmem : ∀ a : X, f a ∈ LinearMap.ker h := by
      intro a
      exact DFunLike.congr_fun hzero a
    let f' := f.codRestrict (LinearMap.ker h) hmem
    have hfac : (LinearMap.ker h).subtype.comp f' = f := rfl
    refine ⟨f', ⟨?_, ?_, hfac⟩, ?_⟩
    · intro g a
      apply Subtype.ext
      exact (hf g a).trans (hKeq g (f' a)).symm
    · exact (IsModuleTopology.continuous_of_linearMap f).subtype_mk _
    · intro f'' hf''
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      exact DFunLike.congr_fun hf''.2.2 a
  · intro Y _ _ _ _ υ hY g hg hzero
    have : IsTopologicalAddGroup Y := IsModuleTopology.topologicalAddGroup E Y
    have hmem : LinearMap.range h ≤ LinearMap.ker g := by
      rintro _ ⟨a, rfl⟩
      exact DFunLike.congr_fun hzero a
    let g' := (LinearMap.range h).liftQ g hmem
    have hfac : g'.comp (LinearMap.range h).mkQ = g := Submodule.liftQ_mkQ _ _ _
    refine ⟨g', ⟨?_, ?_, hfac⟩, ?_⟩
    · intro a q
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range h) q
      rw [← hQeq a b]
      exact hg a b
    · exact IsModuleTopology.continuous_of_linearMap g'
    · intro g'' hg''
      apply LinearMap.ext
      intro q
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range h) q
      exact DFunLike.congr_fun hg''.2.2 b

end Representation
