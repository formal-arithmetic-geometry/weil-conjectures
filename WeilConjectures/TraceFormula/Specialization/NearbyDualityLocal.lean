/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityCompactification
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict

/-!

# Nearby duality is local on the total space

The restriction `M.restrictOpen V` of a trait model `M` over the base to an open `V` of its total
space (keeping the identification `ε`) is again a trait model over the base
(`NearbyCyclesModel.IsTraitModelOfBase.restrictOpen`), and the inclusion is a morphism of models
over `𝟙 X` and the open immersion `i⁻¹ V ⟶ X'` of special fibres. By the compatibility of the
duality map with open restriction
(`NearbyCyclesModel.isIso_map_nearbyDualityMap_iff_of_isOpenImmersion`) and since invertibility of
a morphism of complexes is local
(`ProEtale.CondensedRing.isIso_of_forall_exists_isIso_upperStar_map`),
Gabber's theorem for all trait models over the base follows from the case of affine total spaces
(`NearbyCyclesModel.isIso_nearbyDualityMap`, from
`NearbyCyclesModel.isIso_nearbyDualityMap_of_isAffine`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

section Restrict

instance [LocallyOfFiniteType X'.hom] (V : M.total.Opens) :
    LocallyOfFiniteType (M.restrictSpecialFibre V).hom :=
  inferInstanceAs (LocallyOfFiniteType ((M.i ⁻¹ᵁ V).ι ≫ X'.hom))

instance [IsSeparated X'.hom] (V : M.total.Opens) :
    IsSeparated (M.restrictSpecialFibre V).hom :=
  inferInstanceAs (IsSeparated ((M.i ⁻¹ᵁ V).ι ≫ X'.hom))

instance [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] (V : M.total.Opens) :
    QuasiCompact (M.restrictSpecialFibre V).hom := by
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  have : IsNoetherian X'.left := ⟨⟩
  exact inferInstanceAs (QuasiCompact ((M.i ⁻¹ᵁ V).ι ≫ X'.hom))

/-- The open immersion `i⁻¹ V ⟶ X'` of special fibres of the restriction of a model to an open
`V` of its total space, as a morphism of `k'`-schemes. -/
noncomputable def restrictSpecialFibreι (V : M.total.Opens) : M.restrictSpecialFibre V ⟶ X' :=
  Over.homMk (M.i ⁻¹ᵁ V).ι rfl

instance (V : M.total.Opens) : IsOpenImmersion (M.restrictSpecialFibreι V).left :=
  inferInstanceAs (IsOpenImmersion (M.i ⁻¹ᵁ V).ι)

/-- The restriction of a trait model over the base to an open `V` of its total space with
quasi-compact inclusion is a trait model over the base. -/
lemma IsTraitModelOfBase.restrictOpen (h : M.IsTraitModelOfBase k q g) (V : M.total.Opens)
    [QuasiCompact V.ι] :
    (M.restrictOpen V).IsTraitModelOfBase (X' := M.restrictSpecialFibre V) k (V.ι ≫ q)
      ((M.j ⁻¹ᵁ V).ι ≫ g) := by
  obtain ⟨e, he, he'⟩ := h.exists_comp_ε
  obtain ⟨u, _, hu₁, hu₂⟩ := h.exists_openImmersion
  refine ⟨h.isTraitModelOver.restrictOpen V, ⟨V.ι ≫ e, ?_, ?_⟩, (M.j ⁻¹ᵁ V).ι ≫ u,
    inferInstance, ?_, ?_⟩
  · change (M.j ∣_ V) ≫ V.ι ≫ e = (M.j ⁻¹ᵁ V).ι ≫ M.ε
    rw [morphismRestrict_ι_assoc, he]
  · change V.ι ≫ e ≫ X.hom = (V.ι ≫ q) ≫ traitToBase k k'
    rw [he', Category.assoc]
  · rw [Category.assoc, hu₁]
    rfl
  · rw [Category.assoc, hu₂]

end Restrict

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- **Nearby duality is local on the total space**: the duality map `δ_{M,K}` of a trait model over
the base is an isomorphism as soon as every point of the special fibre lies in an open `V` of the
total space with quasi-compact inclusion such that the duality maps of the restriction
`M.restrictOpen V` are isomorphisms. -/
theorem isIso_nearbyDualityMap_of_forall_exists_restrictOpen (D : NearbyDualizingData k k' ℓ)
    (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (H : ∀ x : X'.left, ∃ (V : M.total.Opens) (_ : QuasiCompact V.ι), M.i x ∈ V ∧
      ∀ K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        IsIso (nearbyDualityMap ℓ D (h.restrictOpen V) K')) :
    IsIso (nearbyDualityMap ℓ D h K) := by
  have : IsLocallyNoetherian X'.left := LocallyOfFiniteType.isLocallyNoetherian X'.hom
  have : CompactSpace X'.left := QuasiCompact.compactSpace_of_compactSpace X'.hom
  have : IsNoetherian X'.left := ⟨⟩
  suffices IsIso ((boundedConstructible _).ι.map (nearbyDualityMap ℓ D h K)) from
    isIso_of_fully_faithful (boundedConstructible _).ι _
  refine isIso_of_forall_exists_isIso_upperStar_map _ _ fun x ↦ ?_
  obtain ⟨V, _, hxV, hV⟩ := H x
  refine ⟨M.i ⁻¹ᵁ V, hxV, ?_⟩
  have : IsOpenImmersion (M.restrictOpenHom V).total := inferInstanceAs (IsOpenImmersion V.ι)
  have hiff := isIso_map_nearbyDualityMap_iff_of_isOpenImmersion (j := 𝟙 X) (D := D)
    (j' := M.restrictSpecialFibreι V) ℓ (M.restrictOpenHom V) h (h.restrictOpen V)
    (isPullback_morphismRestrict M.j V).flip rfl rfl K
  have := hiff.2 (hV _)
  exact (boundedConstructible _).ι.map_isIso
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (M.restrictSpecialFibreι V)).map (nearbyDualityMap ℓ D h K))

/-- **Gabber's theorem: nearby cycles commute with Verdier duality** (Illusie, *Autour du
théorème de monodromie locale*, Thm. 4.2; SGA 7 XIII; blueprint
`sk-prop-tf-nearby-duality-foundation`). For a trait model `M` over the base of a separated
`k`-scheme `X` of finite type, over the strictly henselian trait `S = Spec k'⟦t⟧`, the duality map
`δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K`, adjoint to `θ_M ∘ Ψ(ev) ∘ μ_Ψ` with the dualizing map
`θ_M = β_a(ℚ̄_ℓ)`, is an isomorphism for every bounded constructible `K`. By open locality
(`NearbyCyclesModel.isIso_nearbyDualityMap_of_forall_exists_restrictOpen`) this is the case of
affine total spaces, `NearbyCyclesModel.isIso_nearbyDualityMap_of_isAffine`. -/
theorem isIso_nearbyDualityMap (D : NearbyDualizingData k k' ℓ) (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (nearbyDualityMap ℓ D h K) := by
  refine isIso_nearbyDualityMap_of_forall_exists_restrictOpen ℓ D h K fun x ↦ ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := M.i x) (U := ⊤) trivial
  have : IsAffine V := hV
  have hM := h.isTraitModelOver.isTraitModel.isNoetherian_total
  refine ⟨V, inferInstance, hxV, fun K' ↦ ?_⟩
  have : IsAffine (M.restrictOpen V).total := hV
  exact isIso_nearbyDualityMap_of_isAffine ℓ D (h.restrictOpen V) K'

/-- **Nearby cycles commute with Verdier duality**: for a trait model `M` over the base,
`Ψ(D_X K) ≅ D_{X'}(Ψ K)` for every bounded constructible `K`, the duality being relative to `k` on
`X` and to `k'` on the special fibre. -/
theorem nonempty_nearbyCycles_verdierDual_iso (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
        (verdierDual ℓ (toPoint X) K) ≅
      verdierDual ℓ (toPoint X') ((boundedConstructibleNearbyCycles
        (h.preservesBoundedConstructible ℓ)).obj K)) :=
  let ⟨D⟩ := nonempty_nearbyDualizingData k k' ℓ
  have := isIso_nearbyDualityMap ℓ D h K
  ⟨asIso (nearbyDualityMap ℓ D h K)⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
