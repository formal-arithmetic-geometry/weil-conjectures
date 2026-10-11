/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit

/-!
# Constant sheaves on a normal integral scheme and the generic point

Let `Z` be an integral scheme with integrally closed local rings, `K` its function field and
`g : Spec K ⟶ Z` the generic point. For a `Λ`-module `M` the unit `M_Z ⟶ g_* g^* M_Z` is an
isomorphism [Stacks 09Z5]. We check it on the étale `Z`-schemes `W` that are integral: there the
constant sections are `M` (connectedness), and `W ×_Z Spec K` is a single point, the generic
point of `W`. Every étale `Z`-scheme is covered by integral ones, because étale algebras over a
normal domain are finite products of domains (Stacks 092W).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The forgetful functor from `Λ`-modules to sets preserves sheaves on the small étale site. -/
instance (X : Scheme.{u}) :
    X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  inferInstance

/-- A morphism of étale sheaves of `Λ`-modules which is bijective on the sections over the
members of a family of étale schemes covering every étale scheme is an isomorphism. -/
theorem Scheme.isIso_of_bijective_app_of_forall_exists {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) (P : X.Etale → Prop)
    (hP : ∀ (V : X.Etale) (x : V.left), ∃ (W : X.Etale) (g : W ⟶ V), P W ∧ x ∈ Set.range g.left)
    (hφ : ∀ W, P W → Function.Bijective (φ.hom.app (op W))) : IsIso φ := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (A := ModuleCat.{u + 1} Λ)]
  refine ⟨⟨fun {V} a b h ↦ (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_⟩,
    ⟨fun {V} s ↦ (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_⟩⟩
  · obtain ⟨W, g, hW, hx⟩ := hP V.unop x
    refine ⟨W, g, (hφ W hW).1 ?_, hx⟩
    rw [NatTrans.naturality_apply φ.hom g.op a, NatTrans.naturality_apply φ.hom g.op b]
    exact congrArg _ h
  · obtain ⟨W, g, hW, hx⟩ := hP V x
    exact ⟨W, g, (hφ W hW).2 _, hx⟩

/-- An étale morphism from an integral scheme to an integral scheme sends the generic point to
the generic point, and is the only point over it. -/
lemma Scheme.Hom.preimage_genericPoint_eq_of_etale {W Z : Scheme.{u}} [IsIntegral W]
    [IsIntegral Z] (f : W ⟶ Z) [AlgebraicGeometry.Etale f] :
    f ⁻¹' {genericPoint Z} = {genericPoint W} := by
  have hη : f (genericPoint W) = genericPoint Z := by
    obtain ⟨w₀, hw₀⟩ : genericPoint Z ∈ Set.range f.base := by
      have := (genericPoint_spec Z).mem_open_set_iff (U := Set.range f.base)
        f.isOpenMap.isOpen_range
      rw [this, Set.univ_inter]
      exact Set.range_nonempty _
    have h₁ : f (genericPoint W) ⤳ genericPoint Z :=
      hw₀ ▸ ((genericPoint_spec W).specializes (Set.mem_univ w₀)).map f.continuous
    exact (h₁.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ _))).eq
  ext w
  refine ⟨fun hw ↦ ?_, fun hw ↦ by rw [Set.mem_singleton_iff.1 hw]; exact hη⟩
  have hdisc := f.isDiscrete_preimage_singleton (genericPoint Z)
  have : DiscreteTopology (f ⁻¹' {genericPoint Z}) := hdisc.to_subtype
  have hsp : (⟨genericPoint W, hη⟩ : f ⁻¹' {genericPoint Z}) ⤳ ⟨w, hw⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.1
      ((genericPoint_spec W).specializes (Set.mem_univ w))
  exact congrArg Subtype.val hsp.eq.symm

/-- **The generic fibre of an integral étale scheme is a point.** For an étale morphism
`f : W ⟶ Z` of integral schemes, `W ×_Z Spec 𝒪_{Z,η}` has exactly one point. -/
lemma Scheme.Hom.subsingleton_pullback_fromSpecStalk_genericPoint {W Z : Scheme.{u}}
    [IsIntegral W] [IsIntegral Z] (f : W ⟶ Z) [AlgebraicGeometry.Etale f] :
    Subsingleton ↥(pullback f (Z.fromSpecStalk (genericPoint Z))) ∧
      Nonempty ↥(pullback f (Z.fromSpecStalk (genericPoint Z))) := by
  have hr : Set.range (pullback.fst f (Z.fromSpecStalk (genericPoint Z))).base =
      {genericPoint W} := by
    rw [Scheme.Pullback.range_fst, range_fromSpecStalk, ← f.preimage_genericPoint_eq_of_etale]
    congr 1
    ext y
    exact ⟨fun h ↦ (h.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ y))).eq,
      fun h ↦ by rw [Set.mem_singleton_iff.1 h]; exact specializes_rfl⟩
  have hinj := (pullback.fst f (Z.fromSpecStalk (genericPoint Z))).isEmbedding.injective
  refine ⟨⟨fun a b ↦ hinj ?_⟩, ?_⟩
  · have ha : _ ∈ Set.range (pullback.fst f (Z.fromSpecStalk (genericPoint Z))).base := ⟨a, rfl⟩
    have hb : _ ∈ Set.range (pullback.fst f (Z.fromSpecStalk (genericPoint Z))).base := ⟨b, rfl⟩
    rw [hr] at ha hb
    exact ha.trans hb.symm
  · obtain ⟨a, -⟩ := (Set.ext_iff.1 hr (genericPoint W)).2 rfl
    exact ⟨a⟩

/-- **Étale schemes over a normal integral scheme are locally integral.** -/
lemma Scheme.exists_isIntegral_of_isIntegrallyClosed {Z : Scheme.{u}} [IsIntegral Z]
    (hZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)) (V : Z.Etale) (x : V.left) :
    ∃ U : V.left.Opens, x ∈ U ∧ IsIntegral U.toScheme := by
  sorry

/-- **Constant sheaves on a normal integral scheme, at the generic point** (the generic-point
half of Stacks 09Z5). Let `Z` be an integral scheme whose local rings are integrally closed and
`g : Spec 𝒪_{Z,η} ⟶ Z` its generic point. Then the unit `M_Z ⟶ g_* g^* M_Z` is an isomorphism.
-/
theorem Etale.isIso_unit_constantSheaf_fromSpecStalk_genericPoint (Z : Scheme.{u})
    [IsIntegral Z] (hZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Z.fromSpecStalk (genericPoint Z))).unit.app
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  let g := Z.fromSpecStalk (genericPoint Z)
  suffices h : IsIso (Etale.constantSheafUnit g M) by
    have : IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)) := h
    exact IsIso.of_isIso_comp_right _ ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).map
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M))
  refine Scheme.isIso_of_bijective_app_of_forall_exists _ (fun W ↦ IsIntegral W.left)
    (fun V x ↦ ?_) (fun W hW ↦ ?_)
  · obtain ⟨U, hxU, hU⟩ := Scheme.exists_isIntegral_of_isIntegrallyClosed hZ V x
    exact ⟨Etale.ofOpens V U, Etale.ofOpensι V U, hU, ⟨x, hxU⟩, rfl⟩
  · have : AlgebraicGeometry.Etale W.hom := W.prop
    have : IsIntegral ((𝟭 Scheme).obj W.left) := hW
    have : IsIntegral ((Functor.fromPUnit Z).obj W.right) := ‹IsIntegral Z›
    obtain ⟨hsub, hne⟩ := W.hom.subsingleton_pullback_fromSpecStalk_genericPoint
    let FW := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj W
    have : ConnectedSpace FW.left := by
      have : Subsingleton FW.left := hsub
      exact { isPreconnected_univ :=
                _root_.Set.Subsingleton.isPreconnected Set.subsingleton_of_subsingleton
              toNonempty := hne }
    obtain ⟨p⟩ : Nonempty FW.left := hne
    refine ⟨fun a b h ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨m, rfl⟩ := Scheme.surjective_toSheafify_app_of_connectedSpace Z M W a
      obtain ⟨m', rfl⟩ := Scheme.surjective_toSheafify_app_of_connectedSpace Z M W b
      rw [Etale.constantSheafUnit_app_toSheafify, Etale.constantSheafUnit_app_toSheafify] at h
      let ψ := ((Spec (Z.presheaf.stalk (genericPoint Z))).moduleConstantSheafToPointFunctionSheaf
        M).hom.app (op FW)
      have e₁ := Scheme.moduleConstantSheafToPointFunctionSheaf_app_toSheafify _ M FW m
      have e₂ := Scheme.moduleConstantSheafToPointFunctionSheaf_app_toSheafify _ M FW m'
      have : (fun _ : FW.left ↦ m) = fun _ ↦ m' := e₁.symm.trans ((congrArg ψ h).trans e₂)
      rw [congrFun this p]
    · obtain ⟨m, rfl⟩ := Scheme.surjective_toSheafify_app_of_connectedSpace _ M FW y
      exact ⟨_, Etale.constantSheafUnit_app_toSheafify g M W m⟩

end AlgebraicGeometry
