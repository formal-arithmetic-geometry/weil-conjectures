/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodData
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary
public import WeilConjectures.WeilSheaf.BoundaryStalkSpecialization

/-!
# Boundary stalks of direct images as inertia invariants

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field `k₀`, `U₀` geometrically connected, `F` a lisse Weil sheaf on `U₀` with Weil fundamental
representation `(V, ρ)` and `z ∈ C₀ ∖ U₀` a boundary point with closed point `x`. Given a strictly
henselian neighbourhood of the boundary point
(`AlgebraicGeometry.WeilGroup.BoundaryNeighbourhood`), the boundary stalk `(j_* F)_x̄` is the
module of inertia invariants `V ^ (I_z)`, the Frobenius of the stalk corresponding to the residue
Frobenius lift `ρ(Frob_z)`
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_stalk_directImage_boundaryStalk`).
This is blueprint `lem-wf-boundary-stalk-invariants`.

The proof identifies, Frobenius-equivariantly, the stalk with the `Gal(Ω / K')`-invariant
sections over the geometric generic point `Spec Ω`
(`AlgebraicGeometry.WeilSheaf.exists_stalk_directImage_linearMap_invariants`), and these sections
with the Weil fundamental representation, on which the inertia group acts through `Gal(Ω / K')`
and the residue Frobenius lift through the Weil structure
(`AlgebraicGeometry.WeilGroup.genericStalkEquiv_fundamentalRep`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme Scheme.FiniteEtale ProEtale WeilSheaf

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [C.Over (Spec (.of K))]
  [U.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [IsIntegral C] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [Smooth (C ↘ Spec (.of K))]
  [IsCurve (U ↘ Spec (.of K))] [GeometricallyConnected (U ↘ Spec (.of K))] [ConnectedSpace U]
  (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [Nonempty U] [j.IsOver (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

local notation "M" =>
  universalLisseMonodromy l (Scheme.Hom.geometricFiber (U ↘ Spec (CommRingCat.of K))) K

/-- A strictly henselian neighbourhood of the boundary point `z` with closed point `x`, for the
inertia group of the chosen point over `z` and the residue Frobenius lift at `z`. -/
abbrev BoundaryNeighbourhoodAt (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints) : Type (u + 1) :=
  BoundaryNeighbourhood (K := K) j
    ((boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia Gal(Ω/C.functionField))
    (boundaryFrobeniusLift (p := C ↘ Spec (.of K)) j sU GU τ GC z) x

include τ GC in
/-- An element of the inertia group at the chosen point over `z` maps to an element of degree
zero of the Weil group. -/
lemma genericGaloisMap_mem_weilGroup_of_mem_inertia (z : ↥((Set.range j.base)ᶜ))
    {σ : Gal(Ω/C.functionField)}
    (hσ : σ ∈ (boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia Gal(Ω/C.functionField)) :
    (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (0 : ℤ)) ∈
      weilGroup (U ↘ Spec (.of K)) sU GU := by
  have : Finite (C.residueField z.1) :=
    boundary_subset_finitePoints (p := C ↘ Spec (.of K)) j z.2
  have hk : genericGaloisMap j sU GU σ ∈ inertiaGroup sU GU
      (boundaryChart (p := C ↘ Spec (.of K)) j z) (boundaryChart (p := C ↘ Spec (.of K)) j z).point :=
    ⟨σ, hσ, rfl⟩
  have hkL := inertiaGroup_le_localKernel (p := C ↘ Spec (.of K)) sU GU _ _ hk
  rw [mem_weilGroup_fundamentalGroupMap_iff j (comp_over j _) sU τ GU GC,
    MonoidHom.mem_ker.1 (localKernel_le_ker_restrictionMap j τ GU GC z.1 hkL)]
  exact (weilGroup (C ↘ Spec (.of K)) sC GC).one_mem

section Rep

variable [IsLocallyNoetherian (U ↘ Spec (.of K)).geometricFiber]
  [CompactSpace (U ↘ Spec (.of K)).geometricFiber] [IsRegular (U ↘ Spec (.of K)).geometricFiber]
  [ConnectedSpace (U ↘ Spec (.of K)).geometricFiber]
  [QuasiSeparatedSpace (U ↘ Spec (.of K)).geometricFiber]

/-- **The boundary stalk in the Weil fundamental representation.** Given a strictly henselian
neighbourhood of the boundary point `z` with closed point `x`, there is an injective linear map
from the boundary stalk `(j_* F)_x̄` to the Weil fundamental representation `F_t` (at the base
point data adapted to the geometric generic point), with image the invariants of the inertia
group `I_z`, intertwining the Frobenius of the stalk with the residue Frobenius lift at `z`.
(blueprint: `lem-wf-boundary-stalk-invariants`) -/
theorem exists_linearMap_stalk_directImage_fundamentalRep
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse) (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints)
    (hx : x.1 = z.1) (N : BoundaryNeighbourhoodAt j sU GU τ GC z x) :
    ∃ L : (((lowerStar j).obj F).stalk x).carrier →ₗ[PadicAlgCl l]
        LisseMonodromy.StalkSpace (BasePointData.ofLift j sU GU B₀ ξ hξ).t (F.toLisse hF),
      Function.Injective L ∧
      (∀ w, w ∈ LinearMap.range L ↔ ∀ g ∈ boundaryInertia (p := C ↘ Spec (.of K))
          (pU := U ↘ Spec (.of K)) j sU GU z,
        fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF g w = w) ∧
      ∀ v, L ((((lowerStar j).obj F).stalk x).frobenius v) =
        fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF
          (boundaryResidueFrobenius j sU GU (comp_over j _) τ GC z) (L v) := by
  obtain ⟨x, hxf⟩ := x
  simp only at hx
  subst hx
  letI := N.commRing
  letI := N.isStrictlyHenselianLocalRing
  letI := N.weaklyEtale
  letI := N.field
  letI := N.algebra
  letI := N.isSeparable
  letI := N.normal
  letI := N.weaklyEtale_k
  have hwF := mem_weilGroup_boundaryFrobeniusLift j sU GU (comp_over j _) τ GC z
  have ha := specMap_comp_genericGeomPoint j sU GU _ _ hwF
  obtain ⟨Sp, hSp, hSpr, hSpf⟩ := WeilSheaf.exists_stalk_directImage_linearMap_invariants j F
    N.h N.k N.e ⟨z.1, hxf⟩ N.t hF N.ht N.α N.hα N.hcα (genericGeomPoint (U ↘ Spec (.of K)) j) N.specFieldMap_comp _ ha N.hεα
  set Ψ := genericStalkEquiv B₀ ξ hξ F hF
  -- the Galois groups `Gal(Ω / K')` and `I_z`
  have hfix (σ : Ω ≃ₐ[N.K'] Ω) (a : C.functionField) :
      σ (algebraMap C.functionField Ω a) = algebraMap C.functionField Ω a := by
    obtain ⟨b, hb⟩ := N.exists_algebraMap_eq a
    rw [← hb, σ.commutes]
  let toGal (σ : Ω ≃ₐ[N.K'] Ω) : Gal(Ω/C.functionField) :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (hfix σ)
  have hσI (σ : Ω ≃ₐ[N.K'] Ω) : toGal σ ∈
      (boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia Gal(Ω/C.functionField) :=
    (N.mem_iff _).2 fun b ↦ σ.commutes b
  let ofGal (σ : Gal(Ω/C.functionField))
      (hσ : σ ∈ (boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia
        Gal(Ω/C.functionField)) : Ω ≃ₐ[N.K'] Ω :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) ((N.mem_iff σ).1 hσ)
  -- inertia acts through restrictions along `Spec σ`
  have hI (σ : Gal(Ω/C.functionField))
      (hσ : σ ∈ (boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia
        Gal(Ω/C.functionField)) (w) :
      Ψ (fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF
        ⟨_, genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z hσ⟩ w) =
      ((WeilCoefficients.toModuleCat l).map ((resOver _ _
          (show Spec.map (CommRingCat.ofHom (ofGal σ hσ).toRingHom) ≫ (genericGeomPoint (U ↘ Spec (.of K)) j) = (genericGeomPoint (U ↘ Spec (.of K)) j) by
            rw [← N.specFieldMap_comp, ← Category.assoc,
              specMap_algEquiv_comp_specFieldMap])).app
            F.obj.carrier.X)).hom (Ψ w) := by
    have h0 := specMap_comp_genericGeomPoint j sU GU σ 0
      (genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z hσ)
    rw [pow_zero] at h0
    exact genericStalkEquiv_fundamentalRep_of_deg_zero B₀ ξ hξ F hF σ _
      (h0.trans (Category.comp_id _)) w
  have hmemI (g : weilGroup (U ↘ Spec (.of K)) sU GU)
      (hg : g ∈ boundaryInertia (p := C ↘ Spec (.of K)) (pU := U ↘ Spec (.of K)) j sU GU z) :
      ∃ σ, ∃ hσ : σ ∈ (boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia
          Gal(Ω/C.functionField),
        g = ⟨_, genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z hσ⟩ := by
    obtain ⟨⟨σ, hσ, hσg⟩, hdeg⟩ := hg
    refine ⟨σ, hσ, Subtype.ext (Prod.ext hσg.symm ?_)⟩
    exact (MonoidHom.mem_ker.1 hdeg)
  refine ⟨Ψ.symm.toLinearMap ∘ₗ Sp, Ψ.symm.injective.comp hSp, fun w ↦ ?_, fun v ↦ ?_⟩
  · have hr : w ∈ LinearMap.range (Ψ.symm.toLinearMap ∘ₗ Sp) ↔ Ψ w ∈ LinearMap.range Sp := by
      refine ⟨fun ⟨v, hv⟩ ↦ ⟨v, ?_⟩, fun ⟨v, hv⟩ ↦ ⟨v, ?_⟩⟩
      · rw [← hv]
        exact (Ψ.apply_symm_apply _).symm
      · rw [LinearMap.comp_apply, hv]
        exact Ψ.symm_apply_apply w
    rw [hr, hSpr]
    constructor
    · intro h g hg
      obtain ⟨σ, hσ, rfl⟩ := hmemI g hg
      apply Ψ.injective
      rw [hI σ hσ]
      exact h (ofGal σ hσ)
    · intro h σ
      have hg : (⟨_, genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z (hσI σ)⟩ :
          weilGroup (U ↘ Spec (.of K)) sU GU) ∈
          boundaryInertia (p := C ↘ Spec (.of K)) (pU := U ↘ Spec (.of K)) j sU GU z :=
        ⟨⟨_, hσI σ, rfl⟩, rfl⟩
      have := congrArg Ψ (h _ hg)
      rw [hI _ (hσI σ)] at this
      exact this
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_eq, hSpf]
    have := genericStalkEquiv_fundamentalRep B₀ ξ hξ F hF _ _ hwF ha (Ψ.symm (Sp v))
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

end Rep

include τ GC in
/-- Blueprint `lem-wf-boundary-stalk-invariants`, together with
`prop-wf-weil-sheaf-representation-equivalence`.

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over `𝔽_q`, `U₀`
geometrically connected, with the boundary datum of actual inertia groups and residue Frobenius
lifts (`AlgebraicGeometry.WeilGroup.boundaryDatum`). Assume that every boundary point `z` has a
strictly henselian neighbourhood (`AlgebraicGeometry.WeilGroup.BoundaryNeighbourhood`). There is
a lisse sheaf–representation equivalence `ℱ ↦ (V, ρ)` for `W(U₀)`, identifying the stalk `ℱ_x̄`
with its local Frobenius with `V` with `ρ (Frob_x)` at the closed points of `U₀`, such that at
every boundary point `z` with closed point `x`, the boundary stalk `(j_* ℱ)_x̄` is isomorphic to
the inertia invariants `V ^ (I_z)`, the Frobenius of the stalk corresponding to the residue
Frobenius lift `ρ (Frob_z)`. -/
theorem exists_equivalence_isLisse_stalk_directImage_boundaryStalk
    (hN : ∀ (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints), x.1 = z.1 →
      Nonempty (BoundaryNeighbourhoodAt j sU GU τ GC z x)) :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
          (x : U.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ
            ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).frobenius x) (f v)) ∧
      ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
        (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints), x.1 = z.1 →
        ∃ f : (((directImage j).obj F.obj).stalk x).carrier ≃ₗ[PadicAlgCl l]
            (boundaryDatum (p := C ↘ Spec (.of K)) j sU GU (comp_over j _) τ GC).boundaryStalk l
              (e.functor.obj F).obj.ρ z,
          ∀ v, (f ((((directImage j).obj F.obj).stalk x).frobenius v) :
              (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ ((boundaryDatum (p := C ↘ Spec (.of K)) j sU GU
              (comp_over j _) τ GC).residueFrobenius z) (f v) := by
  have hjU : j ≫ C ↘ Spec (.of K) = U ↘ Spec (.of K) := comp_over j _
  have : SmoothOfRelativeDimension 1 (U ↘ Spec (.of K)) :=
    hjU ▸ (zero_add 1) ▸ (inferInstance : SmoothOfRelativeDimension (0 + 1) (j ≫ C ↘ Spec (.of K)))
  have : Smooth (U ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have : ConnectedSpace (U ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := U ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (U ↘ Spec (.of K)).geometricFiberProj
      (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  set W := ofFundamentalGroup (U ↘ Spec (.of K)) sU GU
  obtain ⟨B₀⟩ := nonempty_basePointData W
  obtain ⟨ξ, hξ⟩ := exists_comp_eq_of_weaklyEtale_of_surjective (UniversalCover.proj B₀.t)
    (UniversalCover.surjective_proj B₀.t) (genericGeomPoint (U ↘ Spec (.of K)) j)
  set B := BasePointData.ofLift j sU GU B₀ ξ hξ
  obtain ⟨e, h₁, -, -, -, hf⟩ := exists_equivalence_isLisse_of_lisseMonodromy W l M B
    (universalLisseMonodromy_isEquivalenceAt l _ K B.t)
  refine ⟨e, h₁, fun F z x hx ↦ ?_⟩
  rw [show (directImage j : WeilSheaf K l U ⥤ WeilSheaf K l C) = lowerStar j from rfl]
  obtain ⟨f, hf⟩ := hf F
  obtain ⟨L, hL, hLr, hLf⟩ := exists_linearMap_stalk_directImage_fundamentalRep j sU GU τ GC
    B₀ ξ hξ F.obj F.property z x hx (hN z x hx).some
  set L' := f.symm.toLinearMap ∘ₗ L
  have hL' : Function.Injective L' := f.symm.injective.comp hL
  have hr : LinearMap.range L' =
      (boundaryDatum (p := C ↘ Spec (.of K)) j sU GU (comp_over j _) τ GC).boundaryStalk l
        (e.functor.obj F).obj.ρ z := by
    ext v
    rw [BoundaryDatum.boundaryStalk, Representation.mem_invariants]
    constructor
    · rintro ⟨w, rfl⟩ ⟨g, hg⟩
      apply f.injective
      simp only [L', LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.coe_comp,
        Function.comp_apply, Subgroup.coe_subtype]
      rw [hf, f.apply_symm_apply]
      exact (hLr _).1 ⟨w, rfl⟩ g hg
    · intro h
      obtain ⟨w, hw⟩ := (hLr (f v)).2 fun g hg ↦ by
        rw [← hf]
        exact congrArg f (h ⟨g, hg⟩)
      refine ⟨w, ?_⟩
      change f.symm (L w) = v
      rw [hw, LinearEquiv.symm_apply_apply]
  refine ⟨(LinearEquiv.ofInjective L' hL').trans (LinearEquiv.ofEq _ _ hr), fun v ↦ ?_⟩
  change L' _ = (e.functor.obj F).obj.ρ _ (L' v)
  change f.symm (L _) = (e.functor.obj F).obj.ρ _ (f.symm (L v))
  apply f.injective
  rw [hf, f.apply_symm_apply, f.apply_symm_apply]
  exact hLf v

end AlgebraicGeometry.WeilGroup
