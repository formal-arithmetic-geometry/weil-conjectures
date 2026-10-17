/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericPath
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift

/-!
# The Weil fundamental representation at the geometric generic point

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over `k₀`, `F` a
lisse Weil sheaf on `U₀`, `η : Spec Ω ⟶ Ū` the geometric generic point, and `B` the base point
data adapted to a lift `ξ` of `η` to the universal cover at the base point `t`
(`AlgebraicGeometry.WeilGroup.BasePointData.ofLift`). The restriction along `ξ` identifies the
Weil fundamental representation `V = F_t` with the sections `Γ(Spec Ω, η^* F)` at the generic
point (`AlgebraicGeometry.WeilGroup.genericStalkEquiv`), and for `σ ∈ Gal(Ω / k(C))` whose image
`w = (ρ(σ), n)` lies in the Weil group:

* if `n = 0`, then `ρ(w)` corresponds to the restriction along `Spec σ`
  (`AlgebraicGeometry.WeilGroup.genericStalkEquiv_fundamentalRep_of_deg_zero`);
* in general, `ρ(w)` corresponds to the transport along the square `Spec σ ≫ η = η ≫ Frⁿ` and the
  iterated Weil structure `φ_n` (`AlgebraicGeometry.WeilGroup.genericStalkEquiv_fundamentalRep`).

For `σ` in the inertia group at a boundary point and for a residue Frobenius lift, this is the
action of the inertia group and of the Frobenius on the generic stalk in blueprint
`lem-wf-boundary-stalk-invariants`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme Scheme.FiniteEtale ProEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [U.Over (Spec (.of K))]
  [IsCurve (U ↘ Spec (.of K))] [GeometricallyConnected (U ↘ Spec (.of K))] [ConnectedSpace U]
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] [IsIntegral C]
  {sU : Spec (.of (AlgebraicClosure K)) ⟶ U}
  {GU : Type u} [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  [IsLocallyNoetherian (U ↘ Spec (.of K)).geometricFiber]
  [CompactSpace (U ↘ Spec (.of K)).geometricFiber] [IsRegular (U ↘ Spec (.of K)).geometricFiber]
  [ConnectedSpace (U ↘ Spec (.of K)).geometricFiber]
  [QuasiSeparatedSpace (U ↘ Spec (.of K)).geometricFiber]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

local notation "M" =>
  universalLisseMonodromy l (Scheme.Hom.geometricFiber (U ↘ Spec (CommRingCat.of K))) K

variable (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
  (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
  (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)

/-- The identification `F_t ≅ Γ(Spec Ω, η^* F)` of the Weil fundamental representation with the
sections at the geometric generic point, by restriction along the lift `ξ`. -/
noncomputable def genericStalkEquiv
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse) :
    LisseMonodromy.StalkSpace (BasePointData.ofLift j sU GU B₀ ξ hξ).t (F.toLisse hF)
      ≃ₗ[PadicAlgCl l]
      (WeilCoefficients.toModuleCat l).obj ((Sheaf.Γ _ _).obj
        ((genericGeomPoint (U ↘ Spec (.of K)) j)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X)) :=
  WeilCoefficients.linearEquivOfIso (liftStalkIso B₀.t ξ hξ (F.toLisse hF))

include ξ hξ in
/-- The identification `F_t ≅ Γ(Spec Ω, η^* F)` on elements. -/
lemma genericStalkEquiv_apply (F : WeilSheaf K l U) (hF : F.IsLisse)
    (v : LisseMonodromy.StalkSpace (BasePointData.ofLift j sU GU B₀ ξ hξ).t (F.toLisse hF)) :
    genericStalkEquiv B₀ ξ hξ F hF v =
      ((WeilCoefficients.toModuleCat l).map (liftStalkIso B₀.t ξ hξ (F.toLisse hF)).hom).hom v :=
  rfl

include ξ hξ in
/-- **Degree-zero Galois elements act by restriction.** If the image `w = (ρ(σ), 0)` of
`σ ∈ Gal(Ω / k(C))` lies in the Weil group (for instance `σ` in an inertia group at a boundary
point), then `ρ(w)` on `F_t` corresponds to the restriction along `Spec σ` on
`Γ(Spec Ω, η^* F)`. -/
theorem genericStalkEquiv_fundamentalRep_of_deg_zero (F : WeilSheaf K l U) (hF : F.IsLisse)
    (σ : Gal(Ω/C.functionField))
    (hw : (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (0 : ℤ)) ∈
      weilGroup (U ↘ Spec (.of K)) sU GU)
    (ha : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericGeomPoint (U ↘ Spec (.of K)) j =
      genericGeomPoint (U ↘ Spec (.of K)) j)
    (v : LisseMonodromy.StalkSpace (BasePointData.ofLift j sU GU B₀ ξ hξ).t (F.toLisse hF)) :
    genericStalkEquiv B₀ ξ hξ F hF (fundamentalRep M
        (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF ⟨_, hw⟩ v) =
      ((WeilCoefficients.toModuleCat l).map ((resOver _ _ ha).app F.obj.carrier.X)).hom
        (genericStalkEquiv B₀ ξ hξ F hF v) := by
  set B := BasePointData.ofLift j sU GU B₀ ξ hξ
  have h' : (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ξ) ≫ UniversalCover.proj B₀.t =
      genericGeomPoint (U ↘ Spec (.of K)) j := by
    rw [Category.assoc, hξ, ha]
  set g := UniversalCover.liftPath B₀.t _ h' ≪≫ (UniversalCover.liftPath B₀.t ξ hξ).symm
  have hgw : (⟨_, hw⟩ : (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).carrier) = B.geomHom g := by
    apply Subtype.ext
    rw [BasePointData.weilGroupEquiv_geomHom, BasePointData.geomAut_ofLift B₀ ξ hξ σ h']
    rfl
  have hgeo := fundamentalRep_geometric M B.weilMonodromyData F hF ⟨B.geomHom g, B.geomHom_mem g⟩
  rw [show (B.weilMonodromyData.geomEquiv.symm ⟨B.geomHom g, B.geomHom_mem g⟩) = g from
    B.geomEquiv.symm_apply_eq.2 (Subtype.ext (B.geomEquiv_apply g).symm)] at hgeo
  change genericStalkEquiv B₀ ξ hξ F hF (fundamentalRep M B.weilMonodromyData F hF
    (B.geomHom g) v) = _
  rw [show fundamentalRep M B.weilMonodromyData F hF (B.geomHom g) =
    LisseMonodromy.rep M B.t (F.toLisse hF) g from hgeo]
  have e := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v)
    (liftStalkIso_resOver B₀.t ξ hξ _ ha h' (F.toLisse hF))
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e.symm

include ξ hξ in
/-- **Galois elements of degree `n` act through the Weil structure.** If the image
`w = (ρ(σ), n)` of `σ ∈ Gal(Ω / k(C))` lies in the Weil group (for instance a residue Frobenius
lift at a boundary point), so that `Spec σ ≫ η = η ≫ Frⁿ`, then `ρ(w)` on `F_t` corresponds to the
transport of `Γ(Spec Ω, η^* F)` along the square `Spec σ ≫ η = η ≫ Frⁿ` and the iterated Weil
structure `φ_n`. -/
theorem genericStalkEquiv_fundamentalRep (F : WeilSheaf K l U) (hF : F.IsLisse)
    (σ : Gal(Ω/C.functionField)) (n : ℕ)
    (hw : (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (n : ℤ)) ∈
      weilGroup (U ↘ Spec (.of K)) sU GU)
    (ha : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericGeomPoint (U ↘ Spec (.of K)) j =
      genericGeomPoint (U ↘ Spec (.of K)) j ≫
        ((U ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).hom)
    (v : LisseMonodromy.StalkSpace (BasePointData.ofLift j sU GU B₀ ξ hξ).t (F.toLisse hF)) :
    genericStalkEquiv B₀ ξ hξ F hF (fundamentalRep M
        (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF ⟨_, hw⟩ v) =
      ((WeilCoefficients.toModuleCat l).map
        (globalSectionsTransport _ ha (F.frobeniusPowStr n))).hom
        (genericStalkEquiv B₀ ξ hξ F hF v) := by
  set B := BasePointData.ofLift j sU GU B₀ ξ hξ
  set Fr := (U ↘ Spec (.of K)).geometricGaloisFrobenius
  have h₁ : (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ξ) ≫ UniversalCover.proj B₀.t =
      genericGeomPoint (U ↘ Spec (.of K)) j ≫ (Fr ^ n).hom := by
    rw [Category.assoc, hξ, ha]
  have h₂ : (ξ ≫ UniversalCover.map (Fr ^ n).hom B₀.t) ≫
      UniversalCover.proj (B₀.t ≫ (Fr ^ n).hom) =
        genericGeomPoint (U ↘ Spec (.of K)) j ≫ (Fr ^ n).hom := by
    rw [Category.assoc, UniversalCover.map_proj, ← Category.assoc, hξ]
  have hd : (B₀.t ≫ (Fr ^ n).hom) ≫ (U ↘ Spec (.of K)).geometricFiberProj =
      B₀.t ≫ (U ↘ Spec (.of K)).geometricFiberProj := by
    rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  set δ := UniversalCover.liftPath B₀.t _ h₁ ≪≫
    (UniversalCover.liftPath (B₀.t ≫ (Fr ^ n).hom) _ h₂).symm
  set g' := δ ≪≫ (B.frobPathPow n).symm
  have hwB : (⟨_, hw⟩ : (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).carrier) =
      B.frobLift ^ n * B.geomHom g' := by
    have hdown := B.downAut_eq_mul_geomAut δ (B.frobPathPow n) hd
    rw [B.downAut_frobPathPow, BasePointData.downAut_ofLift B₀ ξ hξ σ n h₁ h₂ hd] at hdown
    apply Subtype.ext
    have e₁ := B.weilGroupEquiv_frobLift
    have e₂ := B.weilGroupEquiv_geomHom g'
    change (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (n : ℤ)) =
      ((B.frobLift : _ × _) ^ n * (B.geomHom g' : _ × _))
    rw [show (B.frobLift : GU × Multiplicative ℤ) = (B.frobAut, Multiplicative.ofAdd 1) from e₁,
      show (B.geomHom g' : GU × Multiplicative ℤ) = (B.geomAut g', 1) from e₂]
    ext
    · exact hdown
    · simp only [Prod.pow_mk, Prod.mk_mul_mk, mul_one]
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  rw [hwB, map_mul, map_pow, Module.End.mul_apply, fundamentalRep_frobLift]
  have hgeo := fundamentalRep_geometric M B.weilMonodromyData F hF ⟨B.geomHom g', B.geomHom_mem g'⟩
  rw [show (B.weilMonodromyData.geomEquiv.symm ⟨B.geomHom g', B.geomHom_mem g'⟩) = g' from
    B.geomEquiv.symm_apply_eq.2 (Subtype.ext (B.geomEquiv_apply g').symm)] at hgeo
  change _ = _ at hgeo
  rw [show fundamentalRep M B.weilMonodromyData F hF (B.geomHom g') =
    LisseMonodromy.rep M B.t (F.toLisse hF) g' from hgeo]
  -- the transport along the square is `Ψ_n(δ)`
  have e := liftStalkIso_globalSectionsTransport B₀.t ξ hξ (Fr ^ n).hom _ ha h₁ h₂
    (F.toLisse hF) (F.frobeniusPowStr n)
  have hΨ : (LisseMonodromy.mono M δ).hom.app (F.toLisse hF) ≫
      (upperStarStalkIso l (Fr ^ n).hom B₀.t (F.toLisse hF).obj.X).hom ≫
      (stalkFunctor l B₀.t).map (F.frobeniusPowStr n) = frobPowStalk M B F hF n δ := by
    rw [frobPowStalk, ← WeilSheaf.lisseFrobPowStr_hom_hom]
    rfl
  rw [reassoc_of% hΨ, frobPowStalk_eq_mono_comp M F hF n δ (B.frobPathPow n)] at e
  have e' := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v) e
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e'
  rw [genericStalkEquiv_apply, genericStalkEquiv_apply, e', frobPowStalk_frobPathPow]
  rfl

end AlgebraicGeometry.WeilGroup
