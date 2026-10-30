/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.WeilGroupProfiniteExtension
public import WeilConjectures.WeilSheaf.WeilDescentFundamentalRep

/-!
# Descent of irreducible lisse Weil sheaves: the geometrically connected case

Let `X₀` be a smooth geometrically connected scheme of finite type over the finite field `K`.
Every irreducible lisse Weil sheaf `G` on `X₀` is, up to a constant twist, the pullback `π^* H` of
a lisse `ℓ`-adic sheaf `H` on `X₀` with its canonical Weil structure (Deligne, Weil II, 1.3.14):

1. by Weil II 1.3.14 some twist `σ = ρ_G ⊗ b^{-deg}` of the Weil fundamental representation of `G`
   is bounded on the Weil group `W = π₁(X, t) ⋊ ℤ`
   (`AlgebraicGeometry.FrobeniusBasePoint.WeilData.exists_isBoundedOn_twist_fundamentalRep`);
2. the image of `W` in `π₁(X₀, t ≫ π)` is dense and the degree is continuous for the
   profinite topology (`WeilConjectures.WeilSheaf.WeilDescentFundamentalGroup`), so `σ` extends to a
   continuous representation `τ` of `π₁(X₀, t ≫ π)`
   (`Representation.exists_extension_of_isBoundedOn`);
3. `τ` is the monodromy representation of a lisse sheaf `H` on `X₀`
   (`AlgebraicGeometry.ProEtale.universalLisseMonodromy_isEquivalenceAt`), and the Weil
   fundamental representation of `π^* H` is `τ ∘ toArith = σ`
   (`AlgebraicGeometry.FrobeniusBasePoint.fundamentalRep_geometricFiberPullback`); hence that of
   `π^* H ⊗ 𝓑_b` is `ρ_G`, and the two lisse Weil sheaves are isomorphic
   (`AlgebraicGeometry.FrobeniusBasePoint.WeilData.exists_stalkMap_eq`).

## Main results

- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback_of_geometricallyConnected`.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale Representation

variable {K : Type u} [Field K] [Finite K] {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (.of K))]

namespace FrobeniusBasePoint

/-- **Lisse Weil sheaves with the same Weil fundamental representation are isomorphic**: a
linear isomorphism of stalks intertwining the Weil fundamental representations is the stalk of an
isomorphism of Weil sheaves. -/
theorem WeilData.nonempty_iso_of_linearEquiv {B : FrobeniusBasePoint K X} {W : Type*} [Group W]
    (D : B.WeilData W) (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K)
    (hM : M.IsEquivalenceAt B.t) {F G : WeilSheaf K l X} (hF : F.IsLisse) (hG : G.IsLisse)
    (e : LisseMonodromy.StalkSpace B.t (F.toLisse hF) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (G.toLisse hG))
    (he : ∀ w v, e (D.fundamentalRep M F hF w v) = D.fundamentalRep M G hG w (e v)) :
    Nonempty (F ≅ G) := by
  obtain ⟨f, hf⟩ := D.exists_stalkMap_eq M hM (F := ⟨F, hF⟩) (G := ⟨G, hG⟩) e.toLinearMap he
  obtain ⟨g, hg⟩ := D.exists_stalkMap_eq M hM (F := ⟨G, hG⟩) (G := ⟨F, hF⟩) e.symm.toLinearMap
    fun w v ↦ by
      apply e.injective
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, he]
  have h₁ : f ≫ g = 𝟙 _ := stalkMap_injective M B hM _ _ (by
    rw [ObjectProperty.FullSubcategory.comp_hom, stalkMap_comp _ _ _ hF hG hF, hf, hg]
    erw [stalkMap_id]
    exact LinearMap.ext fun v ↦ e.symm_apply_apply v)
  have h₂ : g ≫ f = 𝟙 _ := stalkMap_injective M B hM _ _ (by
    rw [ObjectProperty.FullSubcategory.comp_hom, stalkMap_comp _ _ _ hG hF hG, hf, hg]
    erw [stalkMap_id]
    exact LinearMap.ext fun v ↦ e.apply_symm_apply v)
  exact ⟨⟨f.hom, g.hom, congrArg (·.hom) h₁, congrArg (·.hom) h₂⟩⟩

end FrobeniusBasePoint

namespace WeilSheaf

/-- **Irreducible lisse Weil sheaves come from the model up to twist**, for `X₀` smooth,
geometrically connected and of finite type over `K` (Deligne, Weil II, 1.3.14): every irreducible
lisse Weil sheaf `G` on `X₀` is isomorphic to a constant twist `π^* H ⊗ 𝓑_b` of the pullback of a
lisse `ℓ`-adic sheaf `H` on `X₀`, with its canonical Weil structure. -/
theorem IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback_of_geometricallyConnected
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [Smooth (X ↘ Spec (.of K))] [GeometricallyConnected (X ↘ Spec (.of K))] [Nonempty X]
    {G : WeilSheaf K l X} (hG : G.IsIrreducibleLisse) :
    ∃ (H : AdicSheaf l X) (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ),
      Nonempty (G ≅ (geometricFiberPullback (k₀ := K) hH).constantTwist b) := by
  set π := (X ↘ Spec (.of K)).geometricFiberProj
  -- the geometric fibre and `X₀` are connected regular Noetherian schemes
  have : ConnectedSpace (X ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := X ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (X ↘ Spec (.of K)).geometricFiberProj
      (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  have := IsRegular.of_smooth (X ↘ Spec (.of K))
  have : CompactSpace (X ↘ Spec (.of K)).geometricFiber := sorry
  have : IsLocallyNoetherian X := sorry
  have : CompactSpace X := sorry
  have : QuasiSeparatedSpace X := sorry
  have : ConnectedSpace X := sorry
  -- compatible monodromies on `X₀` and on its geometric fibre
  set M₀ := universalLisseMonodromy l X K
  set M := universalLisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K
  have hc : LisseMonodromy.IsCompatible π M₀ M := isCompatible_universalLisseMonodromy l K π
  -- base point data at a `K̄`-rational point
  obtain ⟨t, ht⟩ := (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure.exists_comp_eq_id_of_isAlgClosed
  obtain ⟨B, rfl⟩ : ∃ B : FrobeniusBasePoint K X, B.t = t :=
    ⟨⟨t, (PreGaloisCategory.nonempty_iso_of_fiberFunctor _ _).some⟩, rfl⟩
  have hM : M.IsEquivalenceAt B.t := universalLisseMonodromy_isEquivalenceAt l _ K B.t
  have hM₀ : M₀.IsEquivalenceAt (B.t ≫ π) := universalLisseMonodromy_isEquivalenceAt l X K _
  set D := B.weilData
  -- Weil II 1.3.14: a twist `σ` of the Weil fundamental representation is bounded
  obtain ⟨b, hb⟩ := D.exists_isBoundedOn_twist_fundamentalRep M hM hG
  set V := LisseMonodromy.StalkSpace B.t (G.toLisse hG.1)
  have : FiniteDimensional (PadicAlgCl l) V := G.finiteDimensional_stalkObj B.t
  set σ := (D.fundamentalRep M G hG.1).twist (degreeCharacter D.deg b⁻¹)
  have hσ : σ.IsContinuousOn (SemidirectProduct.inl (φ := B.frobAction)) := by
    sorry
  -- `σ` extends to a continuous representation `τ` of `π₁(X₀, t ≫ π)`
  obtain ⟨τ, hτ, hτc⟩ := exists_extension_of_isBoundedOn (ℓ := l) (deg := D.deg)
    (γ := D.frobLift) D.deg_frobLift SemidirectProduct.inl
    (fun g ↦ SemidirectProduct.rightHom_inl g) (fun w hw ↦ by
      sorry) B.toArith (B.denseRange_toArith ht) B.continuous_toArith_inl
    B.injective_toArith_inl (B.exists_nhds_forall_dvd_deg ht) σ hσ hb
  -- `τ` is the monodromy representation of a lisse sheaf `H` on `X₀`
  obtain ⟨H, e, he⟩ := hM₀.essSurj V τ hτc
  refine ⟨H.obj, H.property, b, ?_⟩
  -- the Weil fundamental representation of `π^* H ⊗ 𝓑_b` is that of `G`
  refine D.nonempty_iso_of_linearEquiv M hM hG.1
    (isLisse_geometricFiberPullback H.property).constantTwist
    (e.symm.trans (LisseMonodromy.upperStarStalkLinearEquiv π B.t H)) fun w v ↦ ?_
  sorry

end WeilSheaf

end AlgebraicGeometry
