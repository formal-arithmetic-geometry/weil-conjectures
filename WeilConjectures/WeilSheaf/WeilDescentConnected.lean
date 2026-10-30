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

Let `X₀` be a smooth, affine, irreducible, geometrically connected scheme over the finite field
`K`.
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

- `WeilSheaf.IsIrreducibleLisse.exists_iso_constantTwist_of_geometricallyConnected`
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale Representation

variable {K : Type u} [Field K] [Finite K] {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (.of K))]

namespace FrobeniusBasePoint.WeilData

/-- `AlgebraicGeometry.FrobeniusBasePoint.WeilData.fundamentalRep_constantTwist`, with an
independent proof that the twist is lisse. -/
lemma fundamentalRep_constantTwist' {B : FrobeniusBasePoint K X} {W : Type*} [Group W]
    (D : B.WeilData W) (M : LisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K)
    (F : WeilSheaf K l X) (hF : F.IsLisse) (b : (PadicAlgCl l)ˣ) (hF' : (F.constantTwist b).IsLisse)
    (w : W) (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    D.fundamentalRep M (F.constantTwist b) hF' w v =
      (D.fundamentalRep M F hF).twist (degreeCharacter D.deg b) w v :=
  D.fundamentalRep_constantTwist M F hF b w v

end FrobeniusBasePoint.WeilData

namespace WeilSheaf

/-- **Irreducible lisse Weil sheaves come from the model up to twist**, for `X₀` smooth, affine,
irreducible and geometrically connected over `K` (Deligne, Weil II, 1.3.14): every irreducible
lisse Weil sheaf `G` on `X₀` is isomorphic to a constant twist `π^* H ⊗ 𝓑_b` of the pullback of
a lisse `ℓ`-adic sheaf `H` on `X₀`, with its canonical Weil structure. -/
theorem IsIrreducibleLisse.exists_iso_constantTwist_of_geometricallyConnected
    [Smooth (X ↘ Spec (.of K))] [GeometricallyConnected (X ↘ Spec (.of K))] [IsAffine X]
    [IrreducibleSpace X] {G : WeilSheaf K l X} (hG : G.IsIrreducibleLisse) :
    ∃ (H : AdicSheaf l X) (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ),
      Nonempty (G ≅ (geometricFiberPullback (k₀ := K) hH).constantTwist b) := by
  -- the geometric fibre and `X₀` are connected regular Noetherian schemes
  have : ConnectedSpace (X ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := X ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (X ↘ Spec (.of K)).geometricFiberProj
      (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  have := IsRegular.of_smooth (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : QuasiCompact (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure := by
    unfold Scheme.Hom.geometricFiberToAlgebraicClosure Scheme.Hom.geometricFiber
    infer_instance
  have : CompactSpace (X ↘ Spec (.of K)).geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace
      (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  -- base point data at a `K̄`-rational point
  obtain ⟨t, ht⟩ :=
    (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure.exists_comp_eq_id_of_isAlgClosed
  obtain ⟨B, rfl⟩ : ∃ B : FrobeniusBasePoint K X, B.t = t :=
    ⟨⟨t, (PreGaloisCategory.nonempty_iso_of_fiberFunctor _ _).some⟩, rfl⟩
  -- compatible monodromies on `X₀` and on its geometric fibre, equivalences at the base points
  have hc : LisseMonodromy.IsCompatible (X ↘ Spec (.of K)).geometricFiberProj
      (universalLisseMonodromy l X K)
      (universalLisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K) :=
    isCompatible_universalLisseMonodromy l K _
  have hM := universalLisseMonodromy_isEquivalenceAt l (X ↘ Spec (.of K)).geometricFiber K B.t
  have hM₀ := universalLisseMonodromy_isEquivalenceAt l X K
    (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
  generalize universalLisseMonodromy l (X ↘ Spec (.of K)).geometricFiber K = M at hc hM
  generalize universalLisseMonodromy l X K = M₀ at hc hM₀
  -- Weil II 1.3.14: a twist `σ` of the Weil fundamental representation is bounded
  obtain ⟨b, hb⟩ := B.weilData.exists_isBoundedOn_twist_fundamentalRep M hM hG
  have : FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (G.toLisse hG.1)) :=
    G.finiteDimensional_stalkObj B.t
  have hσ : ((B.weilData.fundamentalRep M G hG.1).twist
      (degreeCharacter B.weilData.deg b⁻¹)).IsContinuousOn
        (SemidirectProduct.inl (φ := B.frobAction)) := fun φ v ↦ by
    have h (g : Aut (fiber B.t)) : (B.weilData.fundamentalRep M G hG.1).twist
        (degreeCharacter B.weilData.deg b⁻¹) (SemidirectProduct.inl g) v =
          M.rep B.t (G.toLisse hG.1) g v := by
      rw [twist_apply, degreeCharacter_apply, B.weilData_fundamentalRep_inl M G hG.1 g]
      erw [SemidirectProduct.rightHom_inl]
      rw [toAdd_one, zpow_zero, Units.val_one, one_smul]
    simp_rw [h]
    exact hM.continuous_rep _ φ v
  -- `σ` extends to a continuous representation `τ` of `π₁(X₀, t ≫ π)`
  obtain ⟨τ, hτ, hτc⟩ := exists_extension_of_isBoundedOn (ℓ := l) (deg := B.weilData.deg)
    (γ := B.weilData.frobLift) B.weilData.deg_frobLift SemidirectProduct.inl (fun w hw ↦ by
      obtain ⟨g, hg⟩ := SemidirectProduct.range_inl_eq_ker_rightHom.ge hw
      exact ⟨g, hg⟩) B.toArith (B.denseRange_toArith ht) B.continuous_toArith_inl
    B.injective_toArith_inl (B.exists_nhds_forall_dvd_deg ht) _ hσ hb
  -- `τ` is the monodromy representation of a lisse sheaf `H` on `X₀`
  obtain ⟨H, e, he⟩ := hM₀.essSurj _ τ hτc
  refine ⟨H.obj, H.property, b, ?_⟩
  -- the Weil fundamental representation of `π^* H ⊗ 𝓑_b` is that of `G`
  refine B.weilData.nonempty_iso_of_linearEquiv M hM hG.1
    (isLisse_geometricFiberPullback H.property).constantTwist
    (e.symm.trans (LisseMonodromy.upperStarStalkLinearEquiv
      (X ↘ Spec (.of K)).geometricFiberProj B.t H)) fun w v ↦ ?_
  have h₁ : M₀.rep (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) H (B.toArith w) (e.symm v) =
      e.symm (((B.weilData.fundamentalRep M G hG.1).twist
        (degreeCharacter B.weilData.deg b⁻¹)) w v) := by
    rw [LinearEquiv.eq_symm_apply, he, LinearEquiv.apply_symm_apply, hτ]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    B.weilData.fundamentalRep_constantTwist' M _ (isLisse_geometricFiberPullback H.property),
    twist_apply, LinearMap.smul_apply]
  erw [← B.fundamentalRep_geometricFiberPullback M₀ M hc H w (e.symm v)]
  rw [h₁, twist_apply, LinearMap.smul_apply, map_smul, map_smul, degreeCharacter_apply,
    degreeCharacter_apply, smul_smul, ← Units.val_mul, ← mul_zpow, mul_inv_cancel, one_zpow,
    Units.val_one, one_smul]
  rfl

end WeilSheaf

end AlgebraicGeometry
