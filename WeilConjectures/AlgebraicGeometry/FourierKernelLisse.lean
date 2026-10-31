/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.Perverse
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTraceComparison
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover

/-! # The Fourier kernel is lisse of rank one

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-thm-inversion/
prop-kernel-lisse.md (blueprint: prop-kernel-lisse).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.Etale.DerivedCategory AlgebraicGeometry.ProEtale

/-- The Fourier kernel is lisse of rank one, of Tor amplitude `[0, 0]`, multiplicative in
the character, with tensor inverse the kernel of the inverse character. The four branches
are the finite small-etale kernel, the degree-`q` small-etale Artin--Schreier model, the
admissible condensed prime-field kernel and the degree-`q` condensed model.

Source: current blueprint, sec-fourier-transform/sk-thm-inversion/prop-kernel-lisse.md,
all clauses (blueprint: prop-kernel-lisse).

Proof.
1. Let `G = (F_p, +)` (resp. `(k, +)`, `d = |G|`) and `q : Y → W` the Artin--Schreier torsor
   `T^d - T = b`, the base change of `AS : 𝔸¹ → 𝔸¹` along `b` (lem-fd-as-cover,
   lem-wft-finite-field-as-map). The finite etale exchange for this Cartesian square
   (lem-a1-finite-etale-condensed-base-change) identifies `b^* AS_* Λ` with `q_* Λ_Y`,
   compatibly with the translations `σ_a`; module pullback is exact
   (det-prop-sfb-module-pullback-exact-main), so `b^* ℒ_Ψ` is the image of
   `e_Ψ = d⁻¹ ∑_a Ψ(-a) σ_a^*` in `q_* Λ_Y`. Since `Y ×_W Y ≅ ∐_{a ∈ G} Y`, the same
   exchange identifies `q^* q_* Λ_Y` with `R^G`, translations permuting the factors; on the
   small etale site this is the direct computation `(q_* Λ)(U) = Λ(U)^G`.
2. On this chart the image of `e_Ψ` is the set of `h` with `h(a + c) = Ψ(c) h(a)`, and
   evaluation at `0` is an isomorphism onto `R` with inverse `r ↦ (a ↦ Ψ(a) r)`. So the
   kernel is locally isomorphic to the coefficient module on the single cover `{q}`
   (lem-fd-as-lisse); no nontriviality of `Ψ` is needed.
3. `q_* Λ_Y` is an algebra (def-sfb-finite-lower-star-lax-monoidal) and each `σ_a^*` an
   algebra automorphism, so multiplying eigensections gives
   `μ : 𝒦_Ψ ⊗ 𝒦_Ψ' → 𝒦_{ΨΨ'}` (def-pur-sheaf-tensor-product). On the chart it is
   `R ⊗_R R ≅ R`; `q^*` commutes with tensor products
   (def-sfb-condensed-pullback-tensor-comparison, resp.
   lem-sfb-localized-site-tensor-restriction), and joint conservativity along `{q}`
   (lem-zl-condensed-cover-restriction-conservative, resp.
   lem-sfb-sheaf-cover-local-isomorphism) makes `μ` an isomorphism. For `Ψ' = Ψ⁻¹` this is
   `𝒦_Ψ ⊗ 𝒦_{Ψ⁻¹} ≅ R`, the tensor inverse.
4. By step 3, `- ⊗ 𝒦_Ψ` is an equivalence with inverse `- ⊗ 𝒦_{Ψ⁻¹}`, hence exact, so
   `𝒦_Ψ` is flat (def-pc-flat-sheaf-modules). The flat-single comparison
   (lem-pur-flat-single-derived-normalization) gives `H^i(M[0] ⊗ᴸ 𝒦_Ψ[0]) = 0` for
   `i ≠ 0` and every module `M`: Tor amplitude `[0, 0]` (def-weil-finite-tor-amplitude). -/
theorem prop_kernel_lisse :
    (∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
      (p : ℕ) [Fact p.Prime] [Invertible (p : Λ)]
      {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
      [CharP Γ(pullback π π', ⊤) p] (Ψ Ψ' : AddChar (ZMod p) Λ)
      (b : Γ(pullback π π', ⊤)),
      IsLisse ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (fourierKernel Λ π π' Ψ b)) ∧
        Scheme.IsLisseRankOneSheaf (fourierKernel Λ π π' Ψ b) ∧
        Nonempty (fourierKernel Λ π π' Ψ b ⊗ fourierKernel Λ π π' Ψ' b ≅
          fourierKernel Λ π π' (Ψ * Ψ') b) ∧
        Nonempty (fourierKernel Λ π π' Ψ b ⊗ fourierKernel Λ π π' Ψ⁻¹ b ≅ 𝟙_ _) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) (pullback π π') 0 0
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ π π' Ψ b))) ∧
    (∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
      (k : Type u) [Field k] [Fintype k]
      [Invertible (Fintype.card k : Λ)]
      (X : Scheme.{u}) [X.Over (Spec (.of k))]
      (ψ ψ' : AddChar k Λ) (f : Γ(X, ⊤)),
      Scheme.IsLocallyConstantSheaf (artinSchreierSheafOf X ψ f) ∧
        Nonempty (artinSchreierSheafOf X ψ f ⊗ artinSchreierSheafOf X ψ' f ≅
          artinSchreierSheafOf X (ψ * ψ') f) ∧
        Nonempty (artinSchreierSheafOf X ψ f ⊗ artinSchreierSheafOf X ψ⁻¹ f ≅ 𝟙_ _)) ∧
    (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ]
      (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : MonObj.Γ Λ))
      (hΛ : ProEtale.CondensedRing.IsAdmissibleCoefficient Λ)
      (X : Scheme.{u}) [X.Over (Spec (.of (ULift.{u} (ZMod p))))]
      (Ψ Ψ' : AddChar (ZMod p) (MonObj.Γ Λ)) (b : Γ(X, ⊤)),
      IsLisseCoefficientModule Λ
          (condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
            (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b) ∧
        (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
          Nonempty ((ProEtale.CondensedRing.upperStar Λ (U.f i)).obj
            (condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b) ≅
              Mod.regular (ProEtale.condensedRingObj Λ (U.X i)))) ∧
        Nonempty (
          condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b ⊗
            condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ'.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b ≅
          condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
            ((Ψ * Ψ').compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b) ∧
        Nonempty (
          condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b ⊗
            condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              ((Ψ⁻¹).compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b ≅
          Mod.regular (ProEtale.condensedRingObj Λ X)) ∧
        _root_.DerivedCategory.torAmplitudeIn
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (ProEtale.condensedRingObj Λ X)) 0 0
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (condensedArtinSchreierSheafOf Λ (ULift.{u} (ZMod p)) X
              (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b))) ∧
    (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ]
      (k : Type u) [Field k] [Fintype k]
      (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
      (hΛ : ProEtale.CondensedRing.IsAdmissibleCoefficient Λ)
      (X : Scheme.{u}) [X.Over (Spec (.of k))]
      (ψ ψ' : AddChar k (MonObj.Γ Λ)) (f : Γ(X, ⊤)),
      IsLisseCoefficientModule Λ (condensedArtinSchreierSheafOf Λ k X ψ f) ∧
        (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
          Nonempty ((ProEtale.CondensedRing.upperStar Λ (U.f i)).obj
            (condensedArtinSchreierSheafOf Λ k X ψ f) ≅
              Mod.regular (ProEtale.condensedRingObj Λ (U.X i)))) ∧
        Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
            condensedArtinSchreierSheafOf Λ k X ψ' f ≅
          condensedArtinSchreierSheafOf Λ k X (ψ * ψ') f) ∧
        Nonempty (condensedArtinSchreierSheafOf Λ k X ψ f ⊗
            condensedArtinSchreierSheafOf Λ k X ψ⁻¹ f ≅
          Mod.regular (ProEtale.condensedRingObj Λ X)) ∧
        _root_.DerivedCategory.torAmplitudeIn
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (ProEtale.condensedRingObj Λ X)) 0 0
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (condensedArtinSchreierSheafOf Λ k X ψ f))) := by
  sorry

end AlgebraicGeometry.Etale
