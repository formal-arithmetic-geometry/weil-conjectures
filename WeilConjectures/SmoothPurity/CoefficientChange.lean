/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Adjunction

/-!

# Smooth purity under change of coefficients

Let `f : X ⟶ Y` be smooth of pure relative dimension `d`, and let `Λ → Λ'` be a change of
coefficient rings: reduction `𝒪_E → 𝒪_E/ℓ^n`, inverting `ℓ`, `𝒪_E → E`, or extension of the
coefficient field, `E → F` or `E → ℚ̄_ℓ`. Blueprint `det-sp-purity-coefficient-change` states
that the purity isomorphisms `γ_{f,Λ}` and the smooth traces `Tr_{f,Λ}` are carried to those over
`Λ'`. In each case the proof is the same *transposition argument*: given

* the coefficient change functors `Φ_X`, `Φ_Y` (`(-)_{Λ'} = - ⊗ᴸ_Λ Λ'`),
* an isomorphism `b : (Rf_{!,Λ} M)_{Λ'} ≅ Rf_{!,Λ'}(M_{Λ'})`,
* an isomorphism `v₀ : (Lf^* K(d)[2d])_{Λ'} ≅ Lf^*(K_{Λ'})(d)[2d]`, and
* the fact, proved in the other subsections (`det-sp-integral-adjunction-bijection`,
  `det-sp-rational-adjunction`, `det-sp-qbar-adjunction`, `det-sp-field-extension-towers`), that
  the counit of `Rf_{!,Λ'} ⊣ Lf^*(-)(d)[2d]` is the coefficient change of the counit over `Λ`,
  read through `b` and `v₀`,

the transpose `c(K) : (f^!_Λ K)_{Λ'} ⟶ f^!_{Λ'}(K_{Λ'})` of `ε_{f,Λ}(K)_{Λ'} ∘ b⁻¹` is an
isomorphism carrying `γ_{f,Λ}(K)_{Λ'}` to `γ_{f,Λ'}(K_{Λ'})`, and the traces correspond.

The argument is formal: it is `CategoryTheory.Adjunction.transpose_coefficientChange` for
arbitrary categories and adjunctions, and
`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityNatIso_coefficientChange` for the bounded
constructible categories of two `ℓ`-adic coefficient rings.

## Implementation notes

The coefficient change functors, the comparison `b` and the twist comparison `v₀` are arguments:
the derived extension of scalars of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.
ChangeOfCoefficients` is not known to preserve bounded constructible complexes, its comparison
with `Rf_!` is an isomorphism only when the one for proper pushforwards is, and its
compatibility with the derived tensor product (hence with the Tate twists) is not formalized.
The reduction to the finite levels `𝒪_E/ℓ^n` (clause (1) of the blueprint) needs, moreover, the
exceptional inverse image over the torsion rings in the pro-étale formalism, which is not
constructed; the abstract statement applies to it verbatim.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {CX : Type u₁} {CY : Type u₂} {DX : Type u₃} {DY : Type u₄} [Category.{v₁} CX]
  [Category.{v₂} CY] [Category.{v₃} DX] [Category.{v₄} DY]
  {F : CX ⥤ CY} {G H : CY ⥤ CX} {F' : DX ⥤ DY} {G' H' : DY ⥤ DX}
  (adjG : F ⊣ G) (adjH : F ⊣ H) (adjG' : F' ⊣ G') (adjH' : F' ⊣ H')
  (ΦX : CX ⥤ DX) (ΦY : CY ⥤ DY) (b : F ⋙ ΦY ≅ ΦX ⋙ F') (v₀ : H ⋙ ΦX ≅ ΦY ⋙ H')

/-- The coefficient comparison `c(K) : Φ_X(G K) ⟶ G'(Φ_Y K)` of two right adjoints `G`, `G'` of
`F`, `F'`, the comparison `c_J` of the blueprint: the `G'`-transpose of
`Φ_Y(ε^G_K) ∘ b⁻¹`. -/
noncomputable def coefficientComparison (K : CY) : ΦX.obj (G.obj K) ⟶ G'.obj (ΦY.obj K) :=
  adjG'.homEquiv _ _ (b.inv.app (G.obj K) ≫ ΦY.map (adjG.counit.app K))

/-- **The transposition argument** of blueprint `det-sp-purity-coefficient-change`. Let
`F ⊣ G`, `F ⊣ H` and `F' ⊣ G'`, `F' ⊣ H'` be two pairs of right adjoints, `γ : H ≅ G` and
`γ' : H' ≅ G'` the counit-compatible isomorphisms (`rightAdjointUniq`), and `Φ_X`, `Φ_Y`
functors with comparisons `b : F ⋙ Φ_Y ≅ Φ_X ⋙ F'` and `v₀ : H ⋙ Φ_X ≅ Φ_Y ⋙ H'`. If the counit
of `F' ⊣ H'` is the image of the counit of `F ⊣ H` (`hε`), then the coefficient comparison
`c(K)` (`coefficientComparison`) is an isomorphism with `c(K) ∘ Φ_X(γ_K) = γ'_{Φ K} ∘ v₀(K)`,
and the traces `Tr(K) = ε^G_K ∘ F(γ_K)` correspond:
`Φ_Y(Tr(K)) ∘ b⁻¹ = Tr'(Φ_Y K) ∘ F'(v₀(K))`. -/
theorem transpose_coefficientChange
    (hε : ∀ K : CY, b.inv.app (H.obj K) ≫ ΦY.map (adjH.counit.app K) =
      F'.map (v₀.hom.app K) ≫ adjH'.counit.app (ΦY.obj K)) (K : CY) :
    ΦX.map ((adjH.rightAdjointUniq adjG).hom.app K) ≫ coefficientComparison adjG adjG' ΦX ΦY b K =
        v₀.hom.app K ≫ (adjH'.rightAdjointUniq adjG').hom.app (ΦY.obj K) ∧
      IsIso (coefficientComparison adjG adjG' ΦX ΦY b K) ∧
      b.inv.app (H.obj K) ≫
          ΦY.map (F.map ((adjH.rightAdjointUniq adjG).hom.app K) ≫ adjG.counit.app K) =
        F'.map (v₀.hom.app K) ≫
          F'.map ((adjH'.rightAdjointUniq adjG').hom.app (ΦY.obj K)) ≫
            adjG'.counit.app (ΦY.obj K) := by
  have hγ : ΦX.map ((adjH.rightAdjointUniq adjG).hom.app K) ≫
      coefficientComparison adjG adjG' ΦX ΦY b K =
        v₀.hom.app K ≫ (adjH'.rightAdjointUniq adjG').hom.app (ΦY.obj K) := by
    apply (adjG'.homEquiv _ _).symm.injective
    have hb := b.inv.naturality ((adjH.rightAdjointUniq adjG).hom.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hb
    rw [homEquiv_naturality_left_symm, homEquiv_naturality_left_symm, coefficientComparison,
      Equiv.symm_apply_apply, homEquiv_counit, rightAdjointUniq_hom_app_counit,
      reassoc_of% hb, ← ΦY.map_comp, rightAdjointUniq_hom_app_counit, hε]
  refine ⟨hγ, ?_, ?_⟩
  · have : coefficientComparison adjG adjG' ΦX ΦY b K =
        inv (ΦX.map ((adjH.rightAdjointUniq adjG).hom.app K)) ≫ v₀.hom.app K ≫
          (adjH'.rightAdjointUniq adjG').hom.app (ΦY.obj K) := by
      rw [IsIso.eq_inv_comp, hγ]
    rw [this]
    infer_instance
  · rw [rightAdjointUniq_hom_app_counit, rightAdjointUniq_hom_app_counit, hε]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ]
  [IsCommMonObj Λ] [IsEllAdicFinitenessCoefficient ℓ Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [IsEllAdicFinitenessCoefficient ℓ Λ']
  (φ : Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ Λ) [IsMonHom φ]
  (φ' : Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ Λ') [IsMonHom φ']
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ)
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint]
  [(boundedConstructibleLowerStar Λ' ℓ (compactificationOverField f).overG).IsLeftAdjoint]
  [HasSmoothPurityAdjunction φ f d] [HasSmoothPurityAdjunction φ' f d]

/-- Blueprint `det-sp-purity-coefficient-change`: Purity and the smooth trace under change of
coefficients (`ℓ`-adic coefficients).

Let `f` be smooth of pure relative dimension `d`, `Λ`, `Λ'` two `ℓ`-adic coefficient rings, and
`Φ_X : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ'⟧`, `Φ_Y` a change of coefficients (inverting `ℓ`, `𝒪_E → E`, or
extending the coefficient field, `E → F`, `E → ℚ̄_ℓ`), with comparisons
`b : (Rf_{!,Λ} M)_{Λ'} ≅ Rf_{!,Λ'}(M_{Λ'})` and
`v₀ : (Lf^* K(d)[2d])_{Λ'} ≅ Lf^*(K_{Λ'})(d)[2d]`. Suppose that the counit of the purity
adjunction over `Λ'` is the coefficient change of the counit over `Λ`, read through `b` and `v₀`
(`hε`; for the three cases of the blueprint this is part of `det-sp-rational-adjunction`,
`det-sp-field-extension-towers` and `det-sp-qbar-adjunction`). Let
`c(K) : (Rf^!_Λ K)_{Λ'} ⟶ Rf^!_{Λ'}(K_{Λ'})` be the transpose of `ε_{f,Λ}(K)_{Λ'} ∘ b⁻¹`. Then
`c(K)` is an isomorphism,
`c(K) ∘ γ_{f,Λ}(K)_{Λ'} = γ_{f,Λ'}(K_{Λ'}) ∘ v₀`, and
`Tr_{f,Λ}(K)_{Λ'} ∘ b⁻¹ = Tr_{f,Λ'}(K_{Λ'}) ∘ Rf_{!,Λ'}(v₀)`, where `γ_f` is the purity
isomorphism `smoothPurityNatIso` and `Tr_f(K) = ε_f(K) ∘ Rf_!(γ_f(K))` the smooth trace. -/
theorem smoothPurityNatIso_coefficientChange
    (ΦX : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ'⟧) (ΦY : Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(Y.left)⟦Λ'⟧)
    (b : boundedConstructibleLowerShriek Λ ℓ f ⋙ ΦY ≅
      ΦX ⋙ boundedConstructibleLowerShriek Λ' ℓ f)
    (v₀ : boundedConstructibleTwistShiftPullback φ f d ⋙ ΦX ≅
      ΦY ⋙ boundedConstructibleTwistShiftPullback φ' f d)
    (hε : ∀ K : Dᵇc(Y.left)⟦Λ⟧,
      b.inv.app ((boundedConstructibleTwistShiftPullback φ f d).obj K) ≫
          ΦY.map ((smoothPurityAdjunction φ f d).counit.app K) =
        (boundedConstructibleLowerShriek Λ' ℓ f).map (v₀.hom.app K) ≫
          (smoothPurityAdjunction φ' f d).counit.app (ΦY.obj K))
    (K : Dᵇc(Y.left)⟦Λ⟧) :
    ΦX.map ((smoothPurityNatIso φ f d).hom.app K) ≫
        Adjunction.coefficientComparison (boundedConstructibleUpperShriekAdjunction Λ ℓ f)
          (boundedConstructibleUpperShriekAdjunction Λ' ℓ f) ΦX ΦY b K =
      v₀.hom.app K ≫ (smoothPurityNatIso φ' f d).hom.app (ΦY.obj K) ∧
    IsIso (Adjunction.coefficientComparison (boundedConstructibleUpperShriekAdjunction Λ ℓ f)
      (boundedConstructibleUpperShriekAdjunction Λ' ℓ f) ΦX ΦY b K) ∧
    b.inv.app ((boundedConstructibleTwistShiftPullback φ f d).obj K) ≫
        ΦY.map ((boundedConstructibleLowerShriek Λ ℓ f).map
            ((smoothPurityNatIso φ f d).hom.app K) ≫
          (boundedConstructibleUpperShriekAdjunction Λ ℓ f).counit.app K) =
      (boundedConstructibleLowerShriek Λ' ℓ f).map (v₀.hom.app K) ≫
        (boundedConstructibleLowerShriek Λ' ℓ f).map
            ((smoothPurityNatIso φ' f d).hom.app (ΦY.obj K)) ≫
          (boundedConstructibleUpperShriekAdjunction Λ' ℓ f).counit.app (ΦY.obj K) :=
  Adjunction.transpose_coefficientChange _ (smoothPurityAdjunction φ f d) _
    (smoothPurityAdjunction φ' f d) ΦX ΦY b v₀ hε K

end AlgebraicGeometry.ProEtale.CondensedRing
