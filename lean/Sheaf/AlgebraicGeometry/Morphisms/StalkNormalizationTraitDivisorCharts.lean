/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

public import Mathlib.RingTheory.AdjoinRoot

/-! Tame charts with the trait divisor equation. 
Source: Stacks Project, Tags 0EYH, 0EYI and 0EYJ.
(blueprint: lem-sbc-stalk-normalization-trait-divisor-charts)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A tame affine chart using the pullback of an actual trait uniformizer.

Source: Stacks Project, Tags 0EYJ (trait reduction), 0EYG and 0EYH.
(blueprint: lem-sbc-stalk-normalization-trait-divisor-charts)

Proof: Minimality of s outside U identifies the local generic restriction with the
punctured trait. Choose a uniformizer of its DVR. Its pullback cuts out the closed
fibre of the smooth total space and is a nonzerodivisor with regular quotient.
The stabilizer of each connected torsor component has order dividing the invertible
order of G. The ramification and inseparable residue degrees divide that order, so
the cover is tame along the closed fibre. Apply 0EYG with this particular divisor
equation, then 0EYH. If a chart initially uses a unit multiple of the equation,
adjoin the required roots of the unit etale locally (the exponents are invertible)
and rescale the roots. This gives the same equation rho(varpi) in every factor.
Normalization commutes with trait localization and etale base change, identifying
these charts with the concrete n. Choose a chart over n(x), enumerate its factors
by Fin m, and retain the structural equality over the chart. Since n(x) is on the
closed fibre, rho(varpi) belongs to the prime y. No stalk localization or generic
section factor is constructed in this theorem. Empty normalizations have no x. -/
theorem GaloisCover.stalk_normalization_trait_divisor_charts {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∀ x : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a) : Scheme.{u}),
      n x = τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) →
      ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ pullback c a) (y : Spec R)
        (ρ : S.presheaf.stalk s →+* R) (ϖ : S.presheaf.stalk s),
        Etale φ ∧ φ y = n x ∧
        IsLocalRing.maximalIdeal (S.presheaf.stalk s) = Ideal.span {ϖ} ∧
        φ ≫ pullback.snd c a = Spec.map (CommRingCat.ofHom ρ) ∧
        ρ ϖ ∈ y.asIdeal ∧
        ∃ (m : ℕ) (e : Fin m → ℕ), (∀ k, 0 < e k) ∧
          ∃ α : pullback n φ ≅ Spec (CommRingCat.of (∀ k : Fin m,
              AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ)))),
            α.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap R (∀ k : Fin m,
                AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ))))) =
              pullback.snd n φ := by sorry

end AlgebraicGeometry.Scheme
