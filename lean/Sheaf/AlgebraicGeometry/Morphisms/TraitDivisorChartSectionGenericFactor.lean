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

/-! Generic section factors of a supplied trait-divisor chart. 
Source: Stacks Project, Tags 0EYH, 0EYI and 0EYJ.
(blueprint: lem-sbc-trait-divisor-chart-section-generic-factor)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Each supplied trait-divisor root factor restricts along the section to a
root of a uniformizer over an unramified trait extension.

Source: Stacks Project, Tag 0EYI, preliminary paragraph before parts (1) and (2),
and Tag 0EYJ, the local trait reduction.
(blueprint: lem-sbc-trait-divisor-chart-section-generic-factor)

Proof: Pull phi back along the trait section tau. The point y lies above its closed
point, so the pullback has a point above y and that closed point (take a common
extension of their residue fields). Its local ring A is an unramified DVR extension
of the base trait. The structural equality for phi identifies rho(varpi0) in A
with the image varpi of the base uniformizer. Unramifiedness gives m_A=(varpi).
Take the fraction field K and its nonzero uniformizer image as the unit pi. The
generic morphism Spec K to S factors through its generic point and gives b.
Base change alpha along Spec K: polynomial quotients and finite products commute
with field extension, so each factor is Spec K[T]/(T^(e k)-pi). A factor inclusion
is an open immersion. The generic restriction of the concrete relative normalization
is the original Z, since the finite etale cover is normal over the smooth generic
fibre and normalization commutes with the relevant localization. The pullback squares
hCeta and hpsi and the section equality hsj identify this generic restriction over
Spec K with pullback Z.pi (b composed with seta). Compose the kth factor inclusion
with that isomorphism; both preserve the projection to Spec K, which is precisely
the displayed structural equality. This needs no rational point or splitting.
A zero factor index set has no k; positive exponents exclude constant root polynomials. -/
theorem GaloisCover.trait_divisor_chart_section_generic_factor {S C : Scheme.{u}}
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
      ∀ (R : CommRingCat.{u}) (φ : Spec R ⟶ pullback c a) (y : Spec R)
        (ρ : S.presheaf.stalk s →+* R) (ϖ₀ : S.presheaf.stalk s),
        Etale φ → φ y = n x →
        IsLocalRing.maximalIdeal (S.presheaf.stalk s) = Ideal.span {ϖ₀} →
        φ ≫ pullback.snd c a = Spec.map (CommRingCat.ofHom ρ) →
        ∀ (m : ℕ) (e : Fin m → ℕ), (∀ k, 0 < e k) →
          ∀ α : pullback n φ ≅ Spec (CommRingCat.of (∀ k : Fin m,
              AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ₀)))),
            α.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap R (∀ k : Fin m,
                AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ₀))))) =
              pullback.snd n φ → ∀ k : Fin m,
          ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
            (ϖ : A) (π : Kˣ) (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField),
            IsLocalRing.maximalIdeal A = Ideal.span {ϖ} ∧ (π : K) = algebraMap A K ϖ ∧
            ∃ g : Spec (CommRingCat.of
                (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e k - Polynomial.C (π : K)))) ⟶
                pullback Z.π (b ≫ sη),
              IsOpenImmersion g ∧
              g ≫ pullback.snd Z.π (b ≫ sη) =
                Spec.map (CommRingCat.ofHom (algebraMap K
                  (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e k -
                    Polynomial.C (π : K))))) := by sorry

end AlgebraicGeometry.Scheme
