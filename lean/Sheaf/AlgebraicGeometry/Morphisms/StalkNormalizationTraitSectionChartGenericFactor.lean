/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
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

public import Mathlib.RingTheory.RingHom.Flat

public import Mathlib.RingTheory.AdjoinRoot

/-!
# Tame local chart and its generic section factor

Source: Stacks Project, Tags 0EYH and 0EYI(2).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The tame local chart, before using splitting of the generic section fibre.

Source: Stacks Project, Tag 0EYH, and the transverse section construction in 0EYI(2).
(blueprint: lem-sbc-stalk-normalization-trait-section-chart-generic-factor)

Proof: Minimality of s makes the inverse image of U in the local trait its punctured
spectrum. Smoothness makes the closed fibre a regular effective Cartier divisor.
Since the group order is invertible, the generic torsor is tame at its codimension-one
points. The tame normal form of 0EYH gives, after an etale base change, factors
R[T]/(T^e-f) with e positive and f the divisor equation. Compatibility of integral
closure with localization and etale base change identifies these charts with the
concrete normalization in the statement. Select a factor and point above x, localize,
and call the resulting ring D. Its map beta from the normalization stalk is local
and etale, hence flat. Modulo the maximal ideal of the base the factor is a localization
of a residue field[T]/(T^e), so its maximal ideal is JD+(t) and t^e belongs to JD.
Pull the chart back to the section and localize over the closed point. The section
ring is an unramified trait extension. Its fraction field K has normalized integer
valuation, and transversality makes the image pi of f a uniformizer. Its generic
section factor is Spec K[T]/(T^e-pi), an open factor of the base changed section fibre
of Z. This gives b, g and the displayed structural-map identity. No rational point
of the generic section fibre is used in this construction. -/
theorem GaloisCover.stalk_normalization_trait_section_chart_generic_factor {S C : Scheme.{u}}
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
      let B := (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c a)).presheaf.stalk x
      let J := (IsLocalRing.maximalIdeal ((pullback c a).presheaf.stalk (n x))).map
        (n.stalkMap x).hom
      ∃ (D : CommRingCat.{u}) (_ : IsLocalRing D) (β : B →+* D),
        IsLocalHom β ∧ β.Flat ∧
        ∃ (t : D) (e : ℕ) (K : Type u) (_ : Field K)
          (ord : Kˣ →* Multiplicative ℤ) (π : Kˣ)
          (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField),
          0 < e ∧
          IsLocalRing.maximalIdeal D = J.map β ⊔ Ideal.span {t} ∧
          t ^ e ∈ J.map β ∧ ord π = Multiplicative.ofAdd 1 ∧
          ∃ g : Spec (CommRingCat.of
              (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e - Polynomial.C (π : K)))) ⟶
              pullback Z.π (b ≫ sη),
            IsOpenImmersion g ∧
            g ≫ pullback.snd Z.π (b ≫ sη) =
              Spec.map (CommRingCat.ofHom (algebraMap K
                (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e -
                  Polynomial.C (π : K))))) := by sorry

end AlgebraicGeometry.Scheme
