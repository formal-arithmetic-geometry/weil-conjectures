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

public import Mathlib.RingTheory.RingHom.Flat

public import Mathlib.RingTheory.AdjoinRoot

public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts
import Sheaf.AlgebraicGeometry.Morphisms.RootProductChartStalkLocalization
import Sheaf.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor

/-!
# Localized tame root chart and its transverse generic factor

Source: Stacks Project, Tags 0EYH and 0EYI, proof before parts (1) and (2).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The geometric chart construction, retaining the localization at the chosen root point.
It does not identify that localization with the whole root algebra or assert that the
canonical map into the whole root algebra is local.

Source: Stacks Project, Tags 0EYH and 0EYI, proof before parts (1) and (2),
and Tag 0EYJ, the trait reduction.
(blueprint: lem-sbc-stalk-normalization-trait-section-localized-root-chart)

Proof: The points of the local trait map to generalizations of s. Minimality of s
outside U makes the inverse image of U its generic point. Smoothness gives a regular
effective Cartier closed fibre. For each connected torsor component the ramification
indices and inseparable residue degrees divide its stabilizer order, hence the
invertible order of G. Thus the generic cover is tame. Apply 0EYH to an affine etale
neighborhood of the image of x, with a common equation f for that closed fibre and
positive root exponents. Normalization commutes with localization and etale base
change, so the chart describes the concrete pullback of the normalization in the
statement. Choose a point above x and its root factor. Localize the base chart at
its image to obtain the local ring R, with f in its maximal ideal. The root point
lies over this closed base point; since the root algebra is finite integral over R,
its prime P is maximal. Its local ring is E = D_P. The etale chart induces a local
flat stalk map beta from B to E. The etale map on base stalks extends the original
base maximal ideal to the maximal ideal of R, giving the displayed ideal equality
in E. No identification of E with D is made here.

Pull the same affine neighborhood back to the trait section and localize at a
point above its closed point with the chosen image in the chart. This local ring
A is an unramified DVR extension. Because the section pulls the closed fibre back
to the reduced closed point, f maps to a generator varpi of its maximal ideal.
Take its fraction field K and the unit pi given by the nonzero image of varpi.
The generic section fibre of the root chart is a finite disjoint union of
Spec K[T]/(T^e_i-pi). The chosen factor is open. Compatibility of normalization
with the generic restriction identifies this inclusion with g into the pullback
of Z, and preserves the projection to Spec K. This construction precedes, and
uses neither, the rational-point and splitting hypotheses in 0EYI(1) and (2).
Empty covers have no x, and exponents are positive; no degenerate root polynomial
is used. All witnesses occur only in this theorem's existential conclusion. -/
theorem GaloisCover.stalk_normalization_trait_section_localized_root_chart {S C : Scheme.{u}}
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
      ∃ (R : CommRingCat.{u}) (_ : IsLocalRing R) (f : R) (e : ℕ),
        0 < e ∧ f ∈ IsLocalRing.maximalIdeal R ∧
        let p := (Polynomial.X : Polynomial R) ^ e - Polynomial.C f
        let D := AdjoinRoot p
        ∃ (P : Ideal D) (hP : P.IsMaximal),
          letI : P.IsPrime := hP.isPrime
          let E := Localization.AtPrime P
          ∃ (β : B →+* E), IsLocalHom β ∧ β.Flat ∧
          J.map β = (IsLocalRing.maximalIdeal R).map
            ((algebraMap D E).comp (AdjoinRoot.of p)) ∧
          ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
            (ϖ : A) (π : Kˣ) (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField),
            IsLocalRing.maximalIdeal A = Ideal.span {ϖ} ∧ (π : K) = algebraMap A K ϖ ∧
            ∃ g : Spec (CommRingCat.of
                (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e - Polynomial.C (π : K)))) ⟶
                pullback Z.π (b ≫ sη),
              IsOpenImmersion g ∧
              g ≫ pullback.snd Z.π (b ≫ sη) =
                Spec.map (CommRingCat.ofHom (algebraMap K
                  (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e -
                    Polynomial.C (π : K))))) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro hn x hx
  have hchart := GaloisCover.stalk_normalization_trait_divisor_charts
      (S := S) (C := C) (Cη := Cη)
      hS c σ hσ G hG q j hCη sη hsq hsj Z U hηU jU PA ψ hjU hψ
      s hs hmin hdvr
  dsimp only at hchart
  have hchartn := hchart hn
  have hchartx := hchartn x
  have hcharth := hchartx hx
  obtain ⟨R, φ, y, ρ, ϖ₀, hdata⟩ := hcharth
  obtain ⟨hφ, hy, hϖ₀, hρ, hf, m, e, he, α, hα⟩ := hdata
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
    (pullback.fst c (S.fromSpecStalk s))
  have hlocal := rootProductChart_stalk_localization n R φ y hφ x hy
    (ρ ϖ₀) hf m e he α hα
  dsimp only at hlocal
  obtain ⟨k, R₀, hR₀, f₀, hf₀, P, hP, β, hβ, hflat, hJ⟩ := hlocal
  have hgeneric := GaloisCover.trait_divisor_chart_section_generic_factor
    hS c σ hσ G hG q j hCη sη hsq hsj Z U hηU jU PA ψ hjU hψ
    s hs hmin hdvr hn x hx R φ y ρ ϖ₀ hφ hy hϖ₀ hρ m e he α hα k
  exact ⟨R₀, hR₀, f₀, e k, he k, hf₀, P, hP, β, hβ, hflat, hJ, hgeneric⟩


end AlgebraicGeometry.Scheme
