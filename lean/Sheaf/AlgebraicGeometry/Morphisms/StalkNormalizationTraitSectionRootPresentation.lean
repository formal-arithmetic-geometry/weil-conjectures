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
# Root-algebra presentation along a transverse trait section

Source: Stacks Project, Tags 0EYH and 0EYI, proof preceding parts (1) and (2).
(blueprint: lem-sbc-stalk-normalization-trait-section-root-presentation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The geometric normal form, retaining the actual local root algebra and a uniformizer
of the auxiliary section trait. No maximal-ideal formula for the root algebra and no
integer-valued valuation are asserted here.

Source: Stacks Project, Tags 0EYH and 0EYI, proof preceding parts (1) and (2).
(blueprint: lem-sbc-stalk-normalization-trait-section-root-presentation)

Proof: Minimality of s makes the inverse image of U the punctured local trait.
The closed fibre of the smooth total space is a regular effective Cartier divisor.
At each of its generic points, the ramification and inseparable residue degrees of a
connected component divide the order of its stabilizer in G. The invertibility of
|G| therefore gives tame ramification. Apply 0EYH to obtain an affine etale chart
with the normalization a disjoint union of root algebras, with positive exponents
and a common equation f for the divisor. Normalization commutes with localization
and etale base change, so these are charts for the concrete normalization n.
Choose a point of this etale cover over x and its root factor, and localize the base
chart at its image. Call this local base ring R. The chosen root factor becomes
R[T]/(T^e-f). It is local: it is finite integral over R, and its reduction modulo
m_R is k(R)[T]/(T^e), which has exactly one prime. Thus this whole root algebra is
the stalk D at the chosen point. The stalk map beta from B is local and etale,
hence flat. The etale local base map extends the original base maximal ideal to
m_R; extending once more to D gives the displayed equality with J.map beta.
Pull the etale chart back along the section and localize at its closed point.
As in 0EYI this gives an unramified DVR A over the original trait. Transversality
makes f map to a uniformizer varpi of A. Let K be its fraction field and pi the
unit corresponding to varpi in K. The generic section fibre of the chart is a
disjoint union of Spec K[T]/(T^e_i-pi). The chosen factor is open, and the generic
normalization identifies its inclusion with g into the base change of Z. All
identifications preserve the structural map to Spec K. A uniformizer is
irreducible. Empty fibres have no x; no rational-point assumption is used. -/
theorem GaloisCover.stalk_normalization_trait_section_root_presentation {S C : Scheme.{u}}
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
        ∃ (_ : IsLocalRing D) (β : B →+* D),
          IsLocalHom β ∧ β.Flat ∧ IsLocalHom (AdjoinRoot.of p) ∧
          J.map β = (IsLocalRing.maximalIdeal R).map (AdjoinRoot.of p) ∧
          ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
            (ϖ : A) (π : Kˣ) (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField),
            Irreducible ϖ ∧ (π : K) = algebraMap A K ϖ ∧
            ∃ g : Spec (CommRingCat.of
                (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e - Polynomial.C (π : K)))) ⟶
                pullback Z.π (b ≫ sη),
              IsOpenImmersion g ∧
              g ≫ pullback.snd Z.π (b ≫ sη) =
                Spec.map (CommRingCat.ofHom (algebraMap K
                  (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e -
                    Polynomial.C (π : K))))) := by sorry

end AlgebraicGeometry.Scheme
