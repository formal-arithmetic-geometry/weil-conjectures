/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
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

/-!
# Local algebra of tame trait normalization

Source: Stacks Project, Tag 0EYH.
(blueprint: lem-sbc-stalk-normalization-trait-section-residue-separable)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Residue extensions at points above the closed trait section are separable.

Source: Stacks Project, Tag 0EYH, the tame charts used in the trait paragraph of 0EYJ.
Proof: Minimality identifies the restriction of U to the trait with the punctured
trait. The closed fibre of the smooth base change is a regular effective Cartier
divisor. Invertibility of the group order gives tame ramification in codimension one,
including disconnected torsors by passing to stabilizers. Normalization commutes with
localization and etale base change. Thus 0EYH supplies etale charts in which the
normalization is a union of Spec B[T]/(T^e-f), with f an equation of that divisor and
e positive and invertible. At any point over f=0 one has T=0 in the residue field.
Consequently the residue extension in the displayed chart is the identity extension.
The etale maps introducing these charts induce finite separable residue extensions.
Separability descends to the original residue extension: an inseparable element would
remain inseparable after a separable field extension. This proves the claim without
using the rational-point splitting assumption. An empty section fibre is vacuous.
(blueprint: lem-sbc-stalk-normalization-trait-section-residue-separable) -/
theorem GaloisCover.stalk_normalization_trait_section_residue_separable {S C : Scheme.{u}}
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
      letI := (n.stalkMap x).hom.toAlgebra
      letI : IsLocalHom
          (algebraMap ((pullback c a).presheaf.stalk (n x))
            ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
              (pullback.fst c a)).presheaf.stalk x)) :=
        inferInstanceAs <| IsLocalHom (n.stalkMap x).hom
      Algebra.IsSeparable
        (IsLocalRing.ResidueField ((pullback c a).presheaf.stalk (n x)))
        (IsLocalRing.ResidueField
          ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
            (pullback.fst c a)).presheaf.stalk x)) := by sorry

end AlgebraicGeometry.Scheme
