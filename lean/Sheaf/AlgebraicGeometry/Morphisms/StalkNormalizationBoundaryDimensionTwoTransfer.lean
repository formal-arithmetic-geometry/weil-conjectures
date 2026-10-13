module
import Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore
public import Sheaf.RingTheory.Depth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Finite normalizations transfer the boundary dimension estimate to source stalks.
Source: Stacks Project, Tags 0337, 00LK, 033C and 00H8.
(blueprint: new-stalk-normalization-boundary-dimension-two-transfer)
Proof: on normal affine components, going down for the finite integral normalization
lifts a strict prime chain of length two from the target stalk to the source stalk. -/
theorem stalk_normalization_boundary_dimension_two_transfer {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s))
    (hboundary : let a := S.fromSpecStalk s
      ∀ y : (pullback c a : Scheme.{u}),
        y ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
        (2 : WithBot ℕ∞) ≤ ringKrullDim ((pullback c a).presheaf.stalk y)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ z : (pullback
      (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) : Scheme.{u}),
      n z ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim
        ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
          (pullback.fst c a) : Scheme.{u}).presheaf.stalk z) := by
  sorry
end AlgebraicGeometry.Scheme
