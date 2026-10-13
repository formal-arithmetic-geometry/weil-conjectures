/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
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
# Flatness of tame local normalization

Source: Stacks Project, Tags 0EYG, 0EYH, 0EYI and 0EYJ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The tame local normalization is flat, without a section or a rational point.

Source: Stacks Project, Tags 0EYJ (trait reduction), 0EYG and 0EYH.
(blueprint: lem-sbc-stalk-normalization-trait-flat)

Proof: The points of Spec O_{S,s} map exactly to generalizations of s. Minimality of s outside U
therefore identifies its inverse image with the punctured spectrum. By hypothesis the local ring
A = O_{S,s} is a DVR. The local smooth total space has a regular effective Cartier closed fibre
D, cut out by a uniformizer, and its complement is the local generic fibre. The cartesian
comparison identifies the cover on that complement with the base change of Z. On each connected
component use the stabilizer subgroup of G. Ramification indices divide its order, hence divide
the invertible order of G; the residue extensions are tame as well. Apply 0EYG and 0EYH: etale
locally on the local total space the normalization is a finite product of algebras B[T]/(T^e-f),
with e positive and invertible. Each factor is free over B, with basis 1,T,...,T^(e-1), by
division by its monic polynomial. A finite product is finite free, hence flat. Relative integral
closure commutes with localization, so the normalization described by these charts is the
concrete pullback n in the statement. Flatness descends from the etale charts. Empty covers give
the zero free module; disconnected covers are handled by the same finite products. No section or
splitting is used. -/
theorem GaloisCover.stalk_normalization_trait_flat {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
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
    IsFinite n → Flat n := by sorry

end AlgebraicGeometry.Scheme
