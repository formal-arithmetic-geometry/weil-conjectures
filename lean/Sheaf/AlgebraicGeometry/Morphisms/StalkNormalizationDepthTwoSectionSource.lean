/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
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
public import Mathlib.RingTheory.KrullDimension.Basic

import Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension
import Sheaf.RingTheory.NormalLocalDepthTwo
import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# Source etaleness over the local section in dimension at least two

Source: Stacks Project, Tags 0EYJ, 0EY6 and 0EY9.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Every point of the finite local normalization above the closed section point
has a source open neighbourhood on which the normalization map is etale,
when the local base has dimension at least two.

Source: Stacks Project, Tag 0EYJ, final local computation; Tags 0EY6 and 0EY9.
(blueprint: lem-sbc-stalk-normalization-depth-two-section-source)

Proof: Localize at s; minimality identifies the inverse image of U with the
punctured spectrum of the normal Noetherian local domain A. Normality and
the dimension bound give depth(A) at least two. Smoothness gives flatness,
and the flat local depth formula gives depth at least two along the closed
fibre. The normal finite algebra n is therefore the unique depth-two
extension of the punctured finite etale algebra (Tag 0EY6). Extend the
G-action by normal generic full faithfulness. The rational generic section
point and its translates split the generic section fibre; the same full
faithfulness splits the fibre on the punctured section. Take a smooth affine
chart B around the closed section point. Its section-ideal completion is
A[[x₁,...,x_d]], flat over B. If d is positive, Tag 0EY9 extends the splitting
from the punctured section to the punctured completion. If d is zero the
section is the completed chart itself. Uniqueness and flat base change of
the depth-two extension make the completed finite algebra split. Completion
is faithfully flat at the section point, so etaleness descends to every
point of n above it. Openness of the etale locus gives the required source
opens. Componentwise the stabilizers have order dividing |G|; an empty
fibre gives a vacuous assertion. -/
theorem GaloisCover.stalk_normalization_depth_two_section_source {S C : Scheme.{u}}
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
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (S.presheaf.stalk s)) :
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
      ∃ V : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c a)).Opens, x ∈ V ∧ Etale (V.ι ≫ n) := by sorry

end AlgebraicGeometry.Scheme
