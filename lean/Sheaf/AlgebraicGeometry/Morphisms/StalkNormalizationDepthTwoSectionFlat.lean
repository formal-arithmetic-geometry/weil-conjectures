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

public import Sheaf.RingTheory.Depth

import Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension
import Sheaf.RingTheory.NormalLocalDepthTwo
import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# Flatness of the normalization near a split section

Source: Stacks Project, Tag 0EYJ, the final formal-neighbourhood calculation;
Tags 0EY6 and 0EY9.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The formal section calculation gives flatness on a target neighbourhood.
The depth-two calculation does not require invertibility of the group order.

Source: Stacks Project, Tag 0EYJ, proof of the local claim, last three paragraphs;
Tags 0EY6 and 0EY9.
(blueprint: lem-sbc-stalk-normalization-depth-two-section-flat)

Proof: Put A = O(S,s). The inverse image of U in Spec A is its punctured
spectrum: a point maps to a generalization of s, and minimality excludes
all missing points other than s. The local normalization is normal, since
normalization in the normal punctured finite etale algebra is normal and
localization preserves normality. Its finite algebra is the depth-two
extension of the punctured finite etale algebra: smoothness and the flat
local depth formula give depth at least two on the missing fibre, and
normality gives the corresponding depth condition on the normalization.
The uniqueness assertion of Tag 0EY6 identifies these two extensions.

Extend the action to the punctured cover using generic-fibre full
faithfulness. A rational point and its G-translates trivialize the generic
section fibre. Normal generic full faithfulness extends this trivialization
over the punctured section (extend the inverse as well). Choose a smooth
affine chart Spec B containing the closed section point. The section factors
through this chart, since any open of a local scheme containing its closed
point is the entire scheme. Complete B in the section ideal. Smoothness
identifies the completion with A[[x_1,...,x_d]], and Noetherian completion is
flat over B. For d > 0, Tag 0EY9 extends the section trivialization to the
punctured completion; for d = 0 it is already the same trivialization.
Flat base change and uniqueness in Tag 0EY6 then identify the completed
finite algebra with the product of copies of the completed chart.

The completion map is faithfully flat after localization at the closed
section point, since the section ideal lies in its maximal ideal. Freeness
of the split algebra therefore implies flatness at every source point
above that point, by faithfully flat descent of flatness. The finite
normalization is of finite presentation over the Noetherian local total
space. Its flat locus is open. The complement is closed, and its image in the
local total space is closed because n is finite. Remove this image to
obtain a target open W containing the closed section point. The entire
restriction of n over W is flat.
This conclusion asserts only flatness, not purity or etaleness. The empty
source is vacuous, and d = 0 is included explicitly above. -/
theorem GaloisCover.stalk_normalization_depth_two_section_flat {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
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
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∃ W : (pullback c a).Opens,
      τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) ∈ W ∧ Flat (n ∣_ W) := by sorry

end AlgebraicGeometry.Scheme
