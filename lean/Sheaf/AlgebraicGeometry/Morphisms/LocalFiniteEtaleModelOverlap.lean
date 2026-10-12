/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality

import Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel
import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleStalkNeighbourhoodSpreading

/-!
# Local extension with an overlap comparison

Source: Stacks Project, Tag 0EYJ.
(blueprint: lem-sbc-local-finite-etale-model-overlap)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite étale model extends near a point outside the original open, with an
isomorphism of the two covers on the overlap. The neighbourhood need not contain U.

Source: Stacks Project, Tag 0EYJ, local claim and spreading, and Tags 0BQ5 and 0EY3.
(blueprint: lem-sbc-local-finite-etale-model-overlap)

Proof:
Choose a generic point s of an irreducible component of the nonempty closed complement
of U. Localization at s makes U the punctured spectrum of a normal local domain A.
Extend the G-action from the generic fibre to the existing finite étale cover by the
full faithfulness of finite étale restriction on the normal smooth integral family
(0BQM). The action laws and torsor identity hold by the same faithfulness.
If dim A = 1, A is a discrete valuation ring. The ramification indices divide the
invertible group order, so the normalization is tame. Its standard tame local form
and the split section fibre give étaleness near the section (0EYG, 0EYH, 0EYI), and
purity across the regular special divisor extends the cover everywhere (0EYE).
If dim A >= 2, normality gives depth at least two and flatness carries this depth to
the total space. Apply the finite depth-two algebra extension (0EY6). Complete a
smooth affine neighbourhood of the section in the section ideal; its completion is
a power series ring over A. The cover restricted to the punctured section is split:
its generic fibre is split by the rational point and torsor action, and full
faithfulness over the normal integral punctured base extends this splitting.
The power series full faithfulness theorem (0EY9) splits the cover on the punctured
completion. Compatibility of the depth-two extension with flat base change makes
the completed extension split as well. Flat descent and the fibre criterion (0EYB)
give étaleness on the missing fibre, hence everywhere on the local family.
Spread the local finite étale cover and its comparison with P to an open neighbourhood
W of s by 0BQ5 and 0EY3, shrinking W so that finiteness, étaleness, and the comparison
isomorphism hold. This gives Q over c inverse W and the isomorphism on c inverse U
intersect c inverse W. No union or gluing is done here.
For a disconnected torsor perform the connected construction on the components and
their stabilizers. Each stabilizer order divides the invertible group order. The
split section fibre meets each component. Induction to G and finite disjoint union
recover the original cover, and their overlap comparisons give the displayed iso. -/
theorem GaloisCover.exists_local_finiteEtale_model_overlap {S C : Scheme.{u}} [IsNoetherian S]
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
    (U : S.Opens) (hηU : genericPoint S ∈ U) (hU : U ≠ ⊤)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU) :
    ∃ (W : S.Opens) (s : S), s ∉ U ∧ s ∈ W ∧
      ∃ Q : (c ⁻¹ᵁ W).toScheme.FiniteEtale,
        Nonempty ((FiniteEtale.pullback
          (C.homOfLE (inf_le_left : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ U))).obj PA ≅
          (FiniteEtale.pullback
          (C.homOfLE (inf_le_right : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W))).obj Q) := by
  obtain ⟨s, hs, Q, e⟩ :=
    GaloisCover.exists_stalk_finiteEtale_model hS c σ hσ G hG
      q j hCη sη hsq hsj Z hZ U hηU hU jU PA ψ hjU hψ
  obtain ⟨W, hsW, R, eR⟩ :=
    FiniteEtale.exists_neighbourhood_model_of_stalk c U PA s Q e
  exact ⟨W, s, hs, hsW, R, eR⟩

end AlgebraicGeometry.Scheme
