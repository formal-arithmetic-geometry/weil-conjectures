/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality

/-!
# Extension over a stalk before spreading

Source: Stacks Project, Tag 0EYJ, proof of the local claim.
(blueprint: lem-sbc-stalk-finite-etale-model)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The cover on the open extends after base change to a suitable stalk.

Source: Stacks Project, Tag 0EYJ (pione-lemma-extend-covering), local claim;
Tags 0BQM, 0EYG, 0EYH, 0EYI, 0EYE, 0EY6, 0EY9, and 0EYB.
(blueprint: lem-sbc-stalk-finite-etale-model)

Proof:
Choose s generic in an irreducible component of the nonempty closed complement of U.
The inverse image of U in Spec O(S,s) is the punctured spectrum of a normal
Noetherian local domain A. The generic G-action extends to PA on this punctured
family by full faithfulness for finite etale covers of normal integral schemes
(0BQM); faithfulness also gives the action laws and torsor identity.
If A has dimension one, it is a DVR. Ramification indices divide the invertible
order of G, so the normalization is tame. Its tame local form (0EYG, 0EYH)
and the split section fibre test (0EYI) give etaleness near the section.
The special fibre is geometrically connected and smooth, hence irreducible;
the etale neighbourhood contains its generic point. Purity for its regular
Cartier divisor (0EYE) extends the cover across the entire special fibre.
If A has dimension at least two, normality gives depth at least two; flatness
propagates this along the missing fibre. The depth-two algebra extension (0EY6)
is finite, unique with the specified depth, and commutes with flat base change.
Complete a smooth affine neighbourhood of the section in its section ideal;
the completion is a power series ring over A and the completion map is flat.
The section restriction of the punctured cover is split: its generic restriction
is split by the rational point and torsor action, and normal generic full
faithfulness extends this splitting. Power series full faithfulness (0EY9)
then splits the cover on the punctured completion. Uniqueness of the depth-two
extension makes its extension split as well. Flat descent and the fibre test
(0EYB) give etaleness on the missing fibre, hence everywhere.
For a disconnected torsor apply the construction to its components and their
stabilizers, whose orders divide the invertible group order, and induce to G.
The construction restricts to PA on the punctured local family, giving precisely
the isomorphism between the two pullbacks displayed below. No neighbourhood
of s is constructed in this lemma. -/
theorem GaloisCover.exists_stalk_finiteEtale_model {S C : Scheme.{u}} [IsNoetherian S]
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
    ∃ (s : S), s ∉ U ∧
      ∃ Q : (Limits.pullback c (S.fromSpecStalk s)).FiniteEtale,
        Nonempty ((FiniteEtale.pullback
          (pullback.fst (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj PA ≅
          (FiniteEtale.pullback
          (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj Q) := by sorry

end AlgebraicGeometry.Scheme
