/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Finiteness of the normalization over a stalk

Source: Stacks Project, Tag 0EYJ, proof of the local claim.
(blueprint: lem-sbc-stalk-normalization-finite)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Finiteness of the concrete normalization at a generic boundary point.

Source: Stacks Project, Tag 0EYJ (pione-lemma-extend-covering), local claim;
Tags 0EYG, 0EYH (tame normalization) and 0EY6 (depth-two extension).
(blueprint: lem-sbc-stalk-normalization-finite)

Proof: The minimality condition on s identifies the inverse image of U in
Spec O(S,s) with the punctured spectrum. This is a normal Noetherian local
domain of positive dimension, since the generic point belongs to U.
Smoothness and geometrically connected fibres make the local total space
normal integral. Extend the G-action to the punctured cover by generic full
faithfulness. In dimension one the base is a DVR. The ramification indices
of each connected component divide the order of its stabilizer, hence |G|,
and are invertible. The tame normalization theorem makes the normalization
finite locally free. In dimension at least two normality gives depth at least
two on the base, and flatness gives that bound along the missing fibre.
The depth-two extension of the finite algebra is coherent and finite by
0EY6. It is normal: on affine charts a function integral over this algebra
lies in the normal algebra on the punctured open and extends by the depth-two
property. Thus it is the integral closure in the punctured algebra.
Integral closure commutes with localization, so this local normalization is
exactly the pullback of the relative normalization used in the conclusion.
For a disconnected cover perform the construction on its components and
combine the resulting finite algebras as a finite product. Empty covers are
included. No rational point or section is needed for finiteness. -/
theorem GaloisCover.stalk_normalization_finite {S C : Scheme.{u}} [IsNoetherian S]
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
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    IsFinite (pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c (S.fromSpecStalk s))) := by sorry

end AlgebraicGeometry.Scheme
