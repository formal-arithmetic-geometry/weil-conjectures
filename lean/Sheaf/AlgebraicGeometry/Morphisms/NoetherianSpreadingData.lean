/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Noetherian approximation data for spreading a finite torsor

Source: Stacks Project, Tag 0EZJ, limit reduction.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Descend the family and its generic torsor, without constructing an extension.

Source: Stacks Project, Tag 0EZJ, proof of Lemma 58.31.9.
(blueprint: lem-sbc-noetherian-spreading-data)

Proof:
Write the qcqs integral normal base as a directed limit of normal integral schemes of
finite type over the integers with affine transition maps. This is obtained from absolute
Noetherian approximation by normalizing each stage in the base: these normalizations are
finite by the finiteness theorem over the integers and their limit is the given normal
base, as is checked on affine opens. Descend the finitely presented smooth qcqs family and
its section to one stage. Replace the descended family by the open locus with geometrically
connected fibres; the original family maps into this locus, and the section lands in it
after enlarging the stage. Descend invertibility of the group order. The generic fibre is
the limit of the generic fibres at the stages. Finite étale descent therefore descends the
cover and its finite group action, including the torsor isomorphism, to some generic fibre.
Descend the rational point and its equality with the generic section after enlarging the
stage once more. The resulting family comparison and generic-fibre comparison commute;
the comparison of covers is a pullback by finite étale descent. Retain these comparison
maps and all the descended hypotheses. No extension of the descended cover is constructed
in this lemma. -/
theorem GaloisCover.exists_noetherian_spreading_data {S C : Scheme.{u}} [CompactSpace S]
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
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (S₀ C₀ : Scheme.{u}) (hI₀ : IsIntegral S₀),
      letI : IsIntegral S₀ := hI₀
      ∃ (c₀ : C₀ ⟶ S₀) (σ₀ : S₀ ⟶ C₀)
        (Cη₀ : Scheme.{u}) (q₀ : Cη₀ ⟶ Spec S₀.functionField) (j₀ : Cη₀ ⟶ C₀)
        (sη₀ : Spec S₀.functionField ⟶ Cη₀) (Z₀ : GaloisCover G Cη₀)
        (a : C ⟶ C₀) (k : Cη ⟶ Cη₀) (χ : Z.P ⟶ Z₀.P),
        IsNoetherian S₀ ∧ QuasiSeparatedSpace S₀ ∧
        (∀ x : S₀, IsIntegrallyClosed (S₀.presheaf.stalk x)) ∧
        QuasiCompact c₀ ∧ QuasiSeparated c₀ ∧ Smooth c₀ ∧ GeometricallyConnected c₀ ∧
        σ₀ ≫ c₀ = 𝟙 S₀ ∧ IsUnit (Nat.card G : Γ(S₀, ⊤)) ∧
        IsPullback q₀ j₀ (S₀.fromSpecStalk (genericPoint S₀)) c₀ ∧
        sη₀ ≫ q₀ = 𝟙 _ ∧ sη₀ ≫ j₀ = S₀.fromSpecStalk (genericPoint S₀) ≫ σ₀ ∧
        (∃ z₀ : Spec S₀.functionField ⟶ Z₀.P, z₀ ≫ Z₀.π = sη₀) ∧
        k ≫ j₀ = j ≫ a ∧ IsPullback χ Z.π Z₀.π k := by sorry

end AlgebraicGeometry.Scheme
