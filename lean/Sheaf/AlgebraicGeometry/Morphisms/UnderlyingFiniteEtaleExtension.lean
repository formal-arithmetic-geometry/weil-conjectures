/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Underlying finite étale extension of a generically split Galois cover

Source: Stacks Project, Tags 0EYJ and 0EZJ, proofs of the spreading theorem.
(blueprint: lem-sbc-underlying-finite-etale-extension)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The underlying finite étale cover extends; no action on the extension is supplied.

Source: Stacks Project, Tags 0EYJ and 0EZJ, the construction of the finite étale morphism.
(blueprint: lem-sbc-underlying-finite-etale-extension)

Proof:
1. Over a discrete valuation ring, the special fibre is a regular Cartier divisor.
Ramification indices divide the group order, so the cover is tame. The normalization is
finite locally free and has the standard tame local form (0EYG, 0EYH). The rational point
and the simply transitive action split the fibre over the generic section point. The trait
criterion (0EYI) gives étaleness near the special section point, hence at the generic point
of the irreducible special fibre. Purity (0EYE) extends the cover across that divisor.
2. Over a Noetherian normal base, choose the maximal open carrying an extension. At a
minimal point of its complement, dimension one is the trait case. In dimension at least
two, normality gives depth at least two, and flatness transfers this to the total space.
The depth-two extension (0EY6) is finite and commutes with flat base change. Complete an
affine neighbourhood along the section: the completion is a power series ring over the
local base. The cover on the punctured section is split, by normality and its split generic
fibre. The full faithfulness theorem (0EY9) makes the cover over the punctured completion
split too. Its depth-two extension is split, so flat descent gives étaleness at the generic
point of the missing fibre; 0EYB gives étaleness everywhere. Spread to a larger open,
contradicting maximality. The action needed during this construction extends by normality.
3. For a qcqs base, descend the family, section, finite cover, action, rational point and
invertibility to a Noetherian normal integral approximation, as in 0EZJ. Descend smoothness
and replace the family by the open with geometrically connected fibres. Apply step 2 and
pull back its finite étale morphism and the generic-fibre comparison.
4. The family is connected: its smooth map with nonempty geometrically connected fibres
is open and surjective over a connected base. The image of a finite étale cover is both
open and closed; its generic restriction is nonempty, so the image is the entire family.
This gives surjectivity. The construction and comparison apply to each connected component
of the torsor, with its stabilizer subgroup, if the total space is disconnected. The
stabilizer order divides the group order and the split section fibre meets every component;
inducing the resulting stabilizer cover back to G recovers the given generic cover. -/
theorem GaloisCover.exists_finiteEtale_extension {S C : Scheme.{u}} [CompactSpace S]
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
    ∃ (P : Scheme.{u}) (π : P ⟶ C) (ψ : Z.P ⟶ P),
      IsFinite π ∧ Etale π ∧ Surjective π ∧ IsPullback ψ Z.π π j := by
  sorry

end AlgebraicGeometry.Scheme
