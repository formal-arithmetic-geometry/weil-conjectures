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
# Underlying finite étale extension over a Noetherian normal base

Source: Stacks Project, Tag 0EYJ.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Noetherian case of extension of a generically split finite torsor.

Source: Stacks Project, Tag 0EYJ, proof of Lemma 58.31.8.
(blueprint: lem-sbc-noetherian-finite-etale-extension)

Proof:
The trait case follows by tame normalization: the ramification index divides the group
order, the section fibre splits by the torsor action, the trait test gives étaleness near
the section, and purity extends across the special divisor. For a normal Noetherian base,
choose a maximal open admitting an extension. At a minimal point of its complement,
dimension one is the trait case. In higher dimension, normality and flatness give depth
two along the missing fibre. Extend the finite algebra by the depth-two extension theorem.
Complete along the section; smoothness identifies this with a power series ring. The
section restriction is split because it is finite étale over a normal integral punctured
base and split generically. Full faithfulness over the punctured completion implies the
completed cover is split. Compatibility of depth-two extension with flat base change and
flat descent give étaleness at the generic point of the missing fibre; the fibre criterion
gives étaleness throughout. Spread to a larger open, contradicting maximality. If the
original torsor is disconnected, apply the argument to each connected component with its
stabilizer (whose order divides the group order); the split section meets each component,
and inducing and taking the disjoint union recovers the original cover. -/
theorem GaloisCover.exists_finiteEtale_extension_noetherian {S C : Scheme.{u}} [IsNoetherian S]
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
      IsFinite π ∧ Etale π ∧ IsPullback ψ Z.π π j := by sorry

end AlgebraicGeometry.Scheme
