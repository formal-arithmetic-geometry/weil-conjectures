/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Torsor

/-!
# Spreading a finite étale Galois cover

Let `S` be a qcqs integral normal scheme with generic point `η`, let `c : C ⟶ S` be a qcqs
smooth morphism with geometrically connected fibres, and fix a section `σ` of `c`. A finite
étale Galois cover of the generic fibre `C_η` with abelian group `M` of order invertible on
`S`, connected and carrying a `κ(η)`-rational point above `σ(η)`, extends to a finite étale
Galois cover of `C` with group `M`. This is [Stacks 0EZJ]; the statement is the input taken
by the induction in the proof of smooth base change.

A Galois cover with abelian group `M` is the same thing as a connected `M`-torsor, so the
covers are recorded as `AlgebraicGeometry.Scheme.EtaleTorsor` of
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Torsor` together with a `ConnectedSpace`
hypothesis on the total space.

## Implementation notes

The statement takes the constructions it speaks about as explicit data rather than building
them, so that it is a statement and not a construction:

- the generic fibre `C_η` is a scheme `Cη` together with a cartesian square over
  `Spec S.functionField ⟶ S`, the latter being `AlgebraicGeometry.Scheme.fromSpecStalk` at
  the generic point;
- the generic point of the section is a morphism `sη : Spec S.functionField ⟶ Cη` which is a
  section of the generic fibre and lies over `σ`;
- the restriction of the produced torsor to the generic fibre is expressed by asking for a
  morphism `ψ` from the given torsor to the produced one which makes a cartesian square over
  `j : Cη ⟶ C` and commutes with the `M`-actions.

Normality of `S` is spelled out as integral closedness of all the stalks, there being no
`IsNormal` predicate on schemes; qcqs-ness of `S` is `CompactSpace` together with
`QuasiSeparatedSpace`.

Two refinements of `0EZJ` are left to the prose. First, the blueprint allows an arbitrary
finite Galois group `G`, while only the abelian case is used by, and stated for, smooth base
change. Second, the uniqueness of the extension is not asserted.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre`: the spreading
  statement.

## References

- Stacks Project, Tag `0EZJ`, <https://stacks.math.columbia.edu/tag/0EZJ>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleTorsor

/-- Blueprint `sk-prop-input-spreading`: Spreading a finite étale Galois cover

Let `S` be a qcqs integral normal scheme with generic point `η` and function field
`κ(η) = S.functionField`, let `c : C ⟶ S` be a qcqs smooth morphism with geometrically
connected fibres, and let `σ` be a section of `c`. Let `M` be a finite abelian group whose
order is invertible on `S`, let `Cη` be the generic fibre of `c` and let `Z` be a connected
`M`-torsor on `Cη` — that is, a finite étale Galois cover of `Cη` with group `M` — carrying
a `κ(η)`-rational point above the generic point `sη` of the section. Then `Z` extends to an
`M`-torsor on `C`: there is an `M`-torsor `T` on `C` and an `M`-equivariant morphism
`Z.P ⟶ T.P` over `j : Cη ⟶ C` making a cartesian square, so that the restriction of `T` to
the generic fibre is `Z`; and `T` is again connected, that is, Galois with group `M`.

This is [Stacks 0EZJ]. -/
@[stacks 0EZJ]
theorem exists_isPullback_of_genericFibre {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (hM : IsUnit ((Nat.card M : ℕ) : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : EtaleTorsor M Cη) [ConnectedSpace Z.P]
    (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (T : EtaleTorsor M C) (ψ : Z.P ⟶ T.P), IsPullback ψ Z.π T.π j ∧
      (∀ m : M, Z.smul m ≫ ψ = ψ ≫ T.smul m) ∧ ConnectedSpace T.P :=
  sorry

end AlgebraicGeometry.Scheme.EtaleTorsor
