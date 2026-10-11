/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# The theorem of the cube over a field, with an arbitrary residue-field fibre

Source: Stacks Project, More on Morphisms, Theorem 37.33.8, Tag 0BF4,
specialised to a field (blueprint: lem-sc-general-theorem-of-cube).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- The theorem of the cube over a field, allowing any point of the connected factor.
Source: Stacks Project, Tag 0BF4 (blueprint: lem-sc-general-theorem-of-cube).

Proof: (1) Products and base changes preserve properness and finite presentation;
flatness over a field is automatic. The geometrically integral product has geometrically
integral fibres (Stacks, Tags 038K, 038F, 035Z).
(2) Apply lem-sc-proper-flat-global-sections (Tag 0E0L) to X, Y, and their product:
the structure sheaf pushes forward to the base structure sheaf universally.
(3) Apply lem-sc-picard-diagonal-locally-closed (Tag 0BDP) to the projection to Z,
obtaining the universal locally closed locus Z' on which L descends from an invertible N.
(4) Fibre triviality at z implies z factors through Z', so Z' is nonempty.
(5) Apply lem-sc-picard-locus-closed (Tag 0BF0) to show Z' is closed.
(6) For each point of Z', the two slice hypotheses and the universal pushforward
property allow lem-sc-picard-product-open (Tag 0BF3) to give a neighbourhood on which
L is trivial. Its inclusion factors through Z' by the universal property, so Z' is open.
(7) Connectedness implies the image of Z' is all of Z; the local factorizations glue
through the immersion, a monomorphism, giving Z' = Z scheme-theoretically.
(8) Now L is the pullback of N from Z. Pulling back along x × y × id identifies N
with a trivial module by the slice hypothesis, hence L is trivial. -/
theorem nonempty_iso_unit_of_tensorPullback_slices_and_fiber
    {k : Type u} [Field k] (X Y Z : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] [ConnectedSpace Z.left]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules) [L.IsInvertible]
    (hx : Nonempty
      ((Scheme.Modules.tensorPullback
        (lift (lift (toUnit (Y ⊗ Z) ≫ x) (fst Y Z)) (snd Y Z)).left).obj L ≅
        SheafOfModules.unit _))
    (hy : Nonempty
      ((Scheme.Modules.tensorPullback
        (lift (lift (fst X Z) (toUnit (X ⊗ Z) ≫ y)) (snd X Z)).left).obj L ≅
        SheafOfModules.unit _))
    (hz : ∃ z : Z.left, Nonempty
      ((Scheme.Modules.tensorPullback ((snd (X ⊗ Y) Z).left.fiberι z)).obj L ≅
        SheafOfModules.unit _)) :
    Nonempty (L ≅ SheafOfModules.unit _) := by
  sorry

end AlgebraicGeometry
