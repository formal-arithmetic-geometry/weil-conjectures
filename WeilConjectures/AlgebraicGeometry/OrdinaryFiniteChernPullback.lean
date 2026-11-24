/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
import all WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange

/-! # Pullback of a module-derived scalar Kummer Chern class

## References

* Stacks Project, Tags 03PL and 03FD.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] Scheme.finiteEtaleTateLine Scheme.kummerδ₁
  AlgebraicGeometry.ProjectiveSpace
  ordinaryFiniteUnitPullback ordinaryFiniteShiftedLinePullback
  Scheme.Pic.toCohomologicalPicardGroup Scheme.Pic.map

/-- Pull a shifted-line arrow back using the fixed constant and twist comparisons.
This is the literal normalized pullback composite, recorded once for arbitrary schemes. -/
@[irreducible]
def ordinaryFiniteLinePullbackMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (c : ordinaryFiniteUnit A Y ⟶ (ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) :
    ordinaryFiniteUnit A X ⟶ (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ :=
  ordinaryFiniteArrowPullback A f _ _ c
    (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom

/-- The normalized derived pullback realizes the Kummer class of the pulled-back line.
This assertion involves no direct image, diagonal, trace, or projective-line splitting
(Stacks, Tags 03PL and 03FD). -/
theorem ordinaryFiniteChern_pullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (M : Y.Pic)
    (c : ordinaryFiniteUnit A Y ⟶ (ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteClass A Y (Scheme.finiteEtaleTateLine Y N A hA) 2 c =
      Sheaf.H.map (ordinaryFiniteRootMap A N hA Y) 2
        (Y.kummerδ₁ N hY (Scheme.Pic.toCohomologicalPicardGroup Y M))) :
    ordinaryFiniteClass A X (Scheme.finiteEtaleTateLine X N A hA) 2
        (ordinaryFiniteLinePullbackMap A N hA t f hY c) =
      Sheaf.H.map (ordinaryFiniteRootMap A N hA X) 2
        (X.kummerδ₁ N hX
          (Scheme.Pic.toCohomologicalPicardGroup X (Scheme.Pic.map f M))) := by
  unfold ordinaryFiniteLinePullbackMap ordinaryFiniteArrowPullback
  refine (class_chern_pullback A N hA t f hY c).trans ?_
  rw [hc]
  exact kummer_class_pullback A N hA t f hY hX M _ rfl

end AlgebraicGeometry.Etale
