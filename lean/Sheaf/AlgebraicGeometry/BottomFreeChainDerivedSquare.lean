/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # Derived square for a finite free chart model -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
namespace AlgebraicGeometry.Scheme

/-- Compare the restricted derived square with its explicit termwise tensor model.
Source: Stacks Project, Tags 06YD, 06YJ and 0D5S.
Proof: Finite free terms are flat, so bounded-above A and B are K-flat (06YD).
The single left-derived counit for tensor pullback on the inverse-image open is
invertible on both complexes (06YJ), and naturality gives their derived square.
Compose the given square with the natural derived composition comparisons
along the cartesian open square (0D5S). Exact restriction identifies derived pullback along
an open immersion with restriction. Transport the resulting square through the
exact inverse of the module-site equivalence, whose termwise functor factors through
Q. This gives the displayed square in the derived category of the localized site.
The standard localization used here is canonically equivalent to any chosen one;
no choice of an arbitrary resolution is involved. Empty opens, zero ranks and zero
complexes use the same counit and exact equivalences.
(blueprint: lem-sc-bottom-free-chain-derived-square). -/
theorem bottomFreeChain_derived_square
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (X Z : schemeDerivedCategory T) (f : X ⟶ Z)
    (W : T.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ℤ)
    (hAbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (A.X i))
    (hBbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (B.X i))
    (hAfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (hBfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (α : A ⟶ B)
    (eA : (derivedPullback W.ι).obj X ≅ DerivedCategory.Q.obj A)
    (eB : (derivedPullback W.ι).obj Z ≅ DerivedCategory.Q.obj B)
    (hsquare : (derivedPullback W.ι).map f ≫ eB.hom =
      eA.hom ≫ DerivedCategory.Q.map α)
    (T' : Scheme.{u}) (g : T' ⟶ T) :
    let V := g ⁻¹ᵁ W
    let F := Modules.tensorPullback (g.resLE W V (le_refl V)) ⋙
      (Modules.overEquiv V).inverse
    ∀ hF : F.Additive,
      letI := hF
      letI := HasDerivedCategory.standard
        (SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over V))
      let R := SheafOfModules.overFunctor.{u} (moduleRings T'.toRingedSpace) V
      let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A
      let Q := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B
      let β := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map α
      ∃ (eP : R.mapDerivedCategory.obj ((derivedPullback g).obj X) ≅
          DerivedCategory.Q.obj P)
        (eQ : R.mapDerivedCategory.obj ((derivedPullback g).obj Z) ≅
          DerivedCategory.Q.obj Q),
        R.mapDerivedCategory.map ((derivedPullback g).map f) ≫ eQ.hom =
          eP.hom ≫ DerivedCategory.Q.map β := by sorry

end AlgebraicGeometry.Scheme
