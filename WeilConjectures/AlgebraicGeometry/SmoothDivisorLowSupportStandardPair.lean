/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSupportSequence
import WeilConjectures.AlgebraicGeometry.RelativeLineLowDegreeGeneral
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Standard-pair low-degree support vanishing

This is the affine-line calculation in Steps 2--3 of
`lem-pur-smooth-divisor-low-support`, before étale chart transport.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Low-degree support vanishing for the zero section of a relative affine line.

The proof is the standard-pair part of the blueprint.  Form the ordinary closed-support
triangle and compare its first term with the right-derived supported-kernel functor using
`etale_injective_support_sequence` and `closedUpperShriekCompLowerStarIso`.  The
bounded-below support triangle is then transported
through `rightDerivedFunctorPlusCompatibility`; this is the unbounded-versus-Plus comparison
needed before applying the long exact homology sequence.  Apply the affine-line projection.
`relativeLineLowDegreeGeneral` identifies the two degree-zero projection units with the
identity on the base Tate sheaf and kills degree one of the affine-line projection.  The
resulting exact sequence gives vanishing in degrees zero and one, while the nonnegative
resolution bound gives negative degrees.  The assertion is strictly local: it has no smooth
pair, codimension, or chart hypotheses beyond the zero section.
(source: clause (b), local-comparison paragraph beginning
"Both classes are global classes supported on D";
blueprint: lem-pur-smooth-divisor-low-support)
-/
theorem isZero_homology_rightDerivedSectionsWithSupport_standard_pair
    {k : Type u} [Field k] (ell N : ℕ) (hell : Nat.Prime ell)
    (hell_unit : IsUnit (ell : k)) (hN : 1 ≤ N)
    {Y G : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [QuasiCompact aY]
    (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) Y) [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ((ell ^ N : ℕ) : Λ) = 0) :
    ∀ q : ℤ, q < 2 →
      IsZero (((DerivedCategory.homologyFunctor _ q).obj
        ((sectionsWithSupport (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (AlgebraicGeometry.Scheme.finiteEtaleTateSheaf Λ (ell ^ N)
              (AffineSpace (ULift.{u} (Fin 1)) Y) (by simpa using hΛ) 1))))) := by
  sorry

end AlgebraicGeometry.Etale
