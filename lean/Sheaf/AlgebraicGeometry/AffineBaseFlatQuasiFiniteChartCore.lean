module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Sheaf.RingTheory.Depth

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The affine-base polynomial chart produced in the proof of Tag 00RH.

Proof: choose affine neighborhoods, apply quasi-finite polynomial factorization, use the
fibre flatness criterion and openness of flatness, and transport the resulting map to schemes.
Source: Stacks Project, Tag 00RH, using Tags 00QE, 00RE, 00R7 and 00RC.
(blueprint: lem-sbc-affine-base-flat-quasi-finite-chart-core) -/
 theorem exists_affine_base_flat_quasiFinite_chart_core
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (y : X) (ht : f y ∈ U)
    (hdepth :
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ (n : ℕ) (O : X.Opens) (V : T.Opens)
      (_ : IsAffine V.toScheme)
      (e : O.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme),
      y ∈ O ∧ Flat e ∧ LocallyQuasiFinite e ∧ LocallyOfFinitePresentation e ∧
        e ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) ≫ V.ι =
          O.ι ≫ f := by sorry

end AlgebraicGeometry
