module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Completed affine sections of a power-torsion sheaf -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A natural comparison on all module sheaves is invertible on quasi-coherent
sheaves whose affine sections are killed by a positive power of the completion ideal.
This statement concerns one sheaf at a time, without formal systems or transitions.

Source: Stacks Project, Tags 088B (completed base change), 05GG (completion quotient),
and 01I9 (affine pullback).
(blueprint: lem-weil-pbc-completed-affine-sections-power-torsion)

Proof: Define the comparison by the unit of tensor pullback followed by restriction
from the inverse image of U to the whole completed affine scheme. This inverse image
is the whole scheme, since g factors through U. The structure-ring map on this chart
is B to its K-adic completion R; the Spec global-section identification therefore
makes the comparison B-linear. Naturality follows from the adjunction unit and
restriction maps. For a quasi-coherent sheaf M, affine pullback sections identify
this map with m mapping to 1 tensor m. If K^(n+1) kills M(U), its scalar action factors
through B/K^(n+1). Since B is Noetherian, K is finitely generated, and the positive
power completion quotient is R/K^(n+1)R = B/K^(n+1), compatibly with B to R. Tensoring
M(U) over this quotient identifies the unit with the identity, hence it is bijective
and gives an isomorphism of B-modules. The unit ideal forces M(U) = 0; the zero ideal
makes completion the original ring. The zero ring and empty affine open are included.
-/
theorem completedAffineSections_powerTorsion
    {Y : Scheme.{u}} [IsNoetherian Y] (J : Y.IdealSheafData) (U : Y.affineOpens) :
    let B := Γ(Y, U.1)
    let R := AdicCompletion (J.ideal U) B
    let S := Spec (CommRingCat.of R)
    let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
      U.2.isoSpec.inv ≫ U.1.ι
    let T := Scheme.Modules.tensorPullback g
    let E := moduleSpecΓFunctor (R := CommRingCat.of R)
    let L := ModuleCat.restrictScalars (algebraMap B R)
    ∃ c : SheafOfModules.evaluation Y.ringCatSheaf (op U.1) ⟶ T ⋙ E ⋙ L,
      ∀ (M : Y.Modules) (_ : M.IsQuasicoherent) (n : ℕ),
        J.ideal U ^ (n + 1) • (⊤ : Submodule B Γ(M, U.1)) = ⊥ →
          IsIso (c.app M) := by
  sorry

end AlgebraicGeometry
