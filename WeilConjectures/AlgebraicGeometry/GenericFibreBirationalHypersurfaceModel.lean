/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Basic

import WeilConjectures.AlgebraicGeometry.GenericFibreHypersurfaceFunctionFieldModel
import WeilConjectures.AlgebraicGeometry.AffineBirationalOfFractionRingEquiv

/-! # A birational hypersurface model of a geometrically integral generic fibre

## References

* [Stacks, Tag 0559], [Stacks, Tag 0552]
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- The generic fibre, without any spreading of its common opens, has a birational
geometrically integral hypersurface model whose equation has coefficients on the base
(Stacks, Tags 0559, 0552). -/
theorem exists_generic_fibre_birational_hypersurface_model
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hred : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤)),
      let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
      let g : H ⟶ S := Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
      GeometricallyIrreducible (g.fiberToSpecResidueField η) ∧
        GeometricallyReduced (g.fiberToSpecResidueField η) ∧
        Scheme.BirationalOver (f.fiberToSpecResidueField η)
          (g.fiberToSpecResidueField η) := by
  obtain ⟨n, P, hgeomH, hredH, hX, hH, hft, e, he⟩ :=
    exists_generic_fibre_hypersurface_function_field_model f η hη hgeom hred
  let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
  let g : H ⟶ S := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
  have : IsIntegral (f.fiber η) := hX
  have : IsIntegral (g.fiber η) := hH
  have : LocallyOfFiniteType (g.fiberToSpecResidueField η) := hft
  have : LocallyOfFiniteType (f.fiberToSpecResidueField η) :=
    show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField η)) from
      inferInstance
  refine ⟨n, P, hgeomH, hredH, ?_⟩
  exact birationalOver_of_fractionRing_equiv
    (f.fiberToSpecResidueField η) (g.fiberToSpecResidueField η) e he

end AlgebraicGeometry
