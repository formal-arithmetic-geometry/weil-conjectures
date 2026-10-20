/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import Sheaf.Paper.StrictHenselizationFunctoriality

/-!
# The fibre of a strict henselization over its distinguished point

Source: Stacks Project, Tags 04HX, 04GW and 04GP, strict henselization construction.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The closed point of an affine presentation of a strict henselization maps to the
selected geometric point. This is the backward half of the singleton-fibre theorem.
Source: Stacks Project, Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-closed-fiber-backward)
Proof: use the local-ring structure and residue equation from strictHenselizationResidue.
The isomorphism transports specializations to and from the unique closed points; antisymmetry
identifies the image of the closed point, and the residue equation gives the result. -/
theorem strictHenselizationStructuralMap_closedPoint_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s) :
    (e.hom ≫ strictHenselizationStructuralMap s) (IsLocalRing.closedPoint A) =
      s (IsLocalRing.closedPoint Ω) := by
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, _, hbase, _⟩ := AlgebraicGeometry.strictHenselizationResidue s rfl
  let := hlocal
  have hforward := IsLocalRing.specializes_closedPoint
    (e.hom (IsLocalRing.closedPoint A))
  have hbackward := (IsLocalRing.specializes_closedPoint
    (e.inv (IsLocalRing.closedPoint (strictHenselizationRing s)))).map e.hom.continuous
  have hpoint : e.hom (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (strictHenselizationRing s) := by
    apply (hforward.antisymm ?_).eq
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id] at hbackward
    exact hbackward
  simpa only [Scheme.Hom.comp_apply, hpoint] using hbase

/-- The only point of the strict henselization over the underlying geometric point is
its closed point, in any local affine presentation.
Source: Stacks Project, Tags 04HX, 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-closed-fiber)

Proof: choose an affine neighbourhood Spec R of the image p of s. The pointed etale
coordinate-ring colimit is the strict henselization of R_p (Tag 04HX): localizing each
neighbourhood at its selected prime does not change the colimit, since every element
outside that prime becomes invertible on a smaller pointed open neighbourhood. Its
maximal ideal is p times the colimit ring, and its quotient is the separable algebraic
closure of the residue field of p inside Ω. In particular that quotient is a field.
Thus the fibre over p has exactly one prime, the maximal ideal: primes over p contain
p times the colimit ring, and conversely that maximal ideal contracts to p. Under the
isomorphism e this point is the closed point of A, since an isomorphism of spectra
preserves closed points and a local ring has a unique closed point. Both implications
of the displayed equivalence follow. This argument also covers a field A, whose
closed point is its zero ideal. -/
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (x : Spec (.of A)) :
    (e.hom ≫ strictHenselizationStructuralMap s) x = s (IsLocalRing.closedPoint Ω) ↔
      x = IsLocalRing.closedPoint A := by
  constructor
  · exact strictHenselizationStructuralMap_fiber_eq_closedPoint_compat s e x
  · intro hx
    subst x
    exact strictHenselizationStructuralMap_closedPoint_eq s e

end AlgebraicGeometry.Scheme
