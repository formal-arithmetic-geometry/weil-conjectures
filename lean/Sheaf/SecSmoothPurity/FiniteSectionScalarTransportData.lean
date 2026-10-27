/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.SecSmoothPurity.DncCoefficientTransportData

/-! # Coefficient transport data for finite section specialization

The coefficient maps and the two fibre squares are the input data for the
canonical scalar transport argument. Their construction is the coefficient
comparison step in the smooth-purity reduction proof.
(blueprint: new-lem-sp-finite-section-specialization-scalar-canonical-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The section coefficient maps are invertible and satisfy both canonical fibre
squares.  This is the coefficient/base-change part of the scalar transport proof.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-compatibilities.proof.md, (3),
and sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, (2), Steps 1--3.
The maps are obtained by the finite coefficient comparison for the exceptional
right adjoint; the two displayed fibre equations are the specialization of the
section scalar/base-change theorem to the one and zero sections.  The argument
uses only finiteness and the common annihilator and includes zero rings and rank
zero.
(blueprint: new-lem-sp-finite-section-specialization-scalar-canonical-data). -/
theorem finiteSectionScalarTransport_data
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [HasCompactification g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s]
    [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
    (hS : IsUnit (N : Γ(S, ⊤))) :
    IsIso (WeilConjectures.DncCoefficientTransport.sectionMap φ g s) ∧
      IsIso (WeilConjectures.DncCoefficientTransport.sectionMap φ
        (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ∧
      WeilConjectures.DncCoefficientTransport.FibreCompatibility φ g s hs := by
  sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity
