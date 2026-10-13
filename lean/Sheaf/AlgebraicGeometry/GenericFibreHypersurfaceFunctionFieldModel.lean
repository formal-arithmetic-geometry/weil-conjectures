/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Basic

public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Construct a geometrically integral hypersurface with the same generic fraction ring.
The fraction-ring isomorphism fixes sections of the spectrum of the residue field.

Source: Stacks Project, Tag 0559, first proof, field generators and polynomial quotient.
Proof: Write A for the domain of base sections and K for its fraction field, identified
with the residue field at the generic point. The generic fibre is the spectrum of a
finitely generated geometrically integral K-algebra B. Its fraction field L is a
finitely generated separably generated extension of K. Choose a separating
transcendence basis and a primitive element for the remaining finite separable
extension. Its minimal polynomial over the rational function field, after removing
content, gives a primitive polynomial Q over K in these variables and one additional
variable. Its quotient is a domain with fraction field L. After extension to an
algebraic closure of K, the same quotient injects into the localization of the
geometrically integral field extension L; hence it remains a domain. Clear the
finitely many coefficient denominators by a nonzero element of A to get P over A.
This scalar is invertible over K, so the generic quotient and its fraction field are
unchanged. Polynomial algebras in finitely many variables and their principal
quotients are finitely presented, hence their generic structure maps are locally
of finite type. The two generic section rings are domains and their fraction rings
are K-isomorphic, giving the stated isomorphism and compatibility. For a purely
transcendental L, use the additional variable with equation T, including L = K.

(blueprint: lem-sbc-generic-fibre-hypersurface-function-field-model) -/
theorem exists_generic_fibre_hypersurface_function_field_model
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
        IsIntegral (f.fiber η) ∧ IsIntegral (g.fiber η) ∧
        LocallyOfFiniteType (g.fiberToSpecResidueField η) ∧
        ∃ e : FractionRing Γ(f.fiber η, ⊤) ≃+* FractionRing Γ(g.fiber η, ⊤),
          ∀ a : Γ(Spec (.of (S.residueField η)), ⊤),
            e (algebraMap Γ(f.fiber η, ⊤) (FractionRing Γ(f.fiber η, ⊤))
              ((f.fiberToSpecResidueField η).appTop.hom a)) =
            algebraMap Γ(g.fiber η, ⊤) (FractionRing Γ(g.fiber η, ⊤))
              ((g.fiberToSpecResidueField η).appTop.hom a) := by sorry

end AlgebraicGeometry
