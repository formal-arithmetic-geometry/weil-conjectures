/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Basic

/-! # A common affine open with a generic hypersurface model

Source: Stacks Project, Tag 0559, first proof, and Tag 0552.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A generically geometrically integral affine family has a common affine open
with a hypersurface over its original base. The generic fibre of this open is
nonempty. No assertion about special fibres is made here.

Source: Stacks Project, Tag 0559, first proof, the separating transcendence basis
and common-open construction; Tag 0552, birational finite type schemes.
Proof: write S = Spec A and X = Spec B. Flatness over the domain A embeds B in
B tensor_A Frac(A). Geometric integrality of this generic fibre makes that ring
a domain, hence B is a domain as well. Its fraction field L is a regular finitely
generated extension of K = Frac(A). Choose a separating transcendence basis and
a primitive element for the remaining finite separable extension. Take the
primitive polynomial numerator of its minimal polynomial over K in the
transcendence variables. It is absolutely irreducible, since L/K is regular.
Multiply by one nonzero element of A to clear all coefficient denominators,
obtaining P in A[t_1,...,t_n]. Its generic hypersurface is geometrically integral
and has function field L. If L is purely transcendental, use the linear equation
in one additional variable, also covering relative dimension zero.
After inverting one nonzero base element the hypersurface ring is a domain:
make the polynomial monic by a separated-powers substitution, invert its leading
coefficient, and use freeness over the remaining polynomial variables to embed
in the generic fibre. These operations only replace the hypersurface by an
isomorphic open over a principal base open. The two finite type domain algebras
now have the same function field. Express their finitely many generators as
fractions in that field and invert all denominators. The resulting localizations
have a common further localization, giving isomorphic nonempty principal opens
of X and of the hypersurface. Their inclusions commute with the maps to S.
The open in X is affine; because its defining element is nonzero in B tensor K,
its generic fibre is nonempty, so eta belongs to its image. Compose the other
inclusion with the localization open immersion into the original hypersurface.

(blueprint: lem-sbc-common-generic-hypersurface-affine-open) -/
theorem exists_common_generic_hypersurface_affine_open
    {X S : Scheme.{u}} [IsAffine X] [IsReduced X] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hred : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ W : X.Opens, IsAffineOpen W ∧ η ∈ Set.range (W.ι ≫ f) ∧
      ∃ (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤)),
        let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
        let g : H ⟶ S := Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
        ∃ i : W.toScheme ⟶ H, IsOpenImmersion i ∧ i ≫ g = W.ι ≫ f ∧
          GeometricallyIrreducible (g.fiberToSpecResidueField η) ∧
          GeometricallyReduced (g.fiberToSpecResidueField η) := by sorry

end AlgebraicGeometry
