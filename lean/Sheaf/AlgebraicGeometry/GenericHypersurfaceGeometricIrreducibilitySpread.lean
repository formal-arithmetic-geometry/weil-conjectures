/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Spreading geometric integrality for a hypersurface

Source: Stacks Project, Tag 0557, lemma-irreducible-polynomial.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A hypersurface with geometrically integral generic fibre has geometrically
irreducible fibres on a neighbourhood of the generic point.

Source: Stacks Project, Tag 0557, lemma-irreducible-polynomial.
Proof: put A = Gamma(S, top), a domain, and K = Frac(A). Identify the generic
fibre ring with K[t_1,...,t_n]/(P_K). If P_K is zero, all coefficients of P vanish
by injectivity of A into K, so P is zero; all fibres are affine spaces and the
whole base works. Otherwise geometric reducedness and irreducibility say that
over an algebraic closure of K the principal ideal (P_K) is prime. Thus P_K is
absolutely irreducible up to a nonzero scalar. A nonzero constant is excluded by
the nonemptiness of the generic fibre. A triangular substitution by sufficiently
separated powers of the last variable makes the leading coefficient a nonzero
element of A. Invert it and divide by it to make the polynomial monic in the
last variable of positive degree d. This coordinate change commutes with every
field specialization. Bound factor degrees in each of the remaining variables
by the corresponding degree of P. For each positive pair e_1 + e_2 = d, form
the finite type coefficient algebra of two monic factors with these bounds,
quotienting by all coefficient equations of P = Q_1 Q_2. Absolute irreducibility
excludes points over the algebraic closure of K. Nullstellensatz says the generic
coefficient algebra is zero. Consequently 1 is killed by some nonzero base
element, and localizing at this element kills the whole coefficient algebra.
Invert the finite product of these elements and the leading coefficient. No
specialization into any algebraically closed residue field can then factor P.
The monic polynomial retains positive degree, so each hypersurface is nonempty
and integral over that field. For an arbitrary field extension of a residue
field, pass to its algebraic closure and descend irreducibility and nonemptiness
along the surjective field-extension base change. This gives exactly geometric
irreducibility of the fibre morphism. The resulting principal base open contains
eta. If d = 1 the product of factor obstructions is empty and equals 1. If n = 0,
the generic hypotheses force P = 0, handled in the first case.

(blueprint: lem-sbc-generic-hypersurface-geometric-irreducibility-spread) -/
theorem exists_open_generic_hypersurface_geometric_irreducibility
    {S : Scheme.{u}} [IsAffine S] [IsIntegral S]
    (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤))
    (η : S) (hη : IsGenericPoint η Set.univ) :
    let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
    let g : H ⟶ S := Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
    GeometricallyIrreducible (g.fiberToSpecResidueField η) →
      GeometricallyReduced (g.fiberToSpecResidueField η) →
      ∃ U : S.Opens, η ∈ U ∧
        ∀ s, s ∈ U → GeometricallyIrreducible (g.fiberToSpecResidueField s) := by sorry

end AlgebraicGeometry
