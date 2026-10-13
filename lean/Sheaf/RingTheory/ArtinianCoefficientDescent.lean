/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.RingTheory.ArtinianCoefficientPresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Descent of Artinian presentations to finite coefficient fields

Source: Stacks Project, Tag 07FG, the final presentation and flatness paragraphs
(blueprint: lem-weil-pbc-artinian-coefficient-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- After adjoining finitely many relation coefficients, every further finite enlargement
of the coefficient field gives a flat Artinian local subalgebra essentially of finite type.
This algebraic descent statement assumes a section and the coefficient containment, and
requires neither a characteristic assumption nor cotangent homology.

Source: Stacks Project, Tag 07FG, the final paragraph (steps 8--11 of the parent node)
(blueprint: lem-weil-pbc-artinian-coefficient-descent).

Proof:
1. Put K=ResidueField Lambda. The section sigma and the generators t give a surjection
   Psi:K[t] -> Lambda: modulo m every element is a coefficient, and successive substitution
   of t leaves a remainder in m^r, eventually zero. Its kernel has finitely many generators
   by the Hilbert basis theorem. Adjoin all their coefficients to those already in c,
   obtaining a finite set c0 containing c.
2. For any finite s containing c0, let F=k(s). The algebra B_F=F[t]/(g_1,...,g_r) base
   changes over F to Lambda over K, by tensor-quotient base change. Field extension is
   faithfully flat, so B_F -> Lambda is injective and flat. Its image is the ring generated
   by sigma(F) and t. The containment hypothesis, and c subset s, show that this image
   contains algebraMap(k); hence it equals artinianCoefficientSubalgebra k Lambda sigma t s.
3. The variables are nilpotent together: m^n=0 implies all degree n monomials vanish in
   Lambda, hence in the injectively embedded B_F. Thus B_F is a quotient of F[t]/(t)^n and
   is finite dimensional over F, so Artinian. Its elements are sigma(a)+h with a in F and
   h in the nilpotent ideal (t). The residue map identifies this quotient with F. If a is
   nonzero, the element is a unit by a finite geometric series; if a=0 it is nilpotent.
   Consequently (t) is its maximal ideal. Its extension to Lambda is m by the span hypothesis.
4. The residue field is F=k(s), finitely generated as a field over k and therefore
   essentially of finite type. Apply Tag 07DT (3), the Artinian local residue criterion,
   to conclude that the image subalgebra is essentially of finite type over k. -/
theorem exists_artinian_coefficient_descent
    (k : Type u) [Field k] (Λ : Type v) [CommRing Λ] [Algebra k Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ]
    (σ : IsLocalRing.ResidueField Λ →+* Λ) (t : Finset Λ)
    (c : Finset (IsLocalRing.ResidueField Λ))
    (hσ : (IsLocalRing.residue Λ).comp σ = RingHom.id _)
    (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (hc : ∀ a : k, algebraMap k Λ a ∈ Subring.closure ((t : Set Λ) ∪
      σ '' (IntermediateField.adjoin k (c : Set (IsLocalRing.ResidueField Λ)) :
        Set (IsLocalRing.ResidueField Λ)))) :
    ∃ c0 : Finset (IsLocalRing.ResidueField Λ), c ⊆ c0 ∧
      ∀ s : Finset (IsLocalRing.ResidueField Λ), c0 ⊆ s →
        ∃ hA : IsLocalRing (artinianCoefficientSubalgebra k Λ σ t s),
          IsArtinianRing (artinianCoefficientSubalgebra k Λ σ t s) ∧
          RingHom.Flat (artinianCoefficientSubalgebra k Λ σ t s).val.toRingHom ∧
          Ideal.map (artinianCoefficientSubalgebra k Λ σ t s).val.toRingHom
            (@IsLocalRing.maximalIdeal (artinianCoefficientSubalgebra k Λ σ t s) _ hA) =
              IsLocalRing.maximalIdeal Λ ∧
          EssFiniteType k (artinianCoefficientSubalgebra k Λ σ t s) := by sorry

end Algebra
