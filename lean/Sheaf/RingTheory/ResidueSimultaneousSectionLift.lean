/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Projection
import WeilConjectures.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso

/-!
# Simultaneous section lifting from the residue field

Source: Stacks Project, More on Algebra, Tag 0FJK, the final paragraph of
`lemma-homotopic-surjections` (blueprint: lem-trf-residue-simultaneous-section-lift).
The scalar-extension convention is `k ⊗[R] M`, as in `LinearMap.baseChange`;
swapping factors gives the source's `M ⊗[R] k` and its displayed formulas.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

/-- Coordinatewise quotient by the maximal ideal, for finite coordinate modules.
Source: Stacks Project, Tag 0FJK, final paragraph, expanded residue-field lift
(blueprint: lem-trf-residue-simultaneous-section-lift). -/
noncomputable def residueCoordinates (R : Type u) [CommRing R] [IsLocalRing R] (t : ℕ)
    (x : Fin t → R) : Fin t → ResidueField R :=
  fun i ↦ residue R (x i)

/-- Reduction of the matrix of a map in the standard coordinate bases.
Source: Stacks Project, Tag 0FJK, final paragraph, expanded residue-field lift
(blueprint: lem-trf-residue-simultaneous-section-lift). -/
noncomputable def residueCoordinateMap (R : Type u) [CommRing R] [IsLocalRing R]
    {m n : ℕ} (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    (Fin n → ResidueField R) →ₗ[ResidueField R] (Fin m → ResidueField R) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (residue R))

/-- Every residue-field section lifts, and a common invertible section gives a common
complement with the specified projections. No surjectivity of the original maps is
assumed: descent of surjectivity is a separate implication in the conclusion.

Source: Stacks Project, More on Algebra, Tag 0FJK, final paragraph of
`lemma-homotopic-surjections`, where the residue lift is left implicit
(blueprint: lem-trf-residue-simultaneous-section-lift).

Proof plan:
1. The maximal ideal is proper. A nonzero residue has a representative outside that
ideal, hence a unit by `lem-weil-pbc-local-ring-unit-criterion`. Thus the quotient is
a field, its maximal ideal is zero, and the quotient map is local and surjective.
2. Expand a linear map in the standard bases (`def-weil-pbc-free-module`). Reduction
commutes with its matrix formula; lift a target vector and use surjectivity upstairs
to deduce surjectivity of its reduction.
3. Lift each column of q through the coordinate quotient. Extending those columns
linearly gives s(x) = sum_j x_j v_j and its required reduction identity.
4. The tensor identification sends c tensor r to (rho(r_i)c)_i; its inverse sends
z to sum_i z_i tensor e_i. Balancing and expansion in the coordinate basis show
that these maps are inverse (`def-weil-module-base-change`).
5. Evaluate base change on pure tensors. The reduction identity for s identifies
the two extended composites, after these identifications, with a q and b q.
6. Apply `lem-sc-local-free-base-change-reflects-iso` to rho and each composite
between the finite free modules R^m. Both composites are invertible for every lift.
7. Invertibility of alpha s implies injectivity of s; its corestriction to its range
is then an isomorphism. Each restriction gamma|U is (gamma s) composed with the
inverse of that corestriction, and is therefore an isomorphism.
8. Put p(x) = (gamma|U)^(-1)(gamma(x)). Then x-p(x) is in ker gamma; the intersection
of U with that kernel is zero because the restriction is injective. This proves
the direct-sum decompositions and identifies their projections, also at rank zero.
-/
theorem residue_simultaneous_section_lift
    (R : Type u) [CommRing R] [IsLocalRing R] (m n : ℕ)
    (α β : (Fin n → R) →ₗ[R] (Fin m → R)) :
    IsField (ResidueField R) ∧
    IsLocalHom (residue R) ∧
    Ideal.comap (residue R) (maximalIdeal (ResidueField R)) = maximalIdeal R ∧
    (∀ γ : (Fin n → R) →ₗ[R] (Fin m → R), γ = α ∨ γ = β →
      Function.Surjective γ → Function.Surjective (residueCoordinateMap R γ)) ∧
    (∀ t : ℕ,
      (∀ (x : Fin t → R) (c : ResidueField R),
        TensorProduct.piScalarRight R (ResidueField R) (ResidueField R) (Fin t)
            (c ⊗ₜ[R] x) = fun i ↦ residue R (x i) * c) ∧
      (∀ z : Fin t → ResidueField R,
        (TensorProduct.piScalarRight R (ResidueField R) (ResidueField R) (Fin t)).symm z =
          ∑ i : Fin t, z i ⊗ₜ[R] (Pi.single i (1 : R)))) ∧
    ∀ q : (Fin m → ResidueField R) →ₗ[ResidueField R] (Fin n → ResidueField R),
      (∃ s : (Fin m → R) →ₗ[R] (Fin n → R),
        ∀ x, residueCoordinates R n (s x) = q (residueCoordinates R m x)) ∧
      (∀ v : Fin m → (Fin n → R),
        (∀ j, residueCoordinates R n (v j) = q (Pi.single j 1)) →
        (∀ x, residueCoordinates R n ((Pi.basisFun R (Fin m)).constr R v x) =
          q (residueCoordinates R m x)) ∧
        (∀ x, (Pi.basisFun R (Fin m)).constr R v x = ∑ j : Fin m, x j • v j)) ∧
      (∀ s : (Fin m → R) →ₗ[R] (Fin n → R),
        (∀ x, residueCoordinates R n (s x) = q (residueCoordinates R m x)) →
        (∀ γ : (Fin n → R) →ₗ[R] (Fin m → R), γ = α ∨ γ = β →
          (TensorProduct.piScalarRight R (ResidueField R) (ResidueField R) (Fin m)).toLinearMap
              ∘ₗ (γ.comp s).baseChange (ResidueField R) ∘ₗ
                (TensorProduct.piScalarRight R (ResidueField R)
                  (ResidueField R) (Fin m)).symm.toLinearMap =
            (residueCoordinateMap R γ).comp q) ∧
        (Function.Bijective ((residueCoordinateMap R α).comp q) →
          Function.Bijective ((residueCoordinateMap R β).comp q) →
          Function.Bijective (α.comp s) ∧ Function.Bijective (β.comp s) ∧
          Function.Injective s ∧
          ∃ e : (Fin m → R) ≃ₗ[R] LinearMap.range s,
            e.toLinearMap = s.rangeRestrict ∧
            ∀ γ : (Fin n → R) →ₗ[R] (Fin m → R), γ = α ∨ γ = β →
              ∃ g : LinearMap.range s ≃ₗ[R] (Fin m → R),
                g.toLinearMap = γ.comp (LinearMap.range s).subtype ∧
                ∃ h : IsCompl (LinearMap.ker γ) (LinearMap.range s),
                  ∀ x : Fin n → R,
                    (LinearMap.range s).projectionOnto (LinearMap.ker γ) h.symm x =
                      g.symm (γ x))) := by
  sorry

end IsLocalRing
