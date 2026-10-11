/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.SchemeTangentSpace
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Rational tangent vectors and cotangent functionals

Source: Stacks Project, Tags 0B2D and 0B2E, with base `Spec k`
(blueprint: lem-sc-rational-point-tangent-derivation-identification).
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- At a rational point, extraction of the epsilon coefficient of the stalk homomorphism
identifies tangent vectors with the dual of the cotangent space. The map `r` is the structural
map from `k` to the residue field; its bijectivity expresses rationality. Scalar structures
are restricted along `r`. The displayed dual-number formula uses residue-field coordinates,
so that the coefficient `D a : k` appears as `r (D a)`.
Source: Stacks Project, Tags 0B2D and 0B2E
(blueprint: lem-sc-rational-point-tangent-derivation-identification).

Proof:
1. The closed-point condition implies that the stalk homomorphism reduces to the residue
   map, using the Spec-local-ring correspondence and composition of stalk maps
   (lem-weil-pbc-morphism-from-spec-local-ring, lem-weil-pbc-scheme-stalk-map-composition).
   Unique dual-number coordinates give `D`; additivity and multiplication give additivity
   and the residue-valued Leibniz identity. The base-morphism condition makes `D` vanish on k.
2. The Leibniz identity makes `D` vanish on products of maximal-ideal elements, hence on
   their square ideal. It descends to the quotient, additively and k-linearly.
3. A functional on the cotangent space recovers `D a` by applying it to the class of
   `a` minus its structural-field residue. Expanding products proves the Leibniz identity,
   giving a local k-algebra map into dual numbers. The Spec-local-ring correspondence
   recovers a unique tangent vector. Scaling epsilon scales coefficients, and the pushout
   addition of def-sc-scheme-tangent-space adds them. Thus this bijection is k-linear. -/
theorem exists_rationalPoint_tangent_cotangent_linearEquiv
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X) :
    let R := X.presheaf.stalk x
    let K := X.residueField x
    let r : k →+* K :=
      (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom
    Function.Bijective r →
    letI : Module k (schemeTangentSpace k X p x) :=
      Module.compHom (schemeTangentSpace k X p x) r
    letI : Module K (IsLocalRing.CotangentSpace R) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
    letI : Module k (IsLocalRing.CotangentSpace R) :=
      Module.compHom (IsLocalRing.CotangentSpace R) r
    ∃ e : schemeTangentSpace k X p x ≃ₗ[k] (IsLocalRing.CotangentSpace R →ₗ[k] k),
      ∀ θ : schemeTangentSpace k X p x,
        ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x,
          let sharp : R →+* DualNumber K :=
            (eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
              Scheme.stalkClosedPointTo θ.val).hom
          ∃! D : R → k,
            (∀ a : R, sharp a =
              TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (r (D a))) ∧
            (∀ a : IsLocalRing.maximalIdeal R,
              e θ ((IsLocalRing.maximalIdeal R).toCotangent a) = D a) := by
  sorry

end AlgebraicGeometry
