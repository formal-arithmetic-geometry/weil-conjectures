/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Equivariant reduction of algebraic constants over a henselian local ring

Source: Stacks Project, algebra.tex, Tags 04GH and 00GN; the constant-field comparison
in main-20261015, sec-purity-real-sheaves/sk-d-real-boundary/d-real-boundary.md.
(blueprint: lem-real-henselian-residue-galois-action)
-/

@[expose] public section

universe u v w z

namespace HenselianLocalRing

/-- Equivariant reduction identifies the algebraic constants with the algebraic closure of the
finite residue field. Source: Stacks Project, Tags 04GH and 00GN, applied to the decomposition
homomorphism in main-20261015, d-real-boundary.
(blueprint: lem-real-henselian-residue-galois-action)

Proof: (1) Each finite subset of the integral closure generates a finite R-algebra, by
lem-sc-finite-generated-integral-subring. (2) This algebra is a domain inside Omega. The
finite product decomposition of lem-weil-pbc-finite-over-henselian-local-product therefore
has precisely one nonzero factor; it is local over R. (3) For every integral b, either b or
1-b is a unit in that finite subalgebra and hence in B; thus B is local. (4) Integrality and
lem-weil-pbc-integral-maximal-contracts-maximal identify the contraction of its maximal
ideal with that of R. (5) lem-a1-integral-residue-extension-algebraic makes the residue
extension algebraic. (6) Lift a nonconstant monic residue polynomial to B and choose a root
in Omega. Its adjoining algebra is finite by lem-sc-finite-generated-integral-subring,
hence integral by lem-weil-pbc-finite-algebra-is-integral; transitivity
(lem-weil-pbc-integral-transitive) places the root in B. Its reduction is the required root,
so the residue field is algebraically closed. (7) Every K-automorphism fixes R, preserves
integrality, and hence restricts to B and preserves its unique maximal ideal. Reduction
then gives the displayed group homomorphism. (8) A finite set of residues has finitely
many integral lifts; their pointwise stabilizer is Krull-open and lies in the inverse
image of the residue stabilizer, proving continuity. (9) Algebraic constants are integral
over k0, hence over R, so their inclusion factors through B. The relative algebraic
closure is algebraically closed by lem-weil-pbc-relative-algebraic-closure-algclosed.
The residue field is algebraic over k0, since its intermediate field kappa is finite.
Thus the injective reduction on the constant field is surjective by
lem-weil-pbc-algebraic-over-algebraically-closed-subfield. (10) Its equivariance is the
reduction formula applied to constants.

The universal instance binders expose the local structures asserted immediately before
them; they add no assumptions to the theorem. The maps a, c, r and t are characterized
on every element by the displayed formulas, so they are the restrictions and reduction
maps of the statement. The last existential gives the restriction of sigma to constants
pointwise, together with its commuting-square formula. -/
theorem exists_residue_galois_action
    (k0 : Type u) [Field k0] [Finite k0]
    (R : Type v) [CommRing R] [HenselianLocalRing R] [Algebra k0 R]
    [Finite (IsLocalRing.ResidueField R)]
    (K : Type w) [Field K] [Algebra k0 K] [Algebra R K] [IsScalarTower k0 R K]
    (Ω : Type z) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra R Ω] [Algebra k0 Ω] [IsScalarTower R K Ω]
    [IsScalarTower k0 K Ω] [IsScalarTower k0 R Ω] :
    IsLocalRing (integralClosure R Ω) ∧
      ∀ [IsLocalRing (integralClosure R Ω)],
        Ideal.comap (algebraMap R (integralClosure R Ω))
            (IsLocalRing.maximalIdeal (integralClosure R Ω)) = IsLocalRing.maximalIdeal R ∧
        IsLocalHom (algebraMap R (integralClosure R Ω)) ∧
        ∀ [IsLocalHom (algebraMap R (integralClosure R Ω))],
          IsAlgClosure (IsLocalRing.ResidueField R)
              (IsLocalRing.ResidueField (integralClosure R Ω)) ∧
          ∃ (a : (Ω ≃ₐ[K] Ω) →* (integralClosure R Ω ≃ₐ[R] integralClosure R Ω)),
            (∀ (σ : Ω ≃ₐ[K] Ω) (b : integralClosure R Ω),
              ((a σ b : integralClosure R Ω) : Ω) = σ (b : Ω)) ∧
            (∀ σ : Ω ≃ₐ[K] Ω,
              Ideal.comap (a σ).toRingHom
                (IsLocalRing.maximalIdeal (integralClosure R Ω)) =
                  IsLocalRing.maximalIdeal (integralClosure R Ω)) ∧
            ∃ (r : (Ω ≃ₐ[K] Ω) →*
                (IsLocalRing.ResidueField (integralClosure R Ω) ≃ₐ[IsLocalRing.ResidueField R]
                  IsLocalRing.ResidueField (integralClosure R Ω))),
              Continuous r ∧
              (∀ (σ : Ω ≃ₐ[K] Ω) (b : integralClosure R Ω),
                r σ (IsLocalRing.residue (integralClosure R Ω) b) =
                  IsLocalRing.residue (integralClosure R Ω) (a σ b)) ∧
              ∃ (c : algebraicClosure k0 Ω →ₐ[k0] integralClosure R Ω),
                (∀ x : algebraicClosure k0 Ω, (c x : Ω) = (x : Ω)) ∧
                ∃ (t : algebraicClosure k0 Ω ≃ₐ[k0]
                    IsLocalRing.ResidueField (integralClosure R Ω)),
                  (∀ x : algebraicClosure k0 Ω,
                    t x = IsLocalRing.residue (integralClosure R Ω) (c x)) ∧
                  ∀ (σ : Ω ≃ₐ[K] Ω) (x : algebraicClosure k0 Ω),
                    ∃ y : algebraicClosure k0 Ω,
                      (y : Ω) = σ (x : Ω) ∧ t y = r σ (t x) := by
  sorry

end HenselianLocalRing
