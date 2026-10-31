/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTowerSupplement
public import WeilConjectures.AlgebraicGeometry.SfCbcExtensionZeroCompletion
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm

/-! # Finite quotient comparison before forming strict towers

Source: Stacks Project, Modules on Sites, Tag 093M (lemma-completion-flat) and
Tag 03EK (section-tensor-product); the finite part of Step 5 of
lem-sf-constant-semilinear-generator-comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.GeneratorReduction

/-- Restricting completed scalars commutes with one ordinary finite quotient.
The quotient unit remains epic after restriction and small-site transport.

Source: Stacks Project, Modules on Sites, Tag 093M (lemma-completion-flat) and
Tag 03EK (section-tensor-product); Pro-etale Cohomology, Tag 099L
(section-derived-completion-noetherian);
the finite-quotient part of Step 5 of lem-sf-constant-semilinear-generator-comparison.
(blueprint: lem-sf-constant-scalar-quotient-comparison).

Proof: put R = O_E, t its fixed uniformizer and B = completed integral coefficients.
The projection B to the constant sheaf R/(t^(n+1)) is surjective on sections:
transport to the published small site, use the completed constant algebra quotient
identification, and transport back. Scalar extension along this projection is
therefore the sheaf quotient M/t^(n+1)M. Its unit is locally surjective and hence
an epimorphism. Restriction to constant scalars leaves the underlying abelian
sheaf unchanged; the exact small-site equivalence also preserves epimorphisms.
On the other side, constant scalar extension and restriction is the same sheaf
quotient of the restricted module. Tensor reassociation gives the comparison:
it sends the class of m to the class of m. The inverse does the same in reverse;
the quotient universal property proves both inverse identities. The two scalar
units send m to the class of m, giving the displayed normalization. This formula
also proves naturality in M. This is only one quotient level: no compatibility
between distinct n, strict-tower comparison or derived comparison is asserted.
The same quotient argument covers zero modules and empty site objects. -/
theorem ordinaryScalarQuotientComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    let F := SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E T) ⋙
      sfCbcModelModules T (Padic.coefficientExtensionIntegers l E)
    let I := (Ideal.span {Padic.coefficientExtensionUniformizer l E}).map
      (ULift.ringEquiv.symm.toRingHom :
        Padic.coefficientExtensionIntegers l E →+*
          ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (∀ M : scalarReductionSource l E T,
      Epi (F.map ((scalarReductionExtension_adjunction l E T n).choose.unit.app M))) ∧
    ∃ e : sfReductionRestricted l E T n ⋙ F ≅
        F ⋙ ConstantCompletion.reduction (proEtaleModelTopology T)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) I false n,
      ∀ M : scalarReductionSource l E T,
        F.map ((scalarReductionExtension_adjunction l E T n).choose.unit.app M) ≫
          e.hom.app M =
        ((ConstantCompletion.reductionUnit (proEtaleModelTopology T)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) I false).app
            (F.obj M)).app (op n) := by sorry

end WeilConjectures.GeneratorReduction
