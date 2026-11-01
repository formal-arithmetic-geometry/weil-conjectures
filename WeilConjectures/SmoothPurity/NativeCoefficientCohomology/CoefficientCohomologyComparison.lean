/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantPurityFrobenius.ConstantPurityFrobeniusSquare
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.ExceptionalCoefficientRealization
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.RealizedTateCohomology
import WeilConjectures.SmoothPurity.NativePairCohomology.NativePairHomologyComparison

/-! # Cohomology comparison between coefficient pairs and native Weil sheaves

Cohomology is constructed from ordinary derived pairs. The two endpoint calculations
are performed before the final restriction to constructible Weil sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius
namespace WeilConjectures.NativeCoefficientCohomology
variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

variable [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]

attribute [local instance] nativeStructureOver

-- The original universal adjunction binder is intentionally unused in its conclusion.
set_option linter.unusedVariables false in
/-- Cohomology of ordinary coefficient Frobenius pairs has a native Weil-sheaf model.
The same functors work in every degree, for every native exceptional adjoint, and for
all nonnegative Tate powers. No smoothness or geometric purity is asserted here.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, exceptional
adjunction paragraph; cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md,
constant-unit identification; lem-pur-constant-purity-frobenius-square, canonical
Tate-source convention.
(blueprint: lem-sf-native-coefficient-cohomology-comparison)

Proof: realize a common-stage complex as an ordinary complex of modules over the
continuous, finite-extension-valued coefficient sheaf. Use the normalized section-module
equivalence and change of algebraic closure to put it on the native geometric fibre.
The realization comparisons for geometric Frobenius transport a coefficient fixed pair
to a fixed pair of ordinary derived objects. Apply degree n cohomology. Exactness of
Frobenius pullback gives its cohomology commutation isomorphism, so this is a pair of
sheaves, functorially on every intertwining morphism. Realization preserves bounded
constructibility; thus these sheaf pairs lie in the full subcategory WeilSheaf. This
constructs the functors C, without identifying the native derived category with fixed
pairs of derived objects.

For the exceptional endpoint, apply the counit-normalized native exceptional-forgetting
comparison and its scalar-unit normalization at the constant point object. Transport the
native counit's equivariance through the normalized compact-support comparison. The
ordinary adjunction hom-equivalence uniquely determines the transported action: transpose
the counit equation to obtain the inverse-exchange right mate followed by G(theta_0).
The scalar Frobenius counit theorem gives exactly that mate and its invariant counit.
Take cohomology of this comparison; exact forgetting computes the native cohomology and
hence gives the first family of Weil-sheaf isomorphisms, in every degree.

For the other endpoint, pullback takes the scalar unit to the scalar unit. The normalized
root-line realization identifies its d-th Tate power with the native Tate sheaf, including
its cyclotomic Frobenius; tensor normalization adds the native constant factor. Exact
realization takes the even shift to the shift by 2d. Its degree -2d cohomology is therefore
the native Tate sheaf tensor the constant sheaf. All maps respect the root, tensor-unit
and shift comparisons used in canonicalSourceTheta. This proves the second family.
The construction is valid at d=0 and on the empty scheme; neither part uses smoothness.
-/
theorem coefficient_cohomology_comparison :
    ∃ C : ℤ → (Pairs P X₀ ⥤ WeilSheaf P.field.k₀ P.coefficients.l X₀.left),
      (∀ (J : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
          WeilComplex P.field.k₀ P.coefficients.l X₀.left)
        (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J)
        (n : ℤ),
        Nonempty ((WeilComplex.homologySheaf n).obj
            (J.obj (WeilSheaf.toComplex.obj
              (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
                (Spec (.of P.field.k₀))))) ≅
          (C n).obj (exceptionalConstant P X₀ c₀ S))) ∧
      (∀ d : ℕ, Nonempty ((C (-2 * (d : ℤ))).obj (twistedConstant P X₀ d) ≅
        (WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d).tensorObj
          (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)
          (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d))) := by
  obtain ⟨R, hR⟩ := exceptional_realization P X₀ c₀ S
  refine ⟨fun n ↦ CoefficientRealization.cohomology P X₀ R n, ?_, ?_⟩
  · intro J adj n
    obtain ⟨e⟩ := hR J adj
    obtain ⟨h⟩ := NativePairCohomology.native_homology P.field.k₀ P.coefficients.l X₀.left
      (J.obj (WeilSheaf.toComplex.obj
        (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
          (Spec (.of P.field.k₀))))) n
    exact ⟨ObjectProperty.isoMk _
      (h ≪≫ (NativePairCohomology.homology P.field.k₀ P.coefficients.l X₀.left n).mapIso e)⟩
  · intro d
    obtain ⟨e⟩ := realized_tate_cohomology P X₀ R d
    exact ⟨ObjectProperty.isoMk _ e⟩

end WeilConjectures.NativeCoefficientCohomology
