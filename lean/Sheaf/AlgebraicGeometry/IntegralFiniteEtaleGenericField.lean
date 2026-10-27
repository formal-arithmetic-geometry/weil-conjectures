/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.TraceFormula.LocalDimensionFormula
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The generic field of an integral finite étale cover

Source: Stacks Project, Morphisms, Tags 02GL(2), 01RV; Algebra, Tags 00CP, 00DK;
Schemes, Tags 01I4 and 01JR (blueprint: lem-sfb-integral-finite-etale-generic-field).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry

/-- A surjective finite étale map between integral schemes induces a finite separable
extension of their actual generic stalks. Its generic fibre is canonically the spectrum
of the upstairs function field, with both projections specified. Every nonempty affine
chart gives the same identification by the tensor and fraction formulas below.

The existential algebra structures are fixed by equalities to the actual stalk map and
section map; they are included as data to bind the scalar structures explicitly.
The localization is Mathlib's `LocalizedModule A⁰ B`, with its commutative ring structure.
The ring equivalences together with their equations on the structural maps are precisely
F-algebra equivalences. No choice of affine coordinates enters the global isomorphism.

Source: Stacks Project, Morphisms, Tags 02GL(2), 01RV; Algebra, Tags 00CP, 00DK;
Schemes, Tags 01I4 and 01JR (blueprint: lem-sfb-integral-finite-etale-generic-field).

Proof:
1. For each nonempty affine V, finiteness makes W=f⁻¹V affine and B finite over A.
Surjectivity makes W nonempty. Apply lem-sc-integral-function-field-affine-fraction
on V and W to identify F and L with their fraction fields via the germ maps.
2. A prime of B above (0) exists by surjectivity, so A→B is injective and the generic
point maps to the generic point. The generic stalk map of
 def-sfb-dominant-function-field-map sends g_X(a)/g_X(s) to g_Z(φ(a))/g_Z(φ(s)).
3. Apply lem-a1-etale-open-restriction and
lem-weil-pbc-etale-algebra-residue-field-separable at the zero primes. This makes the
particular generic stalk extension finite separable.
4. The fraction map C=S⁻¹B→L is injective. Localized finite A-module generators span
C over F. By lem-weil-pbc-finite-dimensional-domain-is-field, C is a field.
The universal property lem-weil-pbc-ring-localization-universal-property now extends
B→C to L→C; both composites fix every fraction, giving C≅L.
5. By lem-weil-pbc-algebra-tensor-pushout-universal-property and the localization
universal property, b⊗(a/s)↦φ(a)b/s and b/s↦b⊗(1/s) are inverse ring maps.
Their equations on F make them F-algebra maps.
6. By lem-weil-pbc-residue-field-point-naturality the generic point maps commute
with f and Spec of the field map. By lem-weil-pbc-spec-residue-field-identification
they factor on affine charts as spectra of the germs. Use
lem-weil-pbc-open-preimage-fibre-product and lem-weil-pbc-fibre-product-affine-spectra:
the induced map from Spec L to the pullback is Spec of the composite in steps 4–5,
hence an isomorphism. Its projections are the generic map and Spec of the field map.
7. Pullback uniqueness makes this isomorphism unique and independent of V.
The displayed fraction formulas and germ restriction identity give compatibility
on every smaller nonempty open, hence on overlaps by an affine refinement.
-/
theorem integral_finite_etale_generic_field
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : Z ⟶ X) [IsFinite f] [Etale f] [Surjective f] :
    ∃ (a : Algebra X.functionField Z.functionField),
      a = (f.functionFieldMap f.apply_genericPoint_of_flat).hom.toAlgebra ∧
      FiniteDimensional X.functionField Z.functionField ∧
      Algebra.IsSeparable X.functionField Z.functionField ∧
      (∃! e : Spec Z.functionField ≅ pullback f X.fromSpecFunctionField,
        e.hom ≫ pullback.fst f X.fromSpecFunctionField = Z.fromSpecFunctionField ∧
        e.hom ≫ pullback.snd f X.fromSpecFunctionField =
          Spec.map (CommRingCat.ofHom (algebraMap X.functionField Z.functionField))) ∧
      ∀ (V : X.Opens) (_ : IsAffineOpen V) (_ : Nonempty V),
        ∃ (_ : Nonempty (f ⁻¹ᵁ V)),
          IsAffineOpen (f ⁻¹ᵁ V) ∧
          Function.Injective (f.app V) ∧
          IsFractionRing Γ(X, V) X.functionField ∧
          IsFractionRing Γ(Z, f ⁻¹ᵁ V) Z.functionField ∧
          ∃ (ab : Algebra Γ(X, V) Γ(Z, f ⁻¹ᵁ V)),
            ab = (f.app V).hom.toAlgebra ∧
            ∃ (c : X.functionField →+* LocalizedModule Γ(X, V)⁰ Γ(Z, f ⁻¹ᵁ V))
              (α : (Γ(Z, f ⁻¹ᵁ V) ⊗[Γ(X, V)] X.functionField) ≃+*
                LocalizedModule Γ(X, V)⁰ Γ(Z, f ⁻¹ᵁ V))
              (β : LocalizedModule Γ(X, V)⁰ Γ(Z, f ⁻¹ᵁ V) ≃+* Z.functionField),
              (∀ t : X.functionField, α (1 ⊗ₜ[Γ(X, V)] t) = c t) ∧
              (∀ t : X.functionField, β (c t) = algebraMap X.functionField Z.functionField t) ∧
              (∀ (b : Γ(Z, f ⁻¹ᵁ V)) (r : Γ(X, V)) (s : Γ(X, V)⁰),
                α (b ⊗ₜ[Γ(X, V)]
                    (X.germToFunctionField V r / X.germToFunctionField V s)) =
                  LocalizedModule.mk ((f.app V r) * b) s) ∧
              (∀ (b : Γ(Z, f ⁻¹ᵁ V)) (s : Γ(X, V)⁰),
                β (LocalizedModule.mk b s) =
                  Z.germToFunctionField (f ⁻¹ᵁ V) b /
                    Z.germToFunctionField (f ⁻¹ᵁ V) (f.app V s)) ∧
              (∀ (b : Γ(Z, f ⁻¹ᵁ V)) (t : X.functionField),
                β (α (b ⊗ₜ[Γ(X, V)] t)) =
                  Z.germToFunctionField (f ⁻¹ᵁ V) b *
                    algebraMap X.functionField Z.functionField t) ∧
              (∀ (W : Z.Opens) (hW : W ≤ f ⁻¹ᵁ V) (_ : Nonempty W)
                  (b : Γ(Z, f ⁻¹ᵁ V)) (s : Γ(X, V)⁰),
                β (LocalizedModule.mk b s) =
                  Z.germToFunctionField W (Z.presheaf.map (homOfLE hW).op b) /
                    Z.germToFunctionField W
                      (Z.presheaf.map (homOfLE hW).op (f.app V s))) := by
  sorry

end AlgebraicGeometry
