/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.Mathlib.AlgebraicGeometry.Birational.RationalMap
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Extending a function-field embedding from a smooth connected curve

Source: Stacks Project, Curves, Tag 0BY1, third proof paragraph; Morphisms, Tag 0BX7
(blueprint: lem-sfb-smooth-curve-embedding-extension).

The integral instance of the source curve is supplied in the conclusion, so the function
field is its actual generic stalk without an additional integrality hypothesis. Compatibility
of the field embedding with the base field is expressed by its canonical spectrum diagram.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Every k-embedding k(Y) → k(C) extends to a k-morphism C → Y when C is a smooth
connected curve over an algebraically closed field and Y is an integral proper k-scheme.
The generic stalk map is the given embedding; the generic-point diagram, affine
factorization, and fraction formula hold. Neither properness of C nor smoothness or
one-dimensionality of Y is required.

Source: Stacks Project, Curves, Tag 0BY1, third proof paragraph, and Tag 0BXY;
Morphisms, Tag 0BX7 (blueprint: lem-sfb-smooth-curve-embedding-extension).

Proof:
1. By lem-sc-smooth-connected-curve-local-rings, C is integral and its stalks are either
   its function field or DVRs. They are valuation rings: for a nonzero fraction u t^n,
   n ≥ 0 puts the fraction in the DVR and n < 0 puts its inverse there.
2. Set h = Spec(φ) followed by the canonical generic-point morphism of Y. The displayed
   compatibility is exactly that h is over k. On any nonempty affine V, the generic germ
   j embeds Γ(Y,V) in k(Y), by lem-sc-integral-function-field-affine-fraction. The affine
   description in lem-weil-pbc-spec-local-ring-canonical-morphism identifies h with
   Spec(j ≫ φ) followed by V → Y, using contravariance of Spec.
3. Apply lem-sfb-valuation-stalk-proper-target-extension to obtain F over k whose composite
   with the generic-point morphism of C is h.
4. Evaluate this identity at the sole point of Spec k(C): the canonical local-spectrum
   morphisms send it to the generic points. Their generic stalk maps are identities by
   lem-weil-pbc-spec-local-ring-canonical-morphism, while the stalk map of Spec(φ) is φ
   by lem-weil-pbc-spec-map-stalk-localization at the zero prime. Thus F sends η_C to η_Y
   and induces φ on their stalks. The affine factorization from step 2 gives the stated
   equality for each V. A homomorphism of fields preserves division, so the generic
   stalk map sends a/b to φ(a)/φ(b), including zero numerators and inseparable embeddings.
-/
theorem exists_hom_of_smooth_connected_curve_functionField_embedding
    (k : Type u) [Field k] [IsAlgClosed k] (C Y : Scheme.{u})
    [C.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsConnectedCurve (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [IsIntegral Y] [IsProper (Y ↘ Spec (.of k))] :
    ∃ hC : IsIntegral C, ∀ (φ : Y.functionField →+* C.functionField),
      Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecFunctionField ≫ (Y ↘ Spec (.of k)) =
          C.fromSpecFunctionField ≫ (C ↘ Spec (.of k)) →
      ∃ (F : C ⟶ Y) (hη : F (genericPoint C) = genericPoint Y),
        F.IsOver (Spec (.of k)) ∧
        (Y.presheaf.stalkSpecializes (specializes_of_eq hη) ≫ F.stalkMap (genericPoint C)) =
          CommRingCat.ofHom φ ∧
        C.fromSpecFunctionField ≫ F =
          Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecFunctionField ∧
        (∀ (V : Y.Opens) (hV : IsAffineOpen V) (_ : Nonempty V),
          Spec.map (Y.germToFunctionField V ≫ CommRingCat.ofHom φ) ≫ hV.fromSpec =
            C.fromSpecFunctionField ≫ F) ∧
        (∀ (a b : Y.functionField), b ≠ 0 →
          (Y.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
              F.stalkMap (genericPoint C)) (a / b) = φ a / φ b) := by
  sorry

end AlgebraicGeometry.Scheme
