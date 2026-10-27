/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Sheaf.AlgebraicGeometry.Curve.AutomorphismTwistCurveLift

/-!
# The function-field image of iterated relative Frobenius

Source: Stacks Project, Varieties, Tag 0CCG (the defining projection formula), and
Curves, Tag 0CCY (the Frobenius image field)
(blueprint: lem-sfb-relative-frobenius-function-field-image).

The twist is the actual scheme pullback along the power endomorphism of the base
field. Its structure morphism is the second projection. The two projection equations
specify relative Frobenius uniquely. The induced field embedding is the existing
map of generic stalks, and its range is compared with the set of actual powers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- On a smooth proper integral dimension-one curve over an algebraically closed
field of positive characteristic, the image of n-fold relative Frobenius on function
fields is exactly the set of p^n-th powers. Primality and vanishing of p in k express
positive characteristic. Integrality of the twist and its generic-point equality
supply the canonical generic-stalk map, rather than an arbitrary field embedding.
At n = 0 the first projection is the canonical identification and carries F to id_C.

Source: Stacks Project, Varieties, Tag 0CCG; Curves, Tag 0CCY
(blueprint: lem-sfb-relative-frobenius-function-field-image).

Proof, following the four steps of the node:
1. Put q = p^n. The power endomorphism of k is injective since k is a field and
   q is positive. Every b has a q-th root, by algebraic closedness applied to Z^q-b.
   Thus the power endomorphism is an automorphism, also for n = 0.
2. Pull p = 0 back along the structure morphism to the global sections of C.
   Absolute Frobenius is the identity on points, and naturality of ring Frobenius
   gives the compatibility of F_C^n with Spec of the base-field power map. Apply
   lem-sfb-automorphism-twist-curve-lift: the twist is integral, its first projection
   is an isomorphism, and the unique lift F has precisely the prescribed projections.
   It preserves the generic point and its generic-stalk pullback is injective.
   If beta is the first projection's field isomorphism, F^* composed with beta is
   the generic-stalk pullback of F_C^n.
3. Represent x in k(C) by a germ of a section g near the generic point. Absolute
   Frobenius fixes that point and sends g to g^p. Iteration therefore sends x to
   x^(p^n), including the identity at n = 0 (def-sc-function-field and
   def-weil-absolute-frobenius-scheme).
4. Surjectivity of beta writes every element of k(T) as beta(x). Its F-pullback
   is x^(p^n), proving one inclusion of ranges; every such power is F^*(beta(x)),
   proving the reverse inclusion. At n = 0 the identity-base-change clause of
   lem-sfb-automorphism-twist-curve-lift identifies F with the identity via the
   first projection. -/
theorem relative_frobenius_function_field_image
    (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) (hp : p.Prime) (hk : (p : k) = 0)
    (C : Scheme.{u}) (a : C ⟶ Spec (.of k))
    [IsCurve a] [Smooth a] [IsProper a] [IsIntegral C]
    (hCdim : topologicalKrullDim C = 1) (n : ℕ) :
    ∃ (_ : IsIntegral (pullback a
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))))),
      ∃ hC : (p : Γ(C, ⊤)) = 0,
        ∃! F : C ⟶ pullback a
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))),
          F ≫ pullback.fst a
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) =
              C.iterateFrobenius hp hC n ∧
          F ≫ pullback.snd a
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) = a ∧
          (n = 0 →
            IsIso (pullback.fst a
              (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n)))) ∧
            F ≫ pullback.fst a
              (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) = 𝟙 C) ∧
          ∃ hη : F (genericPoint C) = genericPoint (pullback a
              (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) : Scheme.{u}),
            Function.Injective (F.functionFieldMap hη).hom ∧
            Set.range (F.functionFieldMap hη).hom =
              Set.range (fun x : C.functionField ↦ x ^ (p ^ n)) := by
  sorry

end AlgebraicGeometry
