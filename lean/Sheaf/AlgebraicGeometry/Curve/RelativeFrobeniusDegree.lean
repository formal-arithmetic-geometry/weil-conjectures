/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Dimension.Free
import Sheaf.AlgebraicGeometry.Curve.ProperFunctionFieldMorphisms
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import WeilConjectures.FieldTheory.ExistsPBasis
import WeilConjectures.FieldTheory.PBasisDifferentialsBasis

/-!
# The degree of relative Frobenius on a smooth proper curve

Source: Stacks Project, Varieties, Tags 0CCF and 0CCG; Curves, Tag 0CCY,
first paragraph of the proof
(blueprint: lem-sfb-smooth-curve-relative-frobenius-degree).

The twist is the actual pullback along the power endomorphism of the base field,
with its second projection as structure map. Unique existence with both projection
identities specifies the canonical relative Frobenius, including the zeroth iterate.
The function-field embedding is the existing generic stalk map, and its degree uses
`FieldExtension.degree`, which distinguishes infinite extensions from degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The Frobenius twist of a smooth proper integral dimension-one curve is another such
curve, and its n-fold relative Frobenius is nonconstant of function-field degree p^n.
The prime p with p = 0 in the field is exactly its positive characteristic.
The witness of integrality supplies the field structure on the twist's generic stalk.
The two projection identities uniquely determine F; at n = 0 the first projection is
an isomorphism and identifies F with the identity of C.

Source: Stacks Project, Varieties, Tags 0CCF and 0CCG; Curves, Tag 0CCY
(blueprint: lem-sfb-smooth-curve-relative-frobenius-degree).

Proof, following the six steps of the node:
1. The algebraically closed base field is perfect, so every power map a -> a^(p^n)
   is an automorphism, including n = 0. The smooth integral dimension-one curve
   is smooth of relative dimension one by the equidimensional-fibre criterion.
2. Smoothness and properness persist under base change. The first projection of
   the twist is an isomorphism, with inverse (id_C, Spec(phi_n)^(-1) composed with sC).
   Hence the twist is integral and of dimension one as well as a smooth proper curve.
3. Pull p = 0 back to global sections of C. Naturality of absolute Frobenius gives
   the unique lift F of (F_C^n, sC) to the pullback. Since absolute Frobenius is the
   identity on points and the first projection is an isomorphism, F is a homeomorphism.
   It is nonconstant, since a surjective map from a dimension-one curve cannot factor
   through a rational point. On generic stalks, F^* composed with the first projection's
   field isomorphism sends x to x^(p^n), so its image is K^(p^n), where K = k(C).
4. Smooth differentials have rank one near the generic point. The affine fraction-field
   description and localization of differentials give dim_K Omega_(K/k) = 1.
5. Since k is perfect, k is contained in K^p. An absolute p-basis of K therefore gives
   a basis of Omega_(K/k). Its index set has one element, and its restricted monomials
   form a p-element basis of K over K^p. Thus [K : K^p] = p.
6. Frobenius identifies K^(p^i) over K^(p^(i+1)) with K over K^p. Each successive
   degree is p, so field-degree multiplicativity and induction give [K : K^(p^n)] = p^n.
   For n = 0 both power maps are identities; the projection equations identify F
   with the identity under the canonical identity-base-change isomorphism. -/
theorem smooth_proper_curve_relative_frobenius_degree
    (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) (hp : p.Prime) (hk : (p : k) = 0)
    (C : Scheme.{u}) (sC : C ⟶ Spec (.of k))
    [IsCurve sC] [Smooth sC] [IsProper sC] [IsIntegral C]
    (hCdim : topologicalKrullDim C = 1) (n : ℕ) :
    ∃ (_ : IsIntegral (pullback sC
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))))),
      IsCurve (pullback.snd sC
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n)))) ∧
      Smooth (pullback.snd sC
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n)))) ∧
      IsProper (pullback.snd sC
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n)))) ∧
      topologicalKrullDim (pullback sC
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) : Scheme.{u}) = 1 ∧
      ∃ hC : (p : Γ(C, ⊤)) = 0,
        ∃! F : C ⟶ pullback sC
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))),
          F ≫ pullback.fst sC
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) =
              C.iterateFrobenius hp hC n ∧
          F ≫ pullback.snd sC
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) = sC ∧
          (¬ ∃ y : Spec (.of k) ⟶ pullback sC
              (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))),
            y ≫ pullback.snd sC
              (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) = 𝟙 _ ∧
            sC ≫ y = F) ∧
          ∃ hη : F (genericPoint C) = genericPoint (pullback sC
              (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) : Scheme.{u}),
            Function.Injective (F.functionFieldMap hη).hom ∧
            @FieldExtension.degree
              (pullback sC
                (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n)))).functionField
              C.functionField _ _ (F.functionFieldMap hη).hom.toAlgebra =
                ((p ^ n : ℕ) : WithTop ℕ) := by
  sorry

end AlgebraicGeometry
