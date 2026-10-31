/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
public import WeilConjectures.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable

import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Frobenius and separable factors of a nonconstant curve morphism

Source: Stacks Project, Curves, Proposition 0CD2 and Theorem 0BY1;
Fields, Lemma 030K; Varieties, Definition relative-frobenius and
Remark n-fold-relative-frobenius
(blueprint: lem-sfb-curve-frobenius-separable-factorization).

The function-field embedding is specified by its canonical generic-point diagram.
Its algebra structure is the one induced by that embedding, rather than a freely chosen
extension. In positive characteristic the intermediate curve is the actual pullback along
the power endomorphism of k, with the second projection as structure morphism. The first
projection of F is absolute Frobenius, which, together with its structure morphism,
characterizes relative Frobenius by the pullback universal property. On an affine chart
these two projections give the tensor map a tensor b to a^(p^n)b.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonconstant map of smooth proper geometrically integral dimension-one curves factors
as relative Frobenius followed by a map inducing a finite separable function-field extension.
In characteristic zero the intermediate curve and maps are exactly C, its identity, and u.

Source: Stacks Project, Curves, Proposition 0CD2, Theorem 0BY1 and Lemma 0CCZ;
Fields, Lemma 030K; Varieties, Definition relative-frobenius and
Remark n-fold-relative-frobenius
(blueprint: lem-sfb-curve-frobenius-separable-factorization).

Proof plan, following the six steps of the DAG node:
1. By lem-sfb-proper-curve-function-field-morphisms, u gives a finite extension
   L/K, where K=k(D) and L=k(C); both fields are finitely generated of transcendence
   degree one over k. Morphisms are determined by their induced field embeddings.
2. Apply lem-weil-pbc-separable-first-purely-inseparable (Stacks 030K) to obtain
   the separable algebraic closure E of K in L. Then E/K is separable and L/E is
   purely inseparable. In characteristic zero E=L, so take C'=C, F=id and v=u.
3. E is finite over K as a K-subspace of L, and L/E is finite because a finite
   K-spanning set also spans over E. A finite basis for E/K together with field
   generators for K/k generates E/k. Its transcendence degree is one, since a
   transcendental element of K remains transcendental and L is algebraic over k(t).
4. Apply lem-trf-algclosed-curve-model to E to obtain a smooth proper integral
   dimension-one curve Z. By lem-sfb-proper-curve-function-field-morphisms the two
   embeddings give a:C to Z and b:Z to D, with u=b composed with a; a induces L/E
   and b induces E/K. Equality follows from the injectivity of the correspondence.
5. Apply lem-sfb-purely-inseparable-curve-frobenius (Stacks 0CCZ) to a. It gives
   n and a k-isomorphism h:C^(p^n) to Z with a=h composed with relative Frobenius.
   Take C'=C^(p^n), F=relative Frobenius and v=b composed with h. Transporting the
   function-field embedding along h preserves finiteness and separability.
6. After any field extension the twist is the base change of C along the composite
   k to k to k', hence integral by geometric integrality of C. The first projection
   of F acts by a to a^(p^n), and its second projection is the structure map.
   The affine tensor-product universal property therefore gives a tensor b to
   a^(p^n)b; the relation (ca) tensor b = a tensor c^(p^n)b is respected. At n=0
   this is multiplication, the identity under the canonical identity-base-change
   isomorphism. Smoothness, properness and dimension one are stable under this
   base change (or transported through h), completing all the assertions. -/
theorem exists_curve_frobenius_separable_factorization
    (k : Type u) [Field k] [IsAlgClosed k]
    (C D : Scheme.{u}) (sC : C ⟶ Spec (.of k)) (sD : D ⟶ Spec (.of k))
    [IsCurve sC] [IsCurve sD] [Smooth sC] [Smooth sD]
    [IsProper sC] [IsProper sD] [GeometricallyIntegral sC] [GeometricallyIntegral sD]
    [IsIntegral C] [IsIntegral D]
    (hCdim : topologicalKrullDim C = 1) (hDdim : topologicalKrullDim D = 1)
    (u : C ⟶ D) (hu : u ≫ sD = sC)
    (hu_nonconstant : ¬ ∃ y : Spec (.of k) ⟶ D, y ≫ sD = 𝟙 _ ∧ sC ≫ y = u) :
    ∃ (C' : Scheme.{u}) (s' : C' ⟶ Spec (.of k)) (_ : IsIntegral C')
      (F : C ⟶ C') (v : C' ⟶ D),
      IsCurve s' ∧ Smooth s' ∧ IsProper s' ∧ GeometricallyIntegral s' ∧
      topologicalKrullDim C' = 1 ∧
      F ≫ s' = sC ∧ v ≫ sD = s' ∧ F ≫ v = u ∧
      (¬ ∃ y : Spec (.of k) ⟶ D, y ≫ sD = 𝟙 _ ∧ s' ≫ y = v) ∧
      (∃ i : D.functionField →+* C'.functionField,
        Spec.map (CommRingCat.ofHom i) ≫ D.fromSpecStalk (genericPoint D) =
          C'.fromSpecStalk (genericPoint C') ≫ v ∧
        @Module.Finite D.functionField C'.functionField _ _
          (@Algebra.toModule _ _ _ _ i.toAlgebra) ∧
        @Algebra.IsSeparable D.functionField C'.functionField _ _ i.toAlgebra) ∧
      (CharZero k → C' = C ∧ HEq s' sC ∧ HEq F (𝟙 C) ∧ HEq v u) ∧
      ∀ (p : ℕ) (hp : p.Prime) (hk : (p : k) = 0),
        ∃ (n : ℕ) (hC : (p : Γ(C, ⊤)) = 0)
          (e : C' = pullback sC
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n)))),
          s' = eqToHom e ≫ pullback.snd sC
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) ∧
          F ≫ eqToHom e ≫ pullback.fst sC
            (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) =
              C.iterateFrobenius hp hC n := by
  sorry

end AlgebraicGeometry
