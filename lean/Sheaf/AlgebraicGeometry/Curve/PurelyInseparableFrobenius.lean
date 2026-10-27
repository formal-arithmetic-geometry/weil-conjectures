/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.FieldTheory.FieldTower
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.PurelyInseparable.Basic

import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Purely inseparable maps of smooth proper curves are relative Frobenius

Source: Stacks Project, Curves, Lemma 0CCZ; Varieties, Remark 0CCG
(blueprint: lem-sfb-purely-inseparable-curve-frobenius).

The twist is the actual pullback along the power endomorphism of the base field,
with its second projection as structure morphism. The two projection equations
characterize the relative Frobenius uniquely, so the factorization uses its canonical
map. The generic-point diagram likewise specifies the induced function-field map.
Unique existence of a dependent pair expresses both uniqueness assertions together.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonconstant purely inseparable map of smooth proper integral dimension-one curves
is a unique iterated relative Frobenius followed by a unique isomorphism over the base.

Source: Stacks Project, Curves, Lemma 0CCZ; Varieties, Remark 0CCG
(blueprint: lem-sfb-purely-inseparable-curve-frobenius).

Proof, following the six steps of the DAG:
1. Set L=k(X) and E=f^*k(Y). The proper-curve function-field correspondence
   (lem-sfb-proper-curve-function-field-morphisms) gives finitely generated
   transcendence-degree-one fields. The pth-root tower
   (lem-weil-pbc-purely-inseparable-pth-root-tower, Stacks 09HI) and degree
   multiplicativity (lem-weil-pbc-field-degree-multiplicativity) give a tower
   E=K_0 < ... < K_r=L with each step of degree p, and [L:E]=p^r.
2. Each intermediate K_j is finite over E and hence finitely generated over k
   with transcendence degree one. The algebraically closed curve-model theorem
   (lem-trf-algclosed-curve-model, Stacks 0BY1 and 0BY3) realizes it as the
   function field of a smooth proper integral dimension-one curve.
3. The relative-Frobenius degree theorem
   (lem-sfb-smooth-curve-relative-frobenius-degree, Stacks 0CCF and 0CCG)
   gives degree p^n. On affine charts its map is a tensor b to a^(p^n)b.
   Extracting p^n-th roots of each b in k identifies the image with the p^n-th
   powers, also after passing to fractions. In particular [K_j:K_j^p]=p.
4. The tower generators satisfy alpha_j^p in K_(j-1), so K_j^p is contained
   in K_(j-1). Both have index p in K_j; multiplicativity forces equality.
   Descending through the tower yields E=L^(p^r), including r=0.
5. For T=X^(p^r) the canonical relative Frobenius F has field image E.
   Thus (F^*)^(-1)f^* is a k-isomorphism k(Y) to k(T). The proper-curve
   correspondence realizes it and its inverse as inverse curve morphisms,
   giving h:T to Y with F followed by h equal to f.
6. Any competing exponent m has p^m=[L:E]=p^r, hence m=r since p is prime.
   For this exponent, injectivity of F^* forces the induced maps of any two
   competing isomorphisms to agree; faithfulness of the curve correspondence
   forces the isomorphisms to agree. At n=0 the base power map and absolute
   Frobenius are identities; the two projections identify F with the identity
   under the canonical identity-base-change isomorphism. -/
theorem existsUnique_purelyInseparable_curve_frobenius
    (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) (hp : p.Prime) (hk : (p : k) = 0)
    (X Y : Scheme.{u}) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsCurve sX] [IsCurve sY] [Smooth sX] [Smooth sY]
    [IsProper sX] [IsProper sY] [IsIntegral X] [IsIntegral Y]
    (hXdim : topologicalKrullDim X = 1) (hYdim : topologicalKrullDim Y = 1)
    (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (hf_nonconstant : ¬ ∃ y : Spec (.of k) ⟶ Y, y ≫ sY = 𝟙 _ ∧ sX ≫ y = f)
    (hfield : ∃ i : Y.functionField →+* X.functionField,
      Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) =
        X.fromSpecStalk (genericPoint X) ≫ f ∧
      @Module.Finite Y.functionField X.functionField _ _
        (@Algebra.toModule _ _ _ _ i.toAlgebra) ∧
      @IsPurelyInseparable Y.functionField X.functionField _ _ i.toAlgebra) :
    ∃! nh : Σ n : ℕ, pullback sX
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk n))) ≅ Y,
      nh.2.hom ≫ sY = pullback.snd sX
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk nh.1))) ∧
      ∃ (hX : (p : Γ(X, ⊤)) = 0)
        (F : X ⟶ pullback sX
          (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk nh.1)))),
        F ≫ pullback.fst sX
          (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk nh.1))) =
            X.iterateFrobenius hp hX nh.1 ∧
        F ≫ pullback.snd sX
          (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp hk nh.1))) = sX ∧
        F ≫ nh.2.hom = f := by
  sorry

end AlgebraicGeometry
