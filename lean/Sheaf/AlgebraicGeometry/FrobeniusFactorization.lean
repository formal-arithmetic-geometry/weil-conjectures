/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.SixFunctors.SchemeFrobenius
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Factorization of the absolute Frobenius

Source: Weil conjectures blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, order 2416
(blueprint: prop-trf-frobenius-factorization).

The absolute q^m-power map is the p^(a*m)-power map, since q = p^a.
The two factors are the recorded scalar-extended scheme Frobenius and arithmetic
Galois Frobenius. Equality is stated on underlying scheme morphisms: the forgetful
functor from schemes over Spec k₀ is faithful, so this is also their equality over k₀.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- Absolute q^m-power Frobenius factors, in either order, into the m-fold scheme
Frobenius and m-fold arithmetic Galois Frobenius on the geometric fibre.
Source: blueprint main-20261015, order 2416
(blueprint: prop-trf-frobenius-factorization).

Proof:
1. Cover the model by affine charts Spec A₀ and the fibre by their base changes
   Spec (A₀ ⊗[k₀] k). The recorded scheme Frobenius acts by
   P(u ⊗ b) = u^q ⊗ b, and arithmetic Galois Frobenius by
   S(u ⊗ b) = u ⊗ b^q (def-trf-scheme-frobenius). Both preserve these charts:
   the first is identity on model points and the second lies over the model identity
   (def-weil-absolute-frobenius-scheme). Induction on m, starting with the identity,
   gives P^m(u ⊗ b) = u^(q^m) ⊗ b and S^m(u ⊗ b) = u ⊗ b^(q^m).
2. Both composite ring maps give u^(q^m) ⊗ b^(q^m) on a pure tensor, which is its
   q^m-th power. This power map is a ring homomorphism since q^m = p^(a*m)
   (def-weil-ring-frobenius). Every tensor is a finite sum of pure tensors, with scalars
   absorbed in one factor (def-weil-pbc-module-tensor-product); additivity gives equality
   on the entire ring, including nilpotents.
3. Absolute Frobenius restricts to Spec of this power map
   (def-weil-absolute-frobenius-scheme). Contravariance and uniqueness of affine
   spectrum morphisms (def-weil-affine-spectrum) identify it with both composites
   on every chart. The continuous maps agree on this cover, and the maps of structure
   sheaves agree locally, hence globally by sheaf uniqueness. These are the data of
   a scheme morphism (def-weil-locally-ringed-space-morphism). All maps are over k₀,
   so the equality is also an equality of k₀-scheme morphisms. -/
theorem absoluteFrobenius_factorization (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) (hm : 1 ≤ m) :
    (D.geometricFiber X₀).left.iterateFrobenius D.prime
        (D.model_characteristic
          (pullback.fst X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom)) (D.a * m) =
      D.schemeFrobeniusIterate X₀ m ≫
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.arithmeticGaloisFrobenius X₀) m) ∧
    (D.geometricFiber X₀).left.iterateFrobenius D.prime
        (D.model_characteristic
          (pullback.fst X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom)) (D.a * m) =
      (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.arithmeticGaloisFrobenius X₀) m) ≫
        D.schemeFrobeniusIterate X₀ m := by
  sorry

end WeilConjectures.FiniteFieldDatum
