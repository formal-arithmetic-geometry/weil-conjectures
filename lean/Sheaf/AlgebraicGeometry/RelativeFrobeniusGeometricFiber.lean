/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius

/-!
# Relative Frobenius on a geometric fibre

Source: Deligne, Weil II (1.1.14), p. 153; Stacks, Tags 03SM and 0CC7
(blueprint: def-weil-relative-frobenius-geometric-fiber).

The absolute q-power Frobenius of the model is linear over the finite base field.
Applying the existing base-change functor defines its base change to the fixed closure.
## Main definitions

- `relativeFrobenius`: base change of the absolute q-power Frobenius of the model.

-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- The characteristic of the finite base vanishes on every scheme over that base.
Source: Deligne, Weil II (1.1.14), p. 153; Stacks, Tag 03SM
(blueprint: def-weil-relative-frobenius-geometric-fiber).
Proof: the base has cardinality p^a with a positive, hence characteristic p.
The structure morphism induces a unital map from the base field to global sections,
which takes the equality p = 0 to the asserted equality. This also covers the zero ring. -/
theorem model_characteristic (D : WeilConjectures.FiniteFieldDatum.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k₀)) :
    (D.p : Γ(X, ⊤)) = 0 :=
  sorry

/-- The q-power absolute Frobenius of the model is a morphism over the finite base.
Source: Deligne, Weil II (1.1.14), p. 153; Stacks, Tag 0CC7
(blueprint: def-weil-relative-frobenius-geometric-fiber).
Proof: absolute Frobenius is natural in a scheme morphism, by the naturality of taking
p^a-th powers on sections. On Spec k₀ it is the identity because c^q = c in k₀.
Use q = p^a to conclude that its composite with f is f. -/
theorem model_frobenius_over (D : WeilConjectures.FiniteFieldDatum.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k₀)) :
    X.iterateFrobenius D.prime (D.model_characteristic f) D.a ≫ f = f :=
  sorry

/-- Base change of the q-power absolute Frobenius of the model, with its actual morphism
as data. Its source and target are the geometric fibre from the recorded dependency.
Source: Deligne, Weil II (1.1.14), p. 153
(blueprint: def-weil-relative-frobenius-geometric-fiber). -/
noncomputable def relativeFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    (D.geometricFiber Y₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    (Over.homMk (Y₀.left.iterateFrobenius D.prime (D.model_characteristic Y₀.hom) D.a)
      (D.model_frobenius_over Y₀.hom))).left

/-- The relative Frobenius has the prescribed two projections, so is a k-morphism.
Source: Deligne, Weil II (1.1.14), p. 153
(blueprint: def-weil-relative-frobenius-geometric-fiber).
Proof: the map is the image under Over.pullback of the model Frobenius. The two defining
projection identities of that functor give the displayed equalities. On an affine chart,
Spec reverses the tensor factors' ring maps: a tensor b goes to a^q tensor b. -/
theorem relativeFrobenius_projections (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    D.relativeFrobenius Y₀ ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        Y₀.left.iterateFrobenius D.prime (D.model_characteristic Y₀.hom) D.a ∧
    D.relativeFrobenius Y₀ ≫ (D.geometricFiber Y₀).hom = (D.geometricFiber Y₀).hom :=
  sorry

/-- On an affine model, relative Frobenius is Spec of a tensor b ↦ a^q tensor b.
The Fintype argument only chooses an enumeration of the already finite base field.
Source: Deligne, Weil II (1.1.14), p. 153
(blueprint: def-weil-relative-frobenius-geometric-fiber).
Proof: identify the affine fibre product with Spec of the tensor product. Its projections
are the two tensor inclusions. Base change applies q-th powers on the first factor and
the identity on the second. The universal property of the tensor product identifies its
ring homomorphism with the displayed tensor map. -/
theorem relativeFrobenius_affine (D : WeilConjectures.FiniteFieldDatum.{u})
    [Fintype D.k₀] (A : Type u) [CommRing A] [Algebra D.k₀ A]
    [LocallyOfFiniteType
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A)))).hom] :
    (pullbackSpecIso D.k₀ A D.k).inv ≫
        @relativeFrobenius D
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A)))) inferInstance
          (inferInstanceAs (QuasiCompact (Spec.map
            (CommRingCat.ofHom (algebraMap D.k₀ A))))) ≫
        (pullbackSpecIso D.k₀ A D.k).hom =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (FiniteField.frobeniusAlgHom D.k₀ A)
          (AlgHom.id D.k₀ D.k)).toRingHom) :=
  sorry

end WeilConjectures.FiniteFieldDatum
