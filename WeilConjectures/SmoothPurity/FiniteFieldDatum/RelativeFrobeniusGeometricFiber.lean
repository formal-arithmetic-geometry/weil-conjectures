/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
import Mathlib.Algebra.CharP.CharAndCard

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
    (D.p : Γ(X, ⊤)) = 0 := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let φ := (Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ f.appTop
  simpa only [map_natCast, map_zero] using
    congrArg φ.hom (CharP.cast_eq_zero D.k₀ D.p)

/-- The q-power absolute Frobenius of the model is a morphism over the finite base.
Source: Deligne, Weil II (1.1.14), p. 153; Stacks, Tag 0CC7
(blueprint: def-weil-relative-frobenius-geometric-fiber).
Proof: absolute Frobenius is natural in a scheme morphism, by the naturality of taking
p^a-th powers on sections. On Spec k₀ it is the identity because c^q = c in k₀.
Use q = p^a to conclude that its composite with f is f. -/
theorem model_frobenius_over (D : WeilConjectures.FiniteFieldDatum.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k₀)) :
    X.iterateFrobenius D.prime (D.model_characteristic f) D.a ≫ f = f := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  apply AlgebraicGeometry.ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫
      (X.iterateFrobenius D.prime (D.model_characteristic f) D.a ≫ f).appTop = _
  rw [Scheme.Hom.comp_appTop]
  ext x
  change (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv x)) ^
    D.p ^ D.a = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv x)
  rw [← D.cardinality_eq, ← D.card_base, Nat.card_eq_fintype_card, ← map_pow,
    ← map_pow, FiniteField.pow_card]

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
    D.relativeFrobenius Y₀ ≫ (D.geometricFiber Y₀).hom = (D.geometricFiber Y₀).hom := by
  constructor
  · simp [relativeFrobenius, Over.pullback_map_left]
  · exact ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
      (Over.homMk (Y₀.left.iterateFrobenius D.prime
        (D.model_characteristic Y₀.hom) D.a) (D.model_frobenius_over Y₀.hom))).w

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
          (AlgHom.id D.k₀ D.k)).toRingHom) := by
  have : QuasiCompact
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A)))).hom :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A))))
  have hF : (Spec (CommRingCat.of A)).iterateFrobenius D.prime
      (D.model_characteristic (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A)))) D.a =
      Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom D.k₀ A).toRingHom) := by
    apply AlgebraicGeometry.ext_to_Spec
    change (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        ((Spec (CommRingCat.of A)).iterateFrobenius D.prime
          (D.model_characteristic (Spec.map
            (CommRingCat.ofHom (algebraMap D.k₀ A)))) D.a).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec.map (CommRingCat.ofHom
          (FiniteField.frobeniusAlgHom D.k₀ A).toRingHom)).appTop
    rw [← Scheme.ΓSpecIso_inv_naturality]
    ext x
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv x) ^ D.p ^ D.a =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (FiniteField.frobeniusAlgHom D.k₀ A x)
    rw [FiniteField.frobeniusAlgHom_apply, ← map_pow, ← Nat.card_eq_fintype_card,
      D.card_base, D.cardinality_eq]
  rw [← cancel_mono (pullbackSpecIso D.k₀ A D.k).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · erw [Category.assoc, (D.relativeFrobenius_projections
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A))))).1,
      pullbackSpecIso_inv_fst_assoc, hF]
    rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · simp only [Category.assoc, pullbackSpecIso_inv_snd]
    erw [show D.relativeFrobenius
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A)))) ≫
        pullback.snd _ _ = pullback.snd _ _ from
      (D.relativeFrobenius_projections _).2]
    erw [pullbackSpecIso_inv_snd D.k₀ A D.k, ← Spec.map_comp]
    congr 1
    ext x
    simp

end WeilConjectures.FiniteFieldDatum
