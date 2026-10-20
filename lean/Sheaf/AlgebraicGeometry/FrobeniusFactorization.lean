/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.SixFunctors.SchemeFrobenius
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius

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

set_option backward.isDefEq.respectTransparency false in
private theorem iterateFrobenius_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
    X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change f.app U ≫ (X.iterateFrobenius hp hX n).app (f ⁻¹ᵁ U) ≫
    X.presheaf.map (𝟙 _) =
      (Y.iterateFrobenius hp hY n).app U ≫ f.app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change ((f.app U).hom s) ^ p ^ n = (f.app U).hom (s ^ p ^ n)
  exact (map_pow (f.app U).hom s _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem iterateFrobenius_add (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (n r : ℕ) :
    X.iterateFrobenius hp hX (n + r) =
      X.iterateFrobenius hp hX n ≫ X.iterateFrobenius hp hX r := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change (X.iterateFrobenius hp hX (n + r)).app U ≫ X.presheaf.map (𝟙 _) =
    (X.iterateFrobenius hp hX r).app U ≫ (X.iterateFrobenius hp hX n).app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change s ^ p ^ (n + r) = (s ^ p ^ r) ^ p ^ n
  rw [← pow_mul, pow_add, Nat.mul_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem iterateFrobenius_zero (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : X.iterateFrobenius hp hX 0 = 𝟙 X := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  change (X.iterateFrobenius hp hX 0).app U ≫ X.presheaf.map (𝟙 _) = 𝟙 _
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change s ^ p ^ 0 = s
  simp

private theorem iterateFrobenius_mul (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (a m : ℕ) :
    X.iterateFrobenius hp hX (a * m) = (End.of (X.iterateFrobenius hp hX a)) ^ m := by
  induction m with
  | zero => simp [iterateFrobenius_zero, End.one_def]
  | succ m ih =>
    rw [Nat.mul_succ, iterateFrobenius_add, ih, pow_succ, End.mul_def]
    exact (Commute.self_pow (End.of (X.iterateFrobenius hp hX a)) m).eq

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
  classical
  let := Fintype.ofFinite D.k₀
  have _ := hm
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let X := (D.geometricFiber X₀).left
  let π := pullback.fst X₀.hom b
  let s := pullback.snd X₀.hom b
  let hX := D.model_characteristic (π ≫ X₀.hom)
  let F : End X := X.iterateFrobenius D.prime hX D.a
  let P : End X := D.schemeFrobenius X₀
  let S : End X := D.arithmeticGaloisFrobenius X₀
  let σ := (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
  have hσ : σ = FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k := by
    simp [σ, FiniteField.geometricFrobeniusAlgEquivOfAlgebraic, AlgEquiv.aut_inv]
  have hFₖ : (Spec (CommRingCat.of D.k)).iterateFrobenius D.prime
      (D.model_characteristic b) D.a = Spec.map (CommRingCat.ofHom σ.toRingHom) := by
    apply AlgebraicGeometry.ext_to_Spec
    change (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
        ((Spec (CommRingCat.of D.k)).iterateFrobenius D.prime
          (D.model_characteristic b) D.a).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
        (Spec.map (CommRingCat.ofHom σ.toRingHom)).appTop
    rw [← Scheme.ΓSpecIso_inv_naturality]
    ext x
    change ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv x) ^ D.p ^ D.a =
      (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv (σ x)
    rw [hσ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← map_pow,
      ← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq]
  have hP₁ : P ≫ π = π ≫
      X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a :=
    (D.relativeFrobenius_projections X₀).1
  have hP₂ : P ≫ s = s := (D.relativeFrobenius_projections X₀).2
  have hS₁ : S ≫ π = π := (D.galoisMap_projections X₀.hom σ).1
  have hS₂ : S ≫ s = s ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
    (D.galoisMap_projections X₀.hom σ).2
  have hF₁ : F ≫ π = π ≫
      X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a :=
    iterateFrobenius_naturality π D.prime hX (D.model_characteristic X₀.hom) D.a
  have hF₂ : F ≫ s = s ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
    rw [← hFₖ]
    exact iterateFrobenius_naturality s D.prime hX (D.model_characteristic b) D.a
  have hPS : F = P ≫ S := by
    apply pullback.hom_ext
    · rw [Category.assoc, hS₁, hP₁, hF₁]
    · rw [Category.assoc, hS₂, ← Category.assoc, hP₂, hF₂]
  have hSP : F = S ≫ P := by
    apply pullback.hom_ext
    · rw [Category.assoc, hP₁, ← Category.assoc, hS₁, hF₁]
    · rw [Category.assoc, hP₂, hS₂, hF₂]
  have hcomm : Commute P S := by
    change S ≫ P = P ≫ S
    exact hSP.symm.trans hPS
  have hpow : X.iterateFrobenius D.prime hX (D.a * m) = F ^ m :=
    iterateFrobenius_mul X D.prime hX D.a m
  change X.iterateFrobenius D.prime hX (D.a * m) = (P ^ m) ≫ (S ^ m) ∧
    X.iterateFrobenius D.prime hX (D.a * m) = (S ^ m) ≫ (P ^ m)
  rw [hpow]
  constructor
  · change F ^ m = S ^ m * P ^ m
    rw [show F = S * P from hPS, hcomm.symm.mul_pow]
  · change F ^ m = P ^ m * S ^ m
    rw [show F = P * S from hSP, hcomm.mul_pow]

end WeilConjectures.FiniteFieldDatum
