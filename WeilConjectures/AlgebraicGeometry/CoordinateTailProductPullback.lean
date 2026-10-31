/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSuccessorCup
import WeilConjectures.AlgebraicGeometry.CoordinateTailCoefficientPullback
import WeilConjectures.AlgebraicGeometry.SupportedKummerBoundaryPullback
import all Mathlib.Logic.Small.Defs

/-! # Pulling back the old factors in a successor coordinate product

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

-- Use the same cached ordinary Ext instances as the normalized Cartier family.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem ordinaryBoundary_normalized (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c) :
    Etale.SupportedKummerBoundary (setting P n).Coefficient
      (P.coefficients.l ^ (n + 1 + 1)) (annihilates (setting P n))
      (inclusion B c i) (coordinate_cartier B c i)
      (by simpa only [Nat.cast_pow] using
        (AffineLinePurity.primeUnit (setting P n) (iteratedAffineLine B c)
          (towerBase aB c)).pow (n + 1 + 1))
      (ordinaryBoundary P n B aB c i) := by
  have h := (Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose_spec.1
  unfold Etale.CartierEtaleKummerNormalization at h
  unfold ordinaryBoundary
  dsimp only [setting, PurityFiniteSetting.Coefficient, PurityFiniteSetting.Ring,
    PurityFiniteSetting.coefficientCommRing, PurityFiniteSetting.ringCommRing]
  with_unfolding_all
    exact h n (n + 1) (annihilates (setting P n)) (inclusion B c i)
      (coordinate_cartier B c i)
      (AffineLinePurity.primeUnit (setting P n) (iteratedAffineLine B c) (towerBase aB c))

/-- The actual ordinary coordinate boundaries satisfy Cartier pullback, with any
root-normalized finite twist transport and any specified Cartesian divisor square.
Source: the Cartier naturality step of the ordered coordinate product.
(blueprint: lem-pur-coordinate-tail-product-pullback).
Proof: the simultaneous ordinary Cartier family is normalized by the relative
Kummer boundary at every coordinate and every allowed exponent. Apply the
supported Kummer pullback theorem to these two normalized boundary classes.
The equality of the invertibility witnesses is proof irrelevance. -/
theorem ordinaryBoundary_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c)
    (B' : Scheme.{u}) (aB' : B' ⟶ Spec (.of P.field.k)) (c' : ℕ) (i' : Fin c')
    (v : iteratedAffineLine B' c' ⟶ iteratedAffineLine B c)
    (w : divisor B' c' i' ⟶ divisor B c i)
    (sq : IsPullback w (inclusion B' c' i') (inclusion B c i) v)
    (t : Etale.OrdinaryFiniteTwistTransport (setting P n).Coefficient
      (P.coefficients.l ^ (n + 1 + 1)) (annihilates (setting P n))) :
    (CategoryTheory.Abelian.Ext.mk₀
      (Etale.supportedConstantExchange (setting P n).Coefficient
        (inclusion B c i) (inclusion B' c' i') v w sq.toCommSq)).comp
      (ordinaryBoundary P n B' aB' c' i') (zero_add 2) =
      ((ordinaryBoundary P n B aB c i).mapExactFunctor
        (Etale.upperStar (ModuleCat.{u + 1} (setting P n).Coefficient) v)).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (t.line v (by simpa only [Nat.cast_pow] using
            (AffineLinePurity.primeUnit (setting P n) (iteratedAffineLine B c)
              (towerBase aB c)).pow (n + 1 + 1))).hom) (add_zero 2) := by
  exact Etale.supported_kummer_boundary_pullback (iteratedAffineLine B c)
    (P.coefficients.l ^ (n + 1 + 1))
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
    (setting P n).Coefficient (annihilates (setting P n))
    (by simpa only [Nat.cast_pow] using
      (AffineLinePurity.primeUnit (setting P n) (iteratedAffineLine B c)
        (towerBase aB c)).pow (n + 1 + 1))
    (inclusion B c i) (coordinate_cartier B c i) (ordinaryBoundary P n B aB c i)
    (ordinaryBoundary_normalized P n B aB c i) t
    (inclusion B' c' i') v w sq (coordinate_cartier B' c' i')
    (ordinaryBoundary P n B' aB' c' i') (ordinaryBoundary_normalized P n B' aB' c' i')

private theorem append_normalized {C : Type*} [Category C]
    {W X Y Z U : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : W ⟶ Z)
    (e : Z ⟶ U) (h : a ≫ b ≫ c = d) : a ≫ b ≫ c ≫ e = d ≫ e := by
  rw [← Category.assoc b c e, ← Category.assoc a (b ≫ c) e, h]

private theorem transport_normalized {C : Type*} [Category C]
    {W X Y Z : C} (f : W ⟶ X) (h : X = Y) (k : Y = Z) :
    (f ≫ eqToHom h) ≫ eqToHom k = f ≫ eqToHom (h.trans k) := by
  subst Y
  subst Z
  simp only [eqToHom_refl, Category.comp_id]

private theorem tailProduct_nil (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    product P n B aB c [] = tailProductUnit P n B c := by
  unfold product coordinateProductFold tailProductUnit
  rfl

private theorem tailProduct_cons_normalized (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (i : Fin c) (is : List (Fin c)) (m : ℕ) (h : is.length = m) :
    product P n B aB c (i :: is) ≫
        eqToHom (congrArg (target P n (iteratedAffineLine B c))
          (congrArg (fun k ↦ k + 1) h)) =
      tailProductStep P n B aB c i is m
        (product P n B aB c is ≫
          eqToHom (congrArg (target P n (iteratedAffineLine B c)) h))
        (boundary P n B aB c i) := by
  subst m
  simp only [eqToHom_refl, Category.comp_id]
  unfold product coordinateProductFold tailProductStep
  dsimp only
  with_unfolding_all rw [cupZero_tensor]

/-- The old-coordinate tail is the pullback of the product in one lower rank.
Source: the ordered exterior product sentence of the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-tail-product-pullback).

Proof: for every old coordinate i, the function with index i.succ is the pullback
of the function with index i along lastProjection. Its zero subscheme square is
Cartesian, by base change of zero loci of sections. The old coordinate remains
Cartier over the polynomial base, and after killing the other old coordinates.
Use successorDivisor_isPullback and the proved ordinaryBoundary_pullback for the
actual normalized ordinary coordinate boundary at the chosen annihilating exponent.
Then realize that equation by the
exact site comparison.
The root-line comparisons are the prescribed pullback comparisons, since both
are normalized by their action on roots. Induct over the old coordinate list.
At the empty list, the constant-unit map is preserved by the exact pullback and
its canonical unit comparison. For a cons, monoidality carries the tensor of the
two maps to the tensor of their images; naturality of the localization tensor
comparison and normalized closed-constant multiplication identifies the inverse
coefficient maps. The even shifted-line pullback comparison identifies the
output with the next ordered target power. Thus the pulled-back list product is
the product on the successor-index list. At the full old list its Cartesian
support square is successorTailSquare: the two maps into the chosen pullback
agree on both projections, hence coincide. Its constant restriction-normalized
coefficient exchange is consequently successorTailSourcePullback. The successive
target comparisons are precisely targetPullbackIso by its actionPullbackIso
recursion. Normalize the list length by length_map and length_finRange. This
proves the displayed equation without the last coordinate factor or any compact
projection formula, including r=0, empty bases and zero coefficients. -/
theorem coordinate_tail_product_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    (successorTailSourcePullback P n B r).inv ≫
      (inverseImage (setting P n).Coefficient (lastProjection B r)).map
        (supportedClass P n B aB r) ≫
      (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r).hom =
        successorTailProduct P n B aB r := by
  obtain ⟨hunit, hstep, hsource⟩ := coordinate_tail_coefficient_pullback P n B aB r
  have hrec (is : List (Fin r)) :
      (tailPartialSourcePullback P n B r is).inv ≫
          (inverseImage (setting P n).Coefficient (lastProjection B r)).map
            (product P n B aB r is) ≫
          (targetPullbackIso P n (lastProjection B r) (towerBase aB r)
            is.length).hom =
        product P n B aB (r + 1) (is.map Fin.succ) ≫
          eqToHom (congrArg (target P n (iteratedAffineLine B (r + 1)))
            (List.length_map Fin.succ)) := by
    induction is with
    | nil =>
      change (tailPartialSourcePullback P n B r []).inv ≫
        (inverseImage (setting P n).Coefficient (lastProjection B r)).map
          (product P n B aB r []) ≫
        (targetPullbackIso P n (lastProjection B r) (towerBase aB r) 0).hom =
          product P n B aB (r + 1) [] ≫ 𝟙 _
      rw [tailProduct_nil, tailProduct_nil, Category.comp_id]
      exact hunit
    | cons i is ih =>
      have h := hstep i is is.length (product P n B aB r is) (boundary P n B aB r i)
      have ho := tailProduct_cons_normalized P n B aB r i is is.length rfl
      simp only [eqToHom_refl, Category.comp_id] at ho
      have hmap := congrArg (fun f ↦
        (tailPartialSourcePullback P n B r (i :: is)).inv ≫
          (inverseImage (setting P n).Coefficient (lastProjection B r)).map f ≫
          (targetPullbackIso P n (lastProjection B r) (towerBase aB r)
            (is.length + 1)).hom) ho
      have hinputs := congrArg₂
        (tailProductStep P n B aB (r + 1) i.succ (is.map Fin.succ) is.length)
        ih (coordinate_tail_factorwise_pullback P n B aB r i)
      exact hmap.trans (h.trans (hinputs.trans
        (tailProduct_cons_normalized P n B aB (r + 1) i.succ
          (is.map Fin.succ) is.length (List.length_map Fin.succ)).symm))
  have h := append_normalized
    (tailPartialSourcePullback P n B r (List.finRange r)).inv
    ((inverseImage (setting P n).Coefficient (lastProjection B r)).map
      (product P n B aB r (List.finRange r)))
    (targetPullbackIso P n (lastProjection B r) (towerBase aB r)
      (List.finRange r).length).hom _
    (eqToHom (congrArg (target P n (iteratedAffineLine B (r + 1)))
      (@List.length_finRange r))) (hrec (List.finRange r))
  exact hsource.trans (h.trans (transport_normalized
    (product P n B aB (r + 1) ((List.finRange r).map Fin.succ))
    (congrArg (target P n (iteratedAffineLine B (r + 1))) (List.length_map Fin.succ))
    (congrArg (target P n (iteratedAffineLine B (r + 1))) (@List.length_finRange r))))

end AlgebraicGeometry.ProEtale.AffineZeroPurity
