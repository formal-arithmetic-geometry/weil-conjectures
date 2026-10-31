/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorSupport
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroCupTensor

/-! # One binary cup in the successor coordinate product

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered coordinate product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The successor coordinate list has the new coordinate at its head.
Source: the ordered coordinate product.
(blueprint: lem-pur-coordinate-successor-product-fold).
Proof: finRange is ofFn of the identity. The cons formula for ofFn leaves the
successor function on the smaller finite range. -/
theorem successorTailList_cons (r : ℕ) :
    List.finRange (r + 1) = (0 : Fin (r + 1)) :: successorTailList r := by
  change List.ofFn id = _
  rw [List.ofFn_succ]
  congr 1
  exact List.ofFn_eq_map

/-- Normalize only the length of the old-coordinate tail product.
Source: ordered coordinate product
(blueprint: lem-pur-coordinate-successor-product-fold). -/
def successorTailProduct (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    classSource P n B (r + 1) (successorTailList r) ⟶
      target P n (iteratedAffineLine B (r + 1)) r :=
  product P n B aB (r + 1) (successorTailList r) ≫
    eqToHom (congrArg (target P n (iteratedAffineLine B (r + 1)))
      ((List.length_map ..).trans (@List.length_finRange r)))

/-- Cup an arbitrary class on the old-coordinate support with the last Cartier boundary,
then transport the actual intersection to the zero section. No projection formula
or exceptional adjunction is used in this construction.
Source: ordered coordinate product
(blueprint: lem-pur-coordinate-successor-product-fold). -/
def successorCup (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ)
    (α : classSource P n B (r + 1) (successorTailList r) ⟶
      target P n (iteratedAffineLine B (r + 1)) r) :
    (cupSingle (setting P n) (iteratedAffineLine B (r + 1))).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B (r + 1))).obj
        ((setting P n).constant B)) ⟶
      target P n (iteratedAffineLine B (r + 1)) (r + 1) :=
  coordinateSupportedCompose
    ((cupSingle (setting P n) (iteratedAffineLine B (r + 1))).map
      ((setting P n).functorialCupSupportMap true (zero B (r + 1))
        (supportMap B (r + 1) (List.finRange (r + 1))) (supportIso B (r + 1)).hom
        (supportIso_existsUnique B (r + 1)).exists.choose_spec))
    (classSource_eq P n B (r + 1) (List.finRange (r + 1))).symm
    (eqToHom (congrArg (classSource P n B (r + 1)) (successorTailList_cons r)) ≫
      coordinateProductStart (classSource_cons P n B (r + 1) 0 (successorTailList r))
        (zeroCupTensor (setting P n)
          (supportMap B (r + 1) (successorTailList r)) (inclusion B (r + 1) 0)
          ⟨target P n (iteratedAffineLine B (r + 1)) r,
            target_plus P n _ (towerBase aB (r + 1)) r⟩
          ⟨shiftedLine (setting P n) (iteratedAffineLine B (r + 1)), boundary_plus P n _⟩
          (coordinateProductStart (classSource_eq P n B (r + 1)
            (successorTailList r)).symm α)
          (boundary P n B aB (r + 1) 0)))
    (target_succ P n (iteratedAffineLine B (r + 1)) r)

private theorem product_reindex_normalized (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (is js : List (Fin c)) (h : is = js) (m : ℕ) (hi : is.length = m)
    (hj : js.length = m) :
    product P n B aB c is ≫
        eqToHom (congrArg (target P n (iteratedAffineLine B c)) hi) =
      eqToHom (congrArg (classSource P n B c) h) ≫ product P n B aB c js ≫
        eqToHom (congrArg (target P n (iteratedAffineLine B c)) hj) := by
  subst js
  rw [eqToHom_refl, Category.id_comp]

private theorem product_cons_normalized (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (i : Fin c) (is : List (Fin c)) (m : ℕ) (h : is.length = m) :
    product P n B aB c (i :: is) ≫
        eqToHom (congrArg (target P n (iteratedAffineLine B c))
          (congrArg (fun k ↦ k + 1) h)) =
      coordinateProductStart (classSource_cons P n B c i is)
        (cupZero (setting P n) (towerBase aB c) (supportMap B c is) (inclusion B c i)
          ⟨target P n (iteratedAffineLine B c) m,
            target_plus P n _ (towerBase aB c) m⟩
          ⟨shiftedLine (setting P n) (iteratedAffineLine B c), boundary_plus P n _⟩
          (coordinateProductStart (classSource_eq P n B c is).symm
            (product P n B aB c is ≫
              eqToHom (congrArg (target P n (iteratedAffineLine B c)) h)))
          (boundary P n B aB c i)) ≫
        eqToHom (target_succ P n (iteratedAffineLine B c) m) := by
  subst m
  simp only [eqToHom_refl, Category.comp_id]
  unfold product coordinateProductFold coordinateProductTransport coordinateProductStart
  simp only [Category.assoc]

/-- Unfolding the ordered product once gives the binary successor cup.
Source: ordered coordinate product in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-successor-product-fold).
Proof: finRange at r+1 is 0 followed by the successors of finRange at r. Apply
that cons equation to the defining List.rec. Its previous value is precisely
successorTailProduct after the canonical length equality. The remaining equality
transports are equal by proof irrelevance. -/
theorem supportedClass_successorCup (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    supportedClass P n B aB (r + 1) =
      successorCup P n B aB r (successorTailProduct P n B aB r) := by
  have hlen : (successorTailList r).length = r := by
    simp only [successorTailList, List.length_map, List.length_finRange]
  unfold supportedClass successorCup coordinateSupportedCompose successorTailProduct
  rw [product_reindex_normalized P n B aB (r + 1) (List.finRange (r + 1))
    (0 :: successorTailList r) (successorTailList_cons r) (r + 1)
    (@List.length_finRange (r + 1)) (congrArg (fun k ↦ k + 1) hlen)]
  rw [product_cons_normalized P n B aB (r + 1) 0 (successorTailList r) r hlen]
  rw [cupZero_tensor]
  simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.AffineZeroPurity
