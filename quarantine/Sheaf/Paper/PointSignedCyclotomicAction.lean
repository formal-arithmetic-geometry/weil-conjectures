/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.Paper.PointSignedCyclotomicActionData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
import Sheaf.Paper.PointSignedCyclotomicScalar
import Sheaf.Paper.PointRootLimitCyclotomicAction
import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
import Sheaf.NumberTheory.FrobeniusRootsOfUnityPower
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Signed cyclotomic action on sections at a geometric point

Source: Deligne, Weil I (2.2), pp. 280--281; Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-point-signed-cyclotomic-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSignedCyclotomicAction

attribute [local irreducible] frobeniusPointIso
set_option backward.defeqAttrib.useBackward true

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem roots_restrict_value (S : Scheme.{u}) (N : ℕ)
    {U V : S.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    (proEtaleRootsOfUnitySections S N V
      ((proEtaleRootsOfUnitySheaf S N).obj.map f x)).toMul.val.val =
      f.unop.left.appTop.hom (proEtaleRootsOfUnitySections S N U x).toMul.val.val := by
  have h := ConcreteCategory.congr_hom
    ((proEtaleRootsOfUnityInclusion S N).hom.naturality f) x
  change (proEtaleRootsOfUnityInclusion S N).hom.app V
      ((proEtaleRootsOfUnitySheaf S N).obj.map f x) =
    (proEtaleUnitsSheaf S).obj.map f
      ((proEtaleRootsOfUnityInclusion S N).hom.app U x) at h
  rw [← (existsUnique_proEtaleRootsOfUnitySections S N V).exists.choose_spec,
    ← (existsUnique_proEtaleRootsOfUnitySections S N U).exists.choose_spec] at h
  exact congrArg (fun z ↦ z.down.toMul.val) h

private theorem roots_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (V : Y.ProEt) (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj (op V)) :
    (proEtaleRootsOfUnityInverseImageMap f N).hom.app
      (op ((proEtaleBaseChange f).obj V))
      (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
        (proEtaleRootsOfUnitySheaf Y N)).hom.app (op V) x) =
    (proEtaleRootsOfUnityDirectImageMap f N).hom.app (op V) x := by
  have h := ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).apply_symm_apply
    (proEtaleRootsOfUnityDirectImageMap f N)
  exact congrArg (fun a ↦ a.hom.app (op V) x) h

private theorem sectionArrow_projection :
    (sectionArrow D).left ≫ pullback.fst (𝟙 (point D)) (frobeniusPointIso D).hom =
      (frobeniusPointIso D).hom := by
  change ((proEtaleIsoCommaArrow (frobeniusPointIso D).hom (finalObject D)).left ≫
    ((proEtaleBaseChange (frobeniusPointIso D).hom).map
      (frobeniusPointRestriction D)).left) ≫ _ = _
  calc
    _ = (proEtaleIsoCommaArrow (frobeniusPointIso D).hom (finalObject D)).left ≫
        (pullback.fst _ _ ≫ (frobeniusPointRestriction D).left) := by
      rw [Category.assoc]
      congr 1
      exact pullback.lift_fst _ _ _
    _ = _ := by
      rw [← Category.assoc,
        show (proEtaleIsoCommaArrow (frobeniusPointIso D).hom (finalObject D)).left ≫
          pullback.fst _ _ = 𝟙 _ from pullback.lift_fst _ _ _, Category.id_comp]
      exact congrArg (fun f ↦ f.left)
        ((ProEt.forget (point D)).map_preimage
          (X := (proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj (finalObject D))
          (Y := finalObject D) (Over.homMk (frobeniusPointIso D).hom))

private theorem root_action_value (N : ℕ)
    (x : (proEtaleRootsOfUnitySheaf (point D) N).obj.obj (op (finalObject D))) :
    rootValue D N (rootAction D N x) =
      (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
        D.k _ _ _).symm (rootValue D N x) := by
  unfold rootAction
  rw [roots_unit]
  unfold rootValue
  rw [roots_restrict_value]
  have hβ := (existsUnique_proEtaleRootsOfUnityDirectImageMap
    (frobeniusPointIso D).hom N).exists.choose_spec (op (finalObject D)) x
  change proEtaleRootsOfUnitySections _ _ _
    ((proEtaleRootsOfUnityDirectImageMap _ _).hom.app _ x) = _ at hβ
  have hv := congrArg (fun z ↦ z.toMul.val.val) hβ
  refine (congrArg (fun z ↦ (ΓSpecIso (.of D.k)).hom.hom
    ((sectionArrow D).left.appTop.hom z)) hv).trans ?_
  change (ΓSpecIso (.of D.k)).hom.hom
    ((sectionArrow D).left.appTop.hom
      ((pullback.fst (𝟙 (point D)) (frobeniusPointIso D).hom).appTop.hom
        (proEtaleRootsOfUnitySections (point D) N (op (finalObject D)) x).toMul.val.val)) = _
  have h := congrArg (fun f ↦ f.appTop) (sectionArrow_projection D)
  rw [Hom.comp_appTop] at h
  change (ΓSpecIso (.of D.k)).hom.hom
    (((pullback.fst (𝟙 (point D)) (frobeniusPointIso D).hom).appTop ≫
      (sectionArrow D).left.appTop).hom _) = _
  rw [h]
  unfold frobeniusPointIso
  exact ConcreteCategory.congr_hom
    (ΓSpecIso_naturality
      ((@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
        D.k _ _ _).symm.toRingEquiv.toCommRingCatIso.hom)) _

private theorem constant_action_one (R : CommRingCat.{u + 1}) :
    constantAction D R 1 = 1 := by
  simp only [constantAction, map_one]

private theorem scalar_unit (hl : l ≠ D.p) (a : Option ℕ) :
    IsUnit (D.q : scalars l E a) := by
  have hcop : l.Coprime D.p := (Nat.coprime_primes Fact.out D.prime).mpr hl
  have hq : IsUnit (D.q : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff, D.cardinality_eq]
    exact hcop.pow_right _
  have hO : IsUnit (D.q : Padic.coefficientExtensionIntegers l E) := by
    simpa only [map_natCast] using hq.map (purTwistIntegersMap l E)
  cases a with
  | none => exact hO.map ULift.ringEquiv.symm.toRingHom
  | some n =>
    exact (hO.map (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))).map
      ULift.ringEquiv.symm.toRingHom

private theorem scale_scale (a : Option ℕ) (m : ℤ) (b c : scalars l E a)
    (x : (line D l E a m).val.obj (op (finalObject D))) :
    scale D l E a m b (scale D l E a m c x) = scale D l E a m (b * c) x := by
  simp only [scale, map_mul, mul_smul]

private theorem scale_one (a : Option ℕ) (m : ℤ)
    (x : (line D l E a m).val.obj (op (finalObject D))) :
    scale D l E a m 1 x = x := by
  simp only [scale, map_one, one_smul]

private theorem tensor_smul {S : Scheme.{u}}
    {R : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (U : S.ProEtᵒᵖ) (b c : R.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    SheafOfModules.siteSheafTensorTmul M N U (b • x) (c • y) =
      (b * c) • SheafOfModules.siteSheafTensorTmul M N U x y := by
  unfold SheafOfModules.siteSheafTensorTmul
  let f := ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (𝟙 _)).unit.app
    (SheafOfModules.siteTensorPresheaf M.val N.val)).app U
  change f ((b • x) ⊗ₜ[R.obj.obj U] (c • y)) = (b * c) • f (x ⊗ₜ[R.obj.obj U] y)
  have h : (b • x) ⊗ₜ[R.obj.obj U] (c • y) =
      (b * c) • (x ⊗ₜ[R.obj.obj U] y) := TensorProduct.smul_tmul_smul b c x y
  exact (congrArg (fun z ↦ f z) h).trans (f.hom.map_smul _ _)

private theorem tensor_scale (a : Option ℕ) (n : ℕ) (b c : scalars l E a)
    (x : (line D l E a ((n + 1 : ℕ) : ℤ)).val.obj (op (finalObject D)))
    (y : (line D l E a 1).val.obj (op (finalObject D))) :
    tensor D l E a n (scale D l E a _ b x) (scale D l E a _ c y) =
      scale D l E a _ (b * c) (tensor D l E a n x y) := by
  cases a with
  | none =>
    simpa only [tensor, scale, map_mul] using
      tensor_smul (FrobeniusCoefficientTwists.positiveLine l E (point D) (n + 1))
        (purTwistIntegralModule (point D) l E) (op (finalObject D))
        (scalarAt D l E none b) (scalarAt D l E none c) x y
  | some j =>
    simpa only [tensor, scale, map_mul] using
      tensor_smul (coefficientTwistPower (point D) (purTwistFiniteOne (point D) l E j)
        (n + 1)) (purTwistFiniteOne (point D) l E j) (op (finalObject D))
        (scalarAt D l E (some j) b) (scalarAt D l E (some j) c) x y

private theorem evaluate_scale_left (a : Option ℕ) (n : ℕ) (b : scalars l E a)
    (φ : (line D l E a (Int.negSucc n)).val.obj (op (finalObject D)))
    (x : (line D l E a ((n + 1 : ℕ) : ℤ)).val.obj (op (finalObject D))) :
    evaluate D l E a n (scale D l E a _ b φ) x =
      scalarAt D l E a b * evaluate D l E a n φ x := by
  cases a <;>
    change ((coefficientRing D l E _).obj.map (𝟙 (op (finalObject D))))
      (scalarAt D l E _ b) * evaluate D l E _ n φ x = _
  all_goals
    have h := ConcreteCategory.congr_hom ((coefficientRing D l E _).obj.map_id
      (op (finalObject D))) (scalarAt D l E _ b)
    exact congrArg (fun z ↦ z * evaluate D l E _ n φ x) h

private theorem evaluate_scale_right (a : Option ℕ) (n : ℕ) (b : scalars l E a)
    (φ : (line D l E a (Int.negSucc n)).val.obj (op (finalObject D)))
    (x : (line D l E a ((n + 1 : ℕ) : ℤ)).val.obj (op (finalObject D))) :
    evaluate D l E a n φ (scale D l E a _ b x) =
      scalarAt D l E a b * evaluate D l E a n φ x := by
  cases a <;> exact (φ.app _).hom.map_smul _ _

private theorem positive_action (hl : l ≠ D.p) (a : Option ℕ) (d : ℕ)
    (x : (line D l E a (d : ℤ)).val.obj (op (finalObject D))) :
    action D l E a (d : ℤ) x =
      scale D l E a (d : ℤ) (Ring.inverse (D.q : scalars l E a) ^ d) x := by
  simpa only [Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, mul_one] using
    signed_section_scalar D l E hl a (d : ℤ) x

private theorem negative_action (hl : l ≠ D.p) (a : Option ℕ) (n : ℕ)
    (φ : (line D l E a (Int.negSucc n)).val.obj (op (finalObject D))) :
    action D l E a (Int.negSucc n) φ =
      scale D l E a (Int.negSucc n) ((D.q : scalars l E a) ^ (n + 1)) φ := by
  simpa only [Int.toNat_negSucc, Int.neg_negSucc, Int.toNat_natCast, pow_zero, one_mul] using
    signed_section_scalar D l E hl a (Int.negSucc n) φ

private theorem inverse_powers (hl : l ≠ D.p) (a : Option ℕ) (d : ℕ) :
    (D.q : scalars l E a) ^ d * Ring.inverse (D.q : scalars l E a) ^ d = 1 := by
  rw [← mul_pow, Ring.mul_inverse_cancel _ (scalar_unit D l E hl a), one_pow]

private theorem positive_action_bijective (hl : l ≠ D.p) (a : Option ℕ) (d : ℕ) :
    Function.Bijective (action D l E a (d : ℤ)) := by
  let f := fun x : (line D l E a (d : ℤ)).val.obj (op (finalObject D)) ↦
    scale D l E a (d : ℤ) ((D.q : scalars l E a) ^ d) x
  have hleft : Function.LeftInverse f (action D l E a (d : ℤ)) := by
    intro x
    dsimp only [f]
    rw [positive_action D l E hl, scale_scale, inverse_powers D l E hl, scale_one]
  have hright : Function.RightInverse f (action D l E a (d : ℤ)) := by
    intro x
    dsimp only [f]
    rw [positive_action D l E hl, scale_scale, mul_comm,
      inverse_powers D l E hl, scale_one]
  exact ⟨hleft.injective, hright.surjective⟩

private theorem dual_pairing (hl : l ≠ D.p) (a : Option ℕ) (n : ℕ)
    (φ : (line D l E a (Int.negSucc n)).val.obj (op (finalObject D)))
    (x : (line D l E a ((n + 1 : ℕ) : ℤ)).val.obj (op (finalObject D))) :
    evaluate D l E a n (action D l E a (Int.negSucc n) φ)
      (action D l E a ((n + 1 : ℕ) : ℤ) x) = evaluate D l E a n φ x := by
  rw [negative_action D l E hl, positive_action D l E hl,
    evaluate_scale_left, evaluate_scale_right, ← mul_assoc, ← map_mul,
    inverse_powers D l E hl, map_one, one_mul]

/-- The root basis carries the signed geometric cyclotomic character. The universal
section formula is equivalent to the coordinate formula b e_m, since the chosen
compatible primitive roots trivialize every signed line; the final clauses retain
its tensor and dual normalizations explicitly.

Source: Deligne, Weil I (2.2), pp. 280--281; Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-point-signed-cyclotomic-action).

Proof:
1. In lem-weil-point-automorphism-restriction-natural the distinguished coprojection
is the identity, so sigma is restriction along g. The root sheaf restricts by
pullback of units. Thus it sends zeta to gamma(zeta), while the comparison itself
is the identity on roots of the unchanged underlying scheme, by
lem-pur-roots-of-unity-inverse-image-iso.
2. Apply lem-pur-frobenius-roots-of-unity-power with N=l^(r+1). The inverse exponent
is q' modulo N and q is a unit in Z_l. Field automorphisms commute with l-th powers;
the root comparison commutes with transitions. The sectionwise inverse limit
therefore acts coordinatewise and takes the compatible root basis to q inverse times it.
3. Constant restriction followed by its structure comparison fixes every coefficient,
including 1. The completed comparison is the inverse limit of the finite comparisons
in def-weil-constant-weil-structure; its quotient projections fix all reductions of 1.
This also proves the degree-zero formula.
4. The inverse-image tensor comparison of lem-pur-isomorphism-inverse-image-tensor-hom
respects the pure tensors of def-pur-sheaf-tensor-product. Therefore extension of
coefficients sends e tensor 1 to q inverse times e tensor 1. The positive tensor
formula gives the successor identity; induction gives q^(-m) for every positive m.
5. Evaluate the internal Hom comparison on tau_r(sigma x). Its inverse tau_r cancels,
and restriction respects evaluation by def-pur-sheaf-hom. The coefficient result
then gives Psi_(-r)(phi)(Psi_r(x))=phi(x). The positive scalar is invertible, hence
Psi_(-r)(phi)=phi composed with Psi_r inverse; at a normalized dual generator the
value on e_r is q^r.
6. The compatible primitive-root coordinates of lem-pur-point-tate-root-coordinates
identify every signed section with b e_m. Coefficient linearity of sigma and tau
assembles the signed scalar formula. Since q is a unit, this includes nonreduced
finite quotients, every negative exponent, and m=0. -/
theorem point_signed_cyclotomic_action (hl : l ≠ D.p)
    (e : (purTwistZlOne (point D) l).obj.obj (op (finalObject D)))
    (he : ∀ r : ℕ, IsPrimitiveRoot
      (rootValue D (l ^ (r + 1))
        ((limit.π (proEtaleRootsOfUnityTower (point D) l Fact.out) (op r)).hom.app
          (op (finalObject D)) e)) (l ^ (r + 1))) :
    (∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = (D.q : ℤ_[l])) ∧
    (∀ r : ℕ,
      (∃ q' : ℤ, Int.ModEq (l ^ (r + 1) : ℕ) ((D.q : ℤ) * q') 1) ∧
      ∀ (q' : ℤ), Int.ModEq (l ^ (r + 1) : ℕ) ((D.q : ℤ) * q') 1 →
        ∀ x : (proEtaleRootsOfUnitySheaf (point D) (l ^ (r + 1))).obj.obj
          (op (finalObject D)),
          rootValue D (l ^ (r + 1)) (rootAction D (l ^ (r + 1)) x) =
            rootValue D (l ^ (r + 1)) x ^ q') ∧
    (∀ (r : ℕ)
      (x : (proEtaleRootsOfUnitySheaf (point D) (l ^ (r + 1))).obj.obj
        (op (finalObject D))),
      rootValue D (l ^ (r + 1)) (rootAction D (l ^ (r + 1)) x) =
        (@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _ (Fintype.ofFinite D.k₀)
          D.k _ _ _).symm (rootValue D (l ^ (r + 1)) x)) ∧
    (∀ (r : ℕ)
      (x : ((proEtaleSheafInverseImage (frobeniusPointIso D).hom AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf (point D) (l ^ (r + 1)))).obj.obj
          (op (finalObject D))),
      proEtaleRootsOfUnitySections (point D) (l ^ (r + 1)) (op (finalObject D))
        ((proEtaleRootsOfUnityInverseImageMap (frobeniusPointIso D).hom
          (l ^ (r + 1))).hom.app (op (finalObject D)) x) =
      proEtaleRootsOfUnitySections (point D) (l ^ (r + 1))
        ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).op.obj (op (finalObject D)))
        (((proEtaleIsoInverseImageIdentification (frobeniusPointIso D).hom
          AddCommGrpCat.{u + 1}).hom.app
            (proEtaleRootsOfUnitySheaf (point D) (l ^ (r + 1)))).app
              (op (finalObject D)) x)) ∧
    (∀ (r : ℕ)
      (x : (proEtaleRootsOfUnitySheaf (point D) (l ^ (r + 2))).obj.obj
        (op (finalObject D))),
      rootAction D (l ^ (r + 1))
        ((proEtaleRootsOfUnityTransition (point D) (l ^ (r + 1)) (l ^ (r + 2))
          (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
          (pow_dvd_pow l (Nat.le_succ (r + 1)))).hom.app
          (op (finalObject D)) x) =
      (proEtaleRootsOfUnityTransition (point D) (l ^ (r + 1)) (l ^ (r + 2))
          (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
          (pow_dvd_pow l (Nat.le_succ (r + 1)))).hom.app
        (op (finalObject D)) (rootAction D (l ^ (r + 2)) x)) ∧
    (rootLimitAction D l e =
      @SMul.smul _ _ (purTwistZlAction (point D) l (op (finalObject D))).toSMul
        ((purTwistZlCompletionMap (point D) l).hom.app (op (finalObject D))
          (((toSheafify (ProEt.topology (point D))
            ((Functor.const (point D).ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1} (PadicInt l))))).app (op (finalObject D)))
                (ULift.up (Ring.inverse (D.q : ℤ_[l])))))
        e) ∧
    (constantAction D (CommRingCat.of (ULift.{u + 1} (PadicInt l))) 1 = 1 ∧
      constantAction D (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) 1 = 1 ∧
      ∀ n : ℕ, constantAction D (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) 1 = 1) ∧
    (∀ (a : Option ℕ) (m : ℤ) (b : scalars l E a)
      (x : (line D l E a m).val.obj (op (finalObject D))),
      action D l E a m (scale D l E a m b x) =
        scale D l E a m (b * (Ring.inverse (D.q : scalars l E a) ^ m.toNat *
          (D.q : scalars l E a) ^ (-m).toNat)) x) ∧
    (∀ a : Option ℕ,
      action D l E a 0 (generator D l E a e 0) = generator D l E a e 0) ∧
    (∀ (a : Option ℕ) (n : ℕ),
      action D l E a ((n + 2 : ℕ) : ℤ)
        (tensor D l E a n (generator D l E a e (n + 1)) (generator D l E a e 1)) =
      tensor D l E a n
        (action D l E a ((n + 1 : ℕ) : ℤ) (generator D l E a e (n + 1)))
        (action D l E a 1 (generator D l E a e 1))) ∧
    (∀ (a : Option ℕ) (n : ℕ)
      (φ : (line D l E a (Int.negSucc n)).val.obj (op (finalObject D)))
      (x : (line D l E a ((n + 1 : ℕ) : ℤ)).val.obj (op (finalObject D))),
      evaluate D l E a n (action D l E a (Int.negSucc n) φ)
        (action D l E a ((n + 1 : ℕ) : ℤ) x) = evaluate D l E a n φ x) ∧
    (∀ (a : Option ℕ) (n : ℕ),
      Function.Bijective (action D l E a ((n + 1 : ℕ) : ℤ)) ∧
      ∀ (φ : (line D l E a (Int.negSucc n)).val.obj (op (finalObject D)))
        (x : (line D l E a ((n + 1 : ℕ) : ℤ)).val.obj (op (finalObject D))),
        evaluate D l E a n (action D l E a (Int.negSucc n) φ) x =
          evaluate D l E a n φ
            (Function.invFun (action D l E a ((n + 1 : ℕ) : ℤ)) x)) ∧
    (∀ (a : Option ℕ) (n : ℕ)
      (φ : (line D l E a (Int.negSucc n)).val.obj (op (finalObject D))),
      evaluate D l E a n φ (generator D l E a e (n + 1)) = 1 →
      evaluate D l E a n (action D l E a (Int.negSucc n) φ)
        (generator D l E a e (n + 1)) = scalarAt D l E a ((D.q : scalars l E a) ^ (n + 1))) := by
  classical
  have he_used := he
  clear he_used he
  have hcop : l.Coprime D.p := (Nat.coprime_primes Fact.out D.prime).mpr hl
  have hpow (r : ℕ) := D.frobenius_rootsOfUnity_power (l ^ (r + 1))
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
    (hcop.pow_left _)
  obtain ⟨uq, huq, _⟩ := ((hpow 0).2.2 l hl).2
  refine ⟨⟨uq, huq⟩, ?_, (fun r ↦ root_action_value D (l ^ (r + 1))), ?_, ?_,
    root_limit_cyclotomic_action D l hl e, ?_, ?_, ?_, ?_,
    dual_pairing D l E hl, ?_, ?_⟩
  · intro r
    refine ⟨(hpow r).2.1.2.1, ?_⟩
    intro q' hq' x
    rw [root_action_value D]
    let ζ : rootsOfUnity (l ^ (r + 1)) D.k :=
      restrictRootsOfUnity (ΓSpecIso (.of D.k)).hom.hom _
        (proEtaleRootsOfUnitySections (point D) _ (op (finalObject D)) x).toMul
    have hz := congrArg Units.val ((hpow r).2.1.2.2 q' hq' ζ)
    have hval : ((ζ : D.kˣ) : D.k) = rootValue D (l ^ (r + 1)) x := rfl
    simp only [Units.coe_map, Units.val_zpow_eq_zpow_val] at hz
    rw [hval] at hz
    exact hz
  · intro r x
    exact ((proEtaleRootsOfUnityInverseImageIso (frobeniusPointIso D).hom).2.2.2
      inferInstance (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _)).2 _ x
  · intro r x
    let g := (frobeniusPointIso D).hom
    let U := finalObject D
    let V := (proEtaleBaseChange g).obj U
    let T := proEtaleRootsOfUnityTransition (point D) (l ^ (r + 1)) (l ^ (r + 2))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (r + 1)))
    let η := (proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit
    have hn := congrArg (fun h ↦ h.hom.app (op U) x) (η.naturality T)
    change (η.app _).hom.app (op U) (T.hom.app (op U) x) =
      ((proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).map T).hom.app (op V)
        ((η.app _).hom.app (op U) x) at hn
    have hc := congrArg (fun h ↦ h.hom.app (op V) ((η.app _).hom.app (op U) x))
      ((proEtaleRootsOfUnityInverseImageIso g).1 (l ^ (r + 1)) (l ^ (r + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (r + 1))))
    change (proEtaleRootsOfUnityInverseImageMap g _).hom.app (op V)
      (((proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).map T).hom.app (op V)
        ((η.app _).hom.app (op U) x)) =
      T.hom.app (op V) ((proEtaleRootsOfUnityInverseImageMap g _).hom.app (op V)
        ((η.app _).hom.app (op U) x)) at hc
    unfold rootAction
    change (proEtaleRootsOfUnitySheaf (point D) _).obj.map (sectionArrow D).op
      ((proEtaleRootsOfUnityInverseImageMap g _).hom.app (op V)
        ((η.app _).hom.app (op U) (T.hom.app (op U) x))) = _
    exact (congrArg (fun z ↦
      (proEtaleRootsOfUnitySheaf (point D) (l ^ (r + 1))).obj.map
        (sectionArrow D).op
        ((proEtaleRootsOfUnityInverseImageMap g (l ^ (r + 1))).hom.app (op V) z))
      hn).trans ((congrArg (fun z ↦
        (proEtaleRootsOfUnitySheaf (point D) (l ^ (r + 1))).obj.map
          (sectionArrow D).op z) hc).trans
            (ConcreteCategory.congr_hom (T.hom.naturality (sectionArrow D).op) _).symm)
  · exact ⟨constant_action_one D _, constant_action_one D _, fun _ ↦ constant_action_one D _⟩
  · intro a m b x
    rw [signed_section_scalar D l E hl, scale_scale, mul_comm]
  · intro a
    simpa only [pow_zero, scale_one, Int.natCast_zero] using
      positive_action D l E hl a 0 (generator D l E a e 0)
  · intro a n
    rw [positive_action D l E hl, positive_action D l E hl]
    have hone := positive_action D l E hl a 1 (generator D l E a e 1)
    simp only [Int.natCast_one, pow_one] at hone
    rw [hone, tensor_scale, ← pow_succ]
  · intro a n
    refine ⟨positive_action_bijective D l E hl a (n + 1), ?_⟩
    intro φ x
    have h := dual_pairing D l E hl a n φ
      (Function.invFun (action D l E a ((n + 1 : ℕ) : ℤ)) x)
    rw [Function.rightInverse_invFun (positive_action_bijective D l E hl a (n + 1)).2 x] at h
    exact h
  · intro a n φ hφ
    rw [negative_action D l E hl, evaluate_scale_left, hφ, mul_one]

end WeilConjectures.PointSignedCyclotomicAction
