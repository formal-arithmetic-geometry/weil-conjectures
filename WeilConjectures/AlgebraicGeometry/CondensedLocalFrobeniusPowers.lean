/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFibresExact
public import WeilConjectures.AlgebraicGeometry.LocalFrobeniusTrace

import WeilConjectures.AlgebraicGeometry.CondensedLocalFrobeniusDegreeDivides
import WeilConjectures.AlgebraicGeometry.CondensedModuleReturnPowers
import WeilConjectures.AlgebraicGeometry.CondensedModuleLiftConjugacy

/-! # Local Frobenius powers for condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/
`sk-lem-wrp-l2-growth/lem-wf-l2-upper.proof.md`, opening sentence
(blueprint: lem-wf-condensed-local-frobenius-powers).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The power of the closed-point local operator used in the comparison.
Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/
`sk-lem-wrp-l2-growth/lem-wf-l2-upper.proof.md`
(blueprint: lem-wf-condensed-local-frobenius-powers). -/
def condensedLocalClosedPower
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (M : CondensedModule.Modules l (D.geometricFiber Y₀).left)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom).obj M ≅ M)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (r : ℕ) : End (CondensedModule.fibre l D M (localClosedPoint D Y₀ y ι hι)) :=
  (CondensedModule.operator l D (D.geometricFrobenius Y₀).hom M θ
    (localClosedPoint D Y₀ y ι hι) (localClosedPointDegree D Y₀ y - 1)
    (localClosedPoint_return D Y₀ y ι hι)) ^ r

private theorem positivePower_eq_pow {Y : Scheme.{u}} (a : Y ⟶ Y) (n : ℕ) :
    localPositivePower a n = (End.of a) ^ (n + 1) := by
  induction n with
  | zero => simp [localPositivePower]
  | succ n ih => simp only [localPositivePower, ih, pow_succ', End.mul_def]

private theorem intertwine_pow {C : Type*} [Category C] {X Y : C}
    (z : X ⟶ Y) (a : End Y) (b : End X) (h : z ≫ a = b ≫ z) (r : ℕ) :
    z ≫ (a ^ r) = (b ^ r) ≫ z := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [pow_succ', End.mul_def]
    calc
      z ≫ (a ^ r) ≫ a = (z ≫ (a ^ r)) ≫ a := (Category.assoc _ _ _).symm
      _ = ((b ^ r) ≫ z) ≫ a := by rw [ih]
      _ = (b ^ r) ≫ b ≫ z := by rw [Category.assoc, h]
      _ = ((b ^ r) ≫ b) ≫ z := (Category.assoc _ _ _).symm

private theorem return_mul (D : FiniteFieldDatum.{u}) {Y : Scheme.{u}} (a : Y ⟶ Y)
    (z : Spec (.of D.k) ⟶ Y) (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (h : z ≫ localPositivePower a (d - 1) =
      localPositivePower (frobeniusPointIso D).hom (d - 1) ≫ z) :
    z ≫ localPositivePower a (d * r - 1) =
      localPositivePower (frobeniusPointIso D).hom (d * r - 1) ≫ z := by
  have hdr : 1 ≤ d * r := Nat.mul_pos hd hr
  simp only [positivePower_eq_pow, Nat.sub_add_cancel hd] at h
  simp only [positivePower_eq_pow, Nat.sub_add_cancel hdr, pow_mul]
  exact intertwine_pow z _ _ h r

private theorem conjugate_of_intertwine {C : Type*} [Category C] {X Y : C}
    (T : X ≅ Y) (f : End X) (g : End Y) (h : f ≫ T.hom = T.hom ≫ g) :
    f = T.hom ≫ g ≫ T.inv := by
  apply (cancel_mono T.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- A rational-point local return is conjugate to the corresponding closed-point power.

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/
`sk-lem-wrp-l2-growth/lem-wf-l2-upper.proof.md`, opening sentence
(blueprint: lem-wf-condensed-local-frobenius-powers).
Proof:
1. The closed-point residue field is finite over the base. The rational point embeds it
   into the field with q^m elements. Its base-field Frobenius has m-th power one, and its
   order is d, proving d divides m. Write m = d*r with r positive.
2. The specified closed-point lift has a d-return. The actual point trivializations
   respect composition, by their normalization on modules pulled back from the condensed
   point and essential surjectivity of that pullback. Pullback associativity and
   naturality then give the concatenation formula for actual semilinear transports.
   Induction on r identifies the m-return at this lift with its d-return operator to the
   r-th power.
3. The extension-point lift and the specified closed-point lift correspond to embeddings
   of the same finite residue field. Upstream finite-field Frobenius lemmas put these in
   one orbit. Transport along an orbit segment gives a linear fibre isomorphism T.
   Concatenation with the m-return in the two orders gives the intertwining equation.
   Substitute step 2, use r = m/d, and cancel T to obtain the displayed conjugacy.
   Zero fibres are allowed; no lissity or lattice is used. -/
theorem condensed_local_frobenius_powers
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (m : ℕ) (hm : 1 ≤ m) (x : D.extensionPoints Y₀ m hm)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (hxy : x.left (IsLocalRing.closedPoint (D.extensionSubfield m hm)) = y.val)
    (M : CondensedModule.Modules l (D.geometricFiber Y₀).left)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber Y₀).left M)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom).obj M ≅ M) :
    1 ≤ localClosedPointDegree D Y₀ y ∧
      localClosedPointDegree D Y₀ y ∣ m ∧
      ∃ T : CondensedModule.fibre l D M (localExtensionPoint D Y₀ m hm x) ≅
          CondensedModule.fibre l D M (localClosedPoint D Y₀ y ι hι),
        CondensedModule.operator l D (D.geometricFrobenius Y₀).hom M θ
            (localExtensionPoint D Y₀ m hm x) (m - 1)
            (localExtensionPoint_return D Y₀ m hm x) =
          T.hom ≫
            condensedLocalClosedPower D l Y₀ M θ y ι hι
              (m / localClosedPointDegree D Y₀ y) ≫ T.inv := by
  have _ := hl
  have _ := hM
  have hd := localClosedPointDegree_pos D Y₀ y
  have hdiv := condensed_local_frobenius_degree_divides D Y₀ m hm x y hxy
  refine ⟨hd, hdiv, ?_⟩
  obtain ⟨r, hrm⟩ := hdiv
  have hr : 1 ≤ r := by
    by_contra h
    have : r = 0 := by omega
    simp [this] at hrm
    omega
  have hret := return_mul D (D.geometricFrobenius Y₀).hom
    (localClosedPoint D Y₀ y ι hι) (localClosedPointDegree D Y₀ y) r hd hr
    (localClosedPoint_return D Y₀ y ι hι)
  have hpower := CondensedModule.return_powers D l
    (D.geometricFrobenius Y₀).hom M θ (localClosedPoint D Y₀ y ι hι)
    (localClosedPointDegree D Y₀ y) r hd hr (localClosedPoint_return D Y₀ y ι hι) hret
  have hretm : localClosedPoint D Y₀ y ι hι ≫
      localPositivePower (D.geometricFrobenius Y₀).hom (m - 1) =
      localPositivePower (frobeniusPointIso D).hom (m - 1) ≫
        localClosedPoint D Y₀ y ι hι := by
    simpa only [hrm] using hret
  have hpowerm : CondensedModule.operator l D (D.geometricFrobenius Y₀).hom M θ
      (localClosedPoint D Y₀ y ι hι) (m - 1) hretm =
      (CondensedModule.operator l D (D.geometricFrobenius Y₀).hom M θ
        (localClosedPoint D Y₀ y ι hι) (localClosedPointDegree D Y₀ y - 1)
        (localClosedPoint_return D Y₀ y ι hι)) ^ r := by
    subst m
    exact hpower
  have hxbase : localExtensionPoint D Y₀ m hm x ≫ (D.geometricFiber Y₀).hom = 𝟙 _ := by
    simp [localExtensionPoint, FiniteFieldDatum.geometricFiber]
  have hybase : localClosedPoint D Y₀ y ι hι ≫ (D.geometricFiber Y₀).hom = 𝟙 _ := by
    simp [localClosedPoint, FiniteFieldDatum.geometricFiber]
  have hximage : (localExtensionPoint D Y₀ m hm x ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = y.val := by
    simp only [localExtensionPoint, pullback.lift_fst, Scheme.Hom.comp_apply]
    convert hxy using 1
    congr 1
    exact Subsingleton.elim _ _
  have hyimage : (localClosedPoint D Y₀ y ι hι ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = y.val := by
    simp only [localClosedPoint, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  obtain ⟨T, hT⟩ := CondensedModule.lift_conjugacy D l Y₀ y
    (localExtensionPoint D Y₀ m hm x) (localClosedPoint D Y₀ y ι hι)
    hxbase hybase hximage hyimage M θ m hm
    (localExtensionPoint_return D Y₀ m hm x) hretm
  refine ⟨T, ?_⟩
  have hrdiv : m / localClosedPointDegree D Y₀ y = r := by
    rw [hrm, Nat.mul_div_cancel_left r (by omega)]
  rw [hpowerm] at hT
  unfold condensedLocalClosedPower
  rw [hrdiv]
  exact conjugate_of_intertwine T _ _ hT

end WeilConjectures
