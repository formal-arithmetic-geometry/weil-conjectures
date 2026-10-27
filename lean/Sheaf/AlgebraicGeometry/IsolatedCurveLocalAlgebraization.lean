/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.AlgebraicGeometry.IsolatedCurveFormalLifting
public import Sheaf.AlgebraicGeometry.ProperFormalCurveAlgebraization
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Algebraizing prescribed local deformations of a proper curve

Source: Stacks Project, Tag 0E7Y, middle paragraph, using Tags 0DZP, 06HN, 0E7R
and 0D4G. (blueprint: lem-sfb-isolated-curve-local-algebraization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem distinguished_X_pow (k : Type u) [Field k] (n : ℕ) :
    (Polynomial.X ^ n : Polynomial k).IsDistinguishedAt (⊥ : Ideal k) := by
  refine ⟨⟨fun {i} hi ↦ ?_⟩, Polynomial.monic_X_pow n⟩
  simp only [Polynomial.natDegree_X_pow] at hi
  simp [Polynomial.coeff_X_pow, ne_of_lt hi]

private noncomputable def levelPowerSeriesEquiv (k : Type u) [Field k] (n : ℕ) :
    isolatedCurveLevelRing k n ≃ₐ[k]
      PowerSeries k ⧸ (Ideal.span {(PowerSeries.X : PowerSeries k)}) ^ (n + 1) :=
  (Ideal.quotientEquivAlgOfEq k (by
    simp [← Ideal.span_singleton_pow])).trans
    (((distinguished_X_pow k (n + 1)).algEquivQuotient).trans
      (Ideal.quotientEquivAlgOfEq k (by simp [← Ideal.span_singleton_pow])))

private theorem levelPowerSeriesEquiv_mk (k : Type u) [Field k] (n : ℕ)
    (a : Polynomial k) :
    levelPowerSeriesEquiv k n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (a : PowerSeries k) := by
  rfl

private theorem levelPowerSeriesEquiv_parameter (k : Type u) [Field k] (n : ℕ) :
    levelPowerSeriesEquiv k n (isolatedCurveLevelParameter k n) =
      Ideal.Quotient.mk _ PowerSeries.X := by
  simpa [isolatedCurveLevelParameter] using
    levelPowerSeriesEquiv_mk k n Polynomial.X

private theorem levelPowerSeriesEquiv_reduction (k : Type u) [Field k] (n : ℕ) :
    (levelPowerSeriesEquiv k n).toRingHom.comp (isolatedCurveLevelReduction k n) =
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).comp
        (levelPowerSeriesEquiv k (n + 1)).toRingHom := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change levelPowerSeriesEquiv k n (Ideal.Quotient.mk _ a) =
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (levelPowerSeriesEquiv k (n + 1) (Ideal.Quotient.mk _ a))
  simp only [levelPowerSeriesEquiv_mk, Ideal.Quotient.factor_mk]

private noncomputable def powerSeriesLevelZero (k : Type u) [Field k] :
    (PowerSeries k ⧸ (Ideal.span {(PowerSeries.X : PowerSeries k)}) ^ (0 + 1)) →+* k :=
  Ideal.Quotient.lift _ PowerSeries.constantCoeff (by
    rw [pow_one]
    change Ideal.span {PowerSeries.X} ≤ RingHom.ker PowerSeries.constantCoeff
    rw [Ideal.span_le]
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    simp)

private theorem levelPowerSeriesEquiv_zero (k : Type u) [Field k] :
    (powerSeriesLevelZero k).comp (levelPowerSeriesEquiv k 0).toRingHom =
      (isolatedCurveLevelZero k).toRingHom := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change powerSeriesLevelZero k
      (levelPowerSeriesEquiv k 0 (Ideal.Quotient.mk _ a)) = _
  rw [levelPowerSeriesEquiv_mk]
  change PowerSeries.constantCoeff (a : PowerSeries k) = _
  simpa [isolatedCurveLevelZero] using Polynomial.coeff_zero_eq_eval_zero a

private theorem scalarToStalk_eq (k : Type u) [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    isolatedCurveScalarToStalk f x =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
        X.presheaf.germ ⊤ x trivial).hom) := by
  change (StructureSheaf.toStalk k (f x) ≫ f.stalkMap x).hom = _
  have h : StructureSheaf.toStalk k (f x) ≫ f.stalkMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
        X.presheaf.germ ⊤ x trivial := by
    change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (f x) trivial) ≫ f.stalkMap x = _
    rw [Category.assoc, Scheme.Hom.germ_stalkMap]
    simp only [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res']
  exact congrArg CommRingCat.Hom.hom h

set_option backward.isDefEq.respectTransparency false in
private theorem scalarToStalk_naturality {A D : Type u} [CommRing A] [CommRing D]
    {V W : Scheme.{u}} (l : V ⟶ W) (q : W ⟶ Spec (.of A))
    (q' : V ⟶ Spec (.of D)) (c : A →+* D)
    (hc : l ≫ q = q' ≫ Spec.map (CommRingCat.ofHom c)) (x : V) (a : A) :
    l.stalkMap x (isolatedCurveScalarToStalk q (l x) a) =
      isolatedCurveScalarToStalk q' x (c a) := by
  have hleft : (StructureSheaf.toStalk A (q (l x)) ≫ q.stalkMap (l x)) ≫
      l.stalkMap x = StructureSheaf.toStalk A ((l ≫ q) x) ≫ (l ≫ q).stalkMap x := by
    rw [Category.assoc, Scheme.Hom.stalkMap_comp]
    rfl
  change (((StructureSheaf.toStalk A (q (l x)) ≫ q.stalkMap (l x)) ≫
    l.stalkMap x).hom) a = _
  rw [hleft]
  have H : StructureSheaf.toStalk A ((l ≫ q) x) ≫ (l ≫ q).stalkMap x =
      StructureSheaf.toStalk A ((q' ≫ Spec.map (CommRingCat.ofHom c)) x) ≫
        (q' ≫ Spec.map (CommRingCat.ofHom c)).stalkMap x := by rw [hc]
  rw [H, Scheme.Hom.stalkMap_comp, ← Category.assoc]
  have ht := AlgebraicGeometry.stalkMap_toStalk (CommRingCat.ofHom c) (q' x)
  change (((StructureSheaf.toStalk A _ ≫
    (Spec.map (CommRingCat.ofHom c)).stalkMap (q' x)) ≫ q'.stalkMap x).hom) a = _
  have ht' : StructureSheaf.toStalk A ((Spec.map (CommRingCat.ofHom c)) (q' x)) ≫
      (Spec.map (CommRingCat.ofHom c)).stalkMap (q' x) =
        CommRingCat.ofHom c ≫ StructureSheaf.toStalk D (q' x) := ht
  rw [ht']
  rfl

private theorem flat_quotient_map (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] [Module.Flat R B] (I : Ideal R) :
    Module.Flat (R ⧸ I) (B ⧸ I.map (algebraMap R B)) :=
  Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Prescribed local flat deformations of a proper curve admit a projective algebraization.
The comparison is asserted only on finite jets; it does not identify the unreduced
local rings of the algebraization with the prescribed local algebras.

Source: Stacks Project, Tag 0E7Y, the paragraph beginning "Observe that the system",
with Tags 0DZP, 06HN, 0E7R and 0D4G.
(blueprint: lem-sfb-isolated-curve-local-algebraization).

Proof: Set C(i,n)=B(i)/(t^(n+1)). The quotient is local, flat over
k[[t]]/(t^(n+1)) by base change, and essentially of finite type by reducing a
localized finite-type presentation. The distinguished-polynomial equivalence
`Polynomial.IsDistinguishedAt.algEquivQuotient` for X^(n+1) identifies the
coefficient quotient with k[t]/(t^(n+1)); these identifications commute with reductions and
with evaluation at zero. The adjacent quotient maps are surjective, have kernel
generated by t^(n+1), and respect the specified identification at level zero.
Apply exists_isolatedCurve_formal_lifting to obtain a proper flat finitely
presented compatible system with these local rings. Transport its bases through
the truncation isomorphisms and apply proper_formal_curve_algebraization. Its
compatible isomorphisms give the special-fibre isomorphism and the maps from X
into every jet. Transport the formal-lifting stalk isomorphisms through these
isomorphisms. Their scalar compatibility gives the last equation below.
Properness gives quasi-compactness and quasi-separatedness of the stages. The
empty marked list needs no local data; the empty scheme uses the empty system.
No Cohen--Macaulay, lci, equidimensionality or Fitting hypothesis is used here. -/
theorem isolated_curve_local_algebraization
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (r : ℕ) (p : Fin r → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    (hsmooth : ∀ x ∉ Set.range p, ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f))
    (B : Fin r → Type u) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    [∀ i, Algebra (PowerSeries k) (B i)] [∀ i, Algebra k (B i)]
    [∀ i, IsScalarTower k (PowerSeries k) (B i)]
    [∀ i, Module.Flat (PowerSeries k) (B i)]
    [∀ i, Algebra.EssFiniteType (PowerSeries k) (B i)]
    (eB : ∀ i,
      let : Algebra k (X.presheaf.stalk (p i)) :=
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
          X.presheaf.germ ⊤ (p i) trivial).hom.toAlgebra)
      (B i ⧸ Ideal.span {algebraMap (PowerSeries k) (B i) PowerSeries.X}) ≃ₐ[k]
        X.presheaf.stalk (p i)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k))),
      Flat g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g ∧
      IsHProjective g ∧
      ∃ e : pullback g (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k)))) ≅ X,
        e.hom ≫ f = pullback.snd g (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k)))) ∧
      ∃ j : ∀ n, X ⟶ pullback g (formalCurveBaseι k n),
        (∀ n, j n ≫ pullback.fst g (formalCurveBaseι k n) =
          e.inv ≫ pullback.fst g (Spec.map (CommRingCat.ofHom
            (PowerSeries.constantCoeff (R := k))))) ∧
      ∃ h : ∀ i n,
        (pullback g (formalCurveBaseι k n)).presheaf.stalk (j n (p i))
          ≃+* (B i ⧸ Ideal.span
            {(algebraMap (PowerSeries k) (B i) PowerSeries.X) ^ (n + 1)}),
        ∀ i n a, h i n (isolatedCurveScalarToStalk
          (pullback.snd g (formalCurveBaseι k n)) (j n (p i))
          (Ideal.Quotient.mk _ a)) = Ideal.Quotient.mk _ (algebraMap _ _ a) := by
  classical
  let aStalk (i : Fin r) : Algebra k (X.presheaf.stalk (p i)) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
      X.presheaf.germ ⊤ (p i) trivial).hom.toAlgebra)
  let := aStalk
  let P (n : ℕ) : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X} ^ (n + 1)
  let J (i : Fin r) (n : ℕ) := (P n).map (algebraMap (PowerSeries k) (B i))
  have hJ (i : Fin r) (n : ℕ) : J i n =
      Ideal.span {(algebraMap (PowerSeries k) (B i) PowerSeries.X) ^ (n + 1)} := by
    simp [J, P, Ideal.map_pow, Ideal.map_span, ← Ideal.span_singleton_pow]
  let C (i : Fin r) (n : ℕ) := B i ⧸ J i n
  let aC (i : Fin r) (n : ℕ) : Algebra (isolatedCurveLevelRing k n) (C i n) :=
    ((algebraMap (PowerSeries k ⧸ P n) (C i n)).comp
      (levelPowerSeriesEquiv k n).toRingHom).toAlgebra
  let := aC
  have hnontrivial (i : Fin r) : Nontrivial (C i 0) := by
    let E : C i 0 ≃+* X.presheaf.stalk (p i) :=
      (Ideal.quotientEquivAlgOfEq k (by simpa using hJ i 0)).toRingEquiv.trans
        (eB i).toRingEquiv
    exact E.surjective.nontrivial
  have hJproper (i : Fin r) (n : ℕ) : J i n ≠ ⊤ := by
    have h0 : J i 0 ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp (hnontrivial i)
    apply ne_top_of_le_ne_top h0
    exact Ideal.map_mono (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)))
  have (i : Fin r) (n : ℕ) : Nontrivial (C i n) :=
    Ideal.Quotient.nontrivial_iff.mpr (hJproper i n)
  have (i : Fin r) (n : ℕ) : IsLocalRing (C i n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (J i n)) Ideal.Quotient.mk_surjective
  let (n : ℕ) : Algebra (PowerSeries k) (isolatedCurveLevelRing k n) :=
    ((levelPowerSeriesEquiv k n).symm.toRingHom.comp (Ideal.Quotient.mk (P n))).toAlgebra
  have (i : Fin r) (n : ℕ) : IsScalarTower (PowerSeries k)
      (isolatedCurveLevelRing k n) (C i n) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change Ideal.Quotient.mk (J i n) (algebraMap _ _ a) =
        algebraMap (PowerSeries k ⧸ P n) (C i n)
          (levelPowerSeriesEquiv k n ((levelPowerSeriesEquiv k n).symm
            (Ideal.Quotient.mk (P n) a)))
      rw [AlgEquiv.apply_symm_apply]
      rfl
  have (i : Fin r) (n : ℕ) : Algebra.EssFiniteType (isolatedCurveLevelRing k n)
      (C i n) := Algebra.EssFiniteType.of_comp (PowerSeries k) _ _
  have (i : Fin r) (n : ℕ) : Module.Flat (isolatedCurveLevelRing k n) (C i n) := by
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.comp (.of_bijective (levelPowerSeriesEquiv k n).bijective)
      (RingHom.flat_algebraMap_iff.mpr (flat_quotient_map (PowerSeries k) (B i) (P n)))
  let c (i : Fin r) (n : ℕ) : C i (n + 1) →+* C i n :=
    Ideal.Quotient.factor (Ideal.map_mono
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
  have hcscalar (i : Fin r) (n : ℕ) :
      (c i n).comp (algebraMap (isolatedCurveLevelRing k (n + 1)) (C i (n + 1))) =
        (algebraMap (isolatedCurveLevelRing k n) (C i n)).comp
          (isolatedCurveLevelReduction k n) := by
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change c i n (algebraMap (PowerSeries k ⧸ P (n + 1)) (C i (n + 1))
        (levelPowerSeriesEquiv k (n + 1) (Ideal.Quotient.mk _ a))) =
      algebraMap (PowerSeries k ⧸ P n) (C i n)
        (levelPowerSeriesEquiv k n (Ideal.Quotient.mk _ a))
    simp only [levelPowerSeriesEquiv_mk]
    rfl
  have hcker (i : Fin r) (n : ℕ) : RingHom.ker (c i n) =
      Ideal.span {(algebraMap (isolatedCurveLevelRing k (n + 1)) (C i (n + 1))
        (isolatedCurveLevelParameter k (n + 1))) ^ (n + 1)} := by
    dsimp [c]
    rw [Ideal.Quotient.factor_ker, hJ i n]
    change _ = Ideal.span {(algebraMap (PowerSeries k ⧸ P (n + 1)) (C i (n + 1))
      (levelPowerSeriesEquiv k (n + 1)
        (isolatedCurveLevelParameter k (n + 1)))) ^ (n + 1)}
    rw [levelPowerSeriesEquiv_parameter]
    simp only [Ideal.map_span, Set.image_singleton, map_pow]
    rfl
  let eC (i : Fin r) : C i 0 ≃+* X.presheaf.stalk (p i) :=
    (Ideal.quotientEquivAlgOfEq k (by simpa using hJ i 0)).toRingEquiv.trans
      (eB i).toRingEquiv
  have heC (i : Fin r) (a : k) :
      eC i (algebraMap (isolatedCurveLevelRing k 0) (C i 0)
        ((isolatedCurveLevelZero k).symm a)) = isolatedCurveScalarToStalk f (p i) a := by
    have hz : (isolatedCurveLevelZero k).symm a =
        algebraMap k (isolatedCurveLevelRing k 0) a := by
      simpa using (isolatedCurveLevelZero k).symm.commutes a
    change eC i (algebraMap (PowerSeries k ⧸ P 0) (C i 0)
      (levelPowerSeriesEquiv k 0 ((isolatedCurveLevelZero k).symm a))) = _
    rw [hz, (levelPowerSeriesEquiv k 0).commutes]
    change eC i (Ideal.Quotient.mk (J i 0)
      (algebraMap (PowerSeries k) (B i) (algebraMap k (PowerSeries k) a))) = _
    rw [← IsScalarTower.algebraMap_apply k (PowerSeries k) (B i)]
    change eC i (algebraMap k (C i 0) a) = _
    rw [scalarToStalk_eq]
    exact ((Ideal.quotientEquivAlgOfEq k (by simpa using hJ i 0)).trans
      (eB i)).commutes a
  obtain ⟨Z, q, eZ, z, hZ, heZ, hcart, h, hscalar, hcompat, hspecial⟩ :=
    exists_isolatedCurve_formal_lifting k X f hdim r p hp hclosed hsmooth C c
      hcscalar (fun _ _ ↦ Ideal.Quotient.factor_surjective _) hcker eC heC
  let b (n : ℕ) : Spec (.of (isolatedCurveLevelRing k n)) ≅ formalCurveBase k n :=
    (asIso (Spec.map (CommRingCat.ofHom (levelPowerSeriesEquiv k n).toRingHom))).symm
  let q' (n : ℕ) := q n ≫ (b n).hom
  have hb (n : ℕ) :
      (Spec.map (CommRingCat.ofHom (isolatedCurveLevelReduction k n))) ≫
          (b (n + 1)).hom = (b n).hom ≫ formalCurveBaseStep k n := by
    apply (cancel_mono (b (n + 1)).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply (cancel_epi (b n).inv).mp
    change Spec.map (CommRingCat.ofHom (levelPowerSeriesEquiv k n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (isolatedCurveLevelReduction k n)) = _
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((levelPowerSeriesEquiv k n).toRingHom.comp (isolatedCurveLevelReduction k n))) = _
    rw [levelPowerSeriesEquiv_reduction]
    simp [b, formalCurveBaseStep, ← Spec.map_comp]
  have hcart' (n : ℕ) :
      IsPullback (z n) (q' n) (q' (n + 1)) (formalCurveBaseStep k n) := by
    exact (hcart n).of_iso (Iso.refl _) (Iso.refl _) (b n) (b (n + 1))
      (by simp) (by simp [q']) (by simp [q']) (hb n)
  have (n : ℕ) : IsProper (q n) := (hZ n).1
  have (n : ℕ) : Flat (q n) := (hZ n).2.1
  have (n : ℕ) : LocallyOfFinitePresentation (q n) := (hZ n).2.2
  have (n : ℕ) : IsProper (q' n) := by dsimp [q']; infer_instance
  have (n : ℕ) : Flat (q' n) := by dsimp [q']; infer_instance
  have (n : ℕ) : LocallyOfFinitePresentation (q' n) := by dsimp [q']; infer_instance
  have hdimZ : topologicalKrullDim (Z 0) ≤ (1 : WithBot ℕ∞) := by
    rw [← eZ.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    exact hdim
  obtain ⟨Y, g, hgflat, hgfp, hgqc, hgqs, hgproj, E, hE, hEcompat⟩ :=
    proper_formal_curve_algebraization k Z q' z hcart' hdimZ
  let s : Spec (.of k) ⟶ formalCurveBase k 0 :=
    Spec.map (CommRingCat.ofHom (powerSeriesLevelZero k))
  have hs : IsIso s := by
    have hh : powerSeriesLevelZero k =
        (isolatedCurveLevelZero k).toRingHom.comp
          (levelPowerSeriesEquiv k 0).symm.toRingHom := by
      apply RingHom.ext
      intro a
      have hz := RingHom.congr_fun (levelPowerSeriesEquiv_zero k)
        ((levelPowerSeriesEquiv k 0).symm a)
      simpa using hz
    dsimp [s]
    rw [hh, CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  have hsbase : s ≫ formalCurveBaseι k 0 =
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) := by
    change Spec.map (CommRingCat.ofHom (powerSeriesLevelZero k)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = _
    rw [← Spec.map_comp]
    rfl
  have heZ' : eZ.hom ≫ q' 0 = f ≫ s := by
    dsimp [q']
    rw [← Category.assoc, heZ, Category.assoc]
    congr 1
    apply (cancel_mono (b 0).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change Spec.map (CommRingCat.ofHom (isolatedCurveLevelZero k).toRingHom) =
      Spec.map (CommRingCat.ofHom (powerSeriesLevelZero k)) ≫
        Spec.map (CommRingCat.ofHom (levelPowerSeriesEquiv k 0).toRingHom)
    rw [← Spec.map_comp]
    exact congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h))
      (levelPowerSeriesEquiv_zero k).symm
  have hEinv (n : ℕ) : (E n).inv ≫ pullback.snd g (formalCurveBaseι k n) = q' n := by
    rw [← hE n, Iso.inv_hom_id_assoc]
  let specialSquare : IsPullback (eZ.hom ≫ (E 0).inv)
      f (pullback.snd g (formalCurveBaseι k 0)) s :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.assoc, hEinv, heZ']⟩
  let specialSquare' := specialSquare.paste_horiz
    (IsPullback.of_hasPullback g (formalCurveBaseι k 0))
  have specialSquare'' : IsPullback
      (eZ.hom ≫ (E 0).inv ≫ pullback.fst g (formalCurveBaseι k 0)) f g
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) := by
    simpa only [hsbase, Category.assoc] using specialSquare'
  let e := specialSquare''.isoPullback.symm
  refine ⟨Y, g, hgflat, hgfp, hgqc, hgqs, hgproj, e, ?_, ?_⟩
  · exact specialSquare''.isoPullback_inv_snd
  let j (n : ℕ) : X ⟶ pullback g (formalCurveBaseι k n) :=
    isolatedCurveSpecialMap Z z eZ n ≫ (E n).inv
  refine ⟨j, ?_, ?_⟩
  · intro n
    induction n with
    | zero =>
      change (eZ.hom ≫ (E 0).inv) ≫ _ = _
      exact specialSquare''.isoPullback_hom_fst.symm
    | succ n ih =>
      change (isolatedCurveSpecialMap Z z eZ n ≫ z n) ≫
        (E (n + 1)).inv ≫ _ = _
      rw [Category.assoc, ← hEcompat n]
      exact ih
  · let h' (i : Fin r) (n : ℕ) :=
      ((asIso ((E n).inv.stalkMap
        (isolatedCurveSpecialMap Z z eZ n (p i)))).commRingCatIsoToRingEquiv.trans
          (h i n)).trans (Ideal.quotientEquivAlgOfEq (PowerSeries k) (hJ i n)).toRingEquiv
    refine ⟨h', ?_⟩
    intro i n a
    let x := isolatedCurveSpecialMap Z z eZ n (p i)
    let v : PowerSeries k ⧸ P n := Ideal.Quotient.mk _ a
    have hv := scalarToStalk_naturality (E n).inv
      (pullback.snd g (formalCurveBaseι k n)) (q' n) (RingHom.id _)
      (by simpa using hEinv n) x v
    change (Ideal.quotientEquivAlgOfEq (PowerSeries k) (hJ i n))
      (h i n ((E n).inv.stalkMap x
        (isolatedCurveScalarToStalk (pullback.snd g (formalCurveBaseι k n))
          ((E n).inv x) v))) = _
    rw [hv]
    have hq : q' n ≫ (b n).inv = q n := by simp [q']
    have hv' := scalarToStalk_naturality (𝟙 (Z n)) (q n) (q' n)
      (levelPowerSeriesEquiv k n).toRingHom (by
        simpa [b] using hq.symm) x ((levelPowerSeriesEquiv k n).symm v)
    simp only [Scheme.Hom.stalkMap_id] at hv'
    change isolatedCurveScalarToStalk (q n) x
        ((levelPowerSeriesEquiv k n).symm v) =
      isolatedCurveScalarToStalk (q' n) x
        (levelPowerSeriesEquiv k n ((levelPowerSeriesEquiv k n).symm v)) at hv'
    rw [AlgEquiv.apply_symm_apply] at hv'
    change (Ideal.quotientEquivAlgOfEq (PowerSeries k) (hJ i n))
      (h i n (isolatedCurveScalarToStalk (q' n) x v)) = _
    rw [← hv', hscalar]
    change (Ideal.quotientEquivAlgOfEq (PowerSeries k) (hJ i n))
      (algebraMap (PowerSeries k ⧸ P n) (C i n)
        (levelPowerSeriesEquiv k n ((levelPowerSeriesEquiv k n).symm v))) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl

end AlgebraicGeometry
