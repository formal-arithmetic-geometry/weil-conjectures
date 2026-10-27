/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.DeligneLaumon.ConstantFieldRestriction
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.DeligneLaumon.GeometricallyConnectedClopenSupport
import Sheaf.DeligneLaumon.ClopenReturnRestriction
import Sheaf.DeligneLaumon.AffineLinePullbackIrreducible
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.WeilSheaf.LisseLocus
import WeilConjectures.WeilSheaf.UpperStarExact
import WeilConjectures.WeilSheaf.UpperStarPointwise

/-! # A positive-dimensional connected support model

Source: the geometric-component and dimension-zero steps of
`thm-zl-real-mixed-by-curves`.
(blueprint: lem-zl-simple-lisse-support-model).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

private theorem frobeniusEnd_stalkAt_eq_of_degree_eq
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    (F : WeilSheaf k l Z)
    (t : Spec (.of (AlgebraicClosure k)) ⟶ (Z ↘ Spec (.of k)).geometricFiber)
    {a b : ℕ} (hab : a = b)
    (ha : t ≫ ((Z ↘ Spec (.of k)).geometricGaloisFrobenius ^ a).hom =
      (specGeometricFrobenius k ^ a).hom ≫ t)
    (hb : t ≫ ((Z ↘ Spec (.of k)).geometricGaloisFrobenius ^ b).hom =
      (specGeometricFrobenius k ^ b).hom ≫ t) :
    (F.stalkAt t a ha).frobeniusEnd = (F.stalkAt t b hb).frobeniusEnd := by
  subst b
  rfl

private theorem hasPointwisePowerTransport_upperStar
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    (φ : Y ⟶ Z) [φ.IsOver (Spec (.of k))] :
    HasPointwisePowerTransport (upperStar (k₀ := k) (l := l) φ) φ := by
  intro z
  let x : Z.finitePoints := ⟨φ z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩
  let m := (Z ↘ Spec (.of k)).degreeOver x.1
  let n := (Y ↘ Spec (.of k)).degreeOver z.1
  have hdvd : m ∣ n := by
    have h := Scheme.Hom.degreeOver_dvd_degreeOver_comp φ (Z ↘ Spec (.of k)) z.2
    rwa [comp_over φ (Spec (.of k))] at h
  obtain ⟨hr, hq⟩ := residueCard_eq_pow_of_upperStar (k₀ := k) φ z
  refine ⟨x, n / m, rfl, hr, hq, fun F ↦ ?_⟩
  let s := (Y ↘ Spec (.of k)).geometricFiberPointOfFinitePoint z
  let t := (Z ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x
  let b := Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (.of k)))
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (Y ↘ Spec (.of k)) z
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (Z ↘ Spec (.of k)) x
  have hb : (s ≫ b) ≫ ((Z ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).hom =
      (specGeometricFrobenius k ^ n).hom ≫ (s ≫ b) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, hs, Category.assoc]
  have hbase := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
    (Z ↘ Spec (.of k)) x
  have hbt : (t ≫ (Z ↘ Spec (.of k)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k)) =
      ((s ≫ b) ≫ (Z ↘ Spec (.of k)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k)) := by
    rw [hbase, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc]
    exact (congrArg φ.base
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ z)).symm
  have hnm : n / m * m = n := Nat.div_mul_cancel hdvd
  have htn := comp_geometricGaloisFrobenius_pow_mul t ht (n / m)
  rw [hnm] at htn
  obtain ⟨e₁⟩ := F.nonempty_equiv_stalkAt t (s ≫ b) hbt (hbase ▸ x.2) n htn hb
  have : IsIso (𝟙 _ : (b)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X ⟶
      ((upperStar φ).obj F).obj.carrier.X) := inferInstanceAs (IsIso (𝟙 _))
  obtain ⟨e₂⟩ := nonempty_equiv_stalkAt_of_upperStar (G := (upperStar φ).obj F)
    (θ := 𝟙 _) (upperStar_frobeniusStr_compatible (φ := φ) F) s n hs hb
  have hpow : (F.stalkAt t n htn).frobeniusEnd = (F.stalk x).frobeniusEnd ^ (n / m) := by
    have h := F.frobeniusEnd_stalkAt_mul t
      (Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero (Z ↘ Spec (.of k)) x.2))
      ht (n / m)
    exact (frobeniusEnd_stalkAt_eq_of_degree_eq F t hnm
      (comp_geometricGaloisFrobenius_pow_mul t ht (n / m)) htn).symm.trans h
  let e₀ : ((F.stalk x).powFrobenius (n / m)).Equiv (F.stalkAt t n htn) :=
    .ofComp (LinearEquiv.refl _ _) (by
      simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id,
        FrobeniusModule.powFrobenius_frobeniusEnd, hpow])
  exact ⟨e₀.trans (e₁.trans e₂)⟩

private def equivPow {K : Type v} [Field K] {M N : FrobeniusModule.{w, v} K}
    (e : M.Equiv N) (n : ℕ) : (M.powFrobenius n).Equiv (N.powFrobenius n) where
  toLinearEquiv := e.toLinearEquiv
  map_frobenius x := by
    change e.toLinearEquiv ((M.frobenius ^ n) x) = (N.frobenius ^ n) (e.toLinearEquiv x)
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        e.map_frobenius, ih]

private theorem powerTransport_comp
    {k₀ k₁ k₂ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Field k₂] [Finite k₂] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)] [Fact (ringChar k₂ ≠ l)]
    {X Y Z : Scheme.{u}} [X.Over (Spec (.of k₀))]
    [Y.Over (Spec (.of k₁))] [Z.Over (Spec (.of k₂))]
    {R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l Y}
    {S : WeilSheaf k₁ l Y ⥤ WeilSheaf k₂ l Z}
    {c : Y ⟶ X} {p : Z ⟶ Y}
    (hR : HasPointwisePowerTransport R c) (hS : HasPointwisePowerTransport S p) :
    HasPointwisePowerTransport (R ⋙ S) (p ≫ c) := by
  intro z
  obtain ⟨y, f, hp, hf, hqS, hFS⟩ := hS z
  obtain ⟨x, e, hc, he, hqR, hFR⟩ := hR y
  refine ⟨x, e * f, ?_, Nat.mul_pos he hf, ?_, fun F ↦ ?_⟩
  · rw [Scheme.Hom.comp_apply, hp, hc]
  · rw [hqS, hqR, pow_mul]
  · obtain ⟨a⟩ := hFR F
    obtain ⟨b⟩ := hFS (R.obj F)
    let t : ((F.stalk x).powFrobenius (e * f)).Equiv
        (((F.stalk x).powFrobenius e).powFrobenius f) :=
      .ofComp (LinearEquiv.refl _ _) (by
        simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id,
          FrobeniusModule.powFrobenius_frobeniusEnd, pow_mul])
    exact ⟨t.trans ((equivPow a f).trans b)⟩

/-- Reduce a simple lisse sheaf to its connected geometric support, without
constructing geometric constituents.

Source: blueprint `sec-deligne-laumon-general/sk-i-dl-general-real`, geometric-socle
step of the unit, and `thm-zl-real-mixed-by-curves`, paragraphs 1 and 7.
(blueprint: lem-zl-simple-lisse-support-model).

Proof: The clopen connected components of a smooth affine finite-type scheme are
finite in number. Restriction to each component and extension by zero give Weil
subobjects, so exactly one component supports a simple lisse V. Both nonzero
stalks lie on it. Frobenius acts transitively on its geometric connected
components: an orbit sum would otherwise give a clopen Weil subobject. Choose
one component, and descend it to the finite field fixed by its Frobenius
stabilizer. The return functor on this component is exact, preserves lissity,
and takes V to an arithmetically simple sheaf. A return-stable subobject would
induce a proper Weil subobject by taking the direct sum of its distinct translates.
Both original closed points have lifts on the chosen component, since its
Frobenius translates exhaust the support. The local return at a lift is conjugate
to the original return raised to its residue degree. The field tower gives the
identical exponent for residue cardinalities; this holds for every constructible
sheaf, not only V. Smoothness on the component has a constant relative dimension,
and smoothness plus geometric connectedness makes its geometric fiber irreducible.
If the dimension is positive, retain the component. In dimension zero it is a
finite-field point and the simple Weil object is a line: an eigenline of the
invertible Frobenius is a Weil subobject. Pull the entire functor back to the
affine line over this field, using its origin for both lifts. The line stays
arithmetically simple, pullback is exact and preserves lissity, and the same
pointwise residue-degree and Frobenius-power formulas hold at every closed point.
Thus the replacement has dimension one. -/
theorem exists_simple_lisse_support_model
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsAffine X]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (V : WeilSheaf k₀ l X) (hV : V.IsIrreducibleLisse)
    (x y : X.finitePoints)
    (hx : Nontrivial (V.stalk x).carrier) (hy : Nontrivial (V.stalk y).carrier) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₀ k₁)
      (_ : Fact (ringChar k₁ ≠ l)) (d : ℕ) (C : Scheme.{u})
      (_ : C.Over (Spec (CommRingCat.of k₁))) (_ : IsAffine C)
      (_ : SmoothOfRelativeDimension d (C ↘ Spec (CommRingCat.of k₁)))
      (_ : GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁)))
      (_ : IsSeparated (C ↘ Spec (CommRingCat.of k₁)))
      (_ : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁)))
      (_ : QuasiCompact (C ↘ Spec (CommRingCat.of k₁)))
      (_ : IrreducibleSpace (C ↘ Spec (CommRingCat.of k₁)).geometricFiber)
      (R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C)
      (_ : PreservesFiniteLimits R) (_ : PreservesFiniteColimits R) (c : C ⟶ X),
      0 < d ∧ (R.obj V).IsIrreducibleLisse ∧
      (∀ F : WeilSheaf k₀ l X, F.IsLisse → (R.obj F).IsLisse) ∧
      HasPointwisePowerTransport R c ∧
      c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
        (C ↘ Spec (CommRingCat.of k₁)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) ∧
      ∃ s t : C.finitePoints, c s.1 = x.1 ∧ c t.1 = y.1 := by
  classical
  -- Use a relative affine line in every dimension, avoiding the point-flag step.
  obtain ⟨k₁, hk₁, hfin₁, halg₁, hl₁, d, C₀, hover₀, haff₀, hsm₀, hconn₀,
    hsep₀, hft₀, hqc₀, c₀, hopen₀, hclosed₀, hc₀, s₀, t₀, hs₀, ht₀⟩ :=
    exists_geometrically_connected_clopen_support V hV x y hx hy
  obtain ⟨R₀, hlim₀, hcolim₀, hlisse₀, hpoint₀, hirr₀⟩ :=
    exists_clopen_return_restriction (k₀ := k₀) (k₁ := k₁) (l := l) c₀ hc₀
  have hV₀ : (R₀.obj V).IsIrreducibleLisse := by
    apply hirr₀ V hV s₀
    have hs : (⟨c₀ s₀.1, Scheme.Hom.map_mem_finitePoints c₀ s₀.2⟩ :
        X.finitePoints) = x := Subtype.ext hs₀
    simpa only [hs] using hx
  have hsmC : Smooth (C₀ ↘ Spec (.of k₁)) := SmoothOfRelativeDimension.smooth d _
  obtain ⟨A, hover, haff, hconn, hft, hqc, hsep, hgeoFiber, p, z,
    hpover, hzover, hsmP, hz, hV'⟩ :=
    IsIrreducibleLisse.exists_affineLine_model (k := k₁) (l := l) (C := C₀)
      (V := R₀.obj V) hV₀
  have hp : p ≫ (C₀ ↘ Spec (.of k₁)) = A ↘ Spec (.of k₁) := comp_over p _
  have hsmA : SmoothOfRelativeDimension (1 + d) (A ↘ Spec (.of k₁)) := by
    rw [← hp]
    exact smoothOfRelativeDimension_comp 1 d p (C₀ ↘ Spec (.of k₁))
  let s : A.finitePoints := ⟨z s₀.1, Scheme.Hom.map_mem_finitePoints z s₀.2⟩
  let t : A.finitePoints := ⟨z t₀.1, Scheme.Hom.map_mem_finitePoints z t₀.2⟩
  let P := upperStar (k₀ := k₁) (l := l) p
  refine ⟨k₁, hk₁, hfin₁, halg₁, hl₁, 1 + d, A, inferInstance, haff, hsmA,
    hconn, hsep, hft, hqc, hgeoFiber, R₀ ⋙ P, inferInstance, inferInstance,
    p ≫ c₀, Nat.add_pos_left Nat.zero_lt_one d, hV', ?_, ?_, ?_, s, t, ?_, ?_⟩
  · intro F hF
    exact IsLisse.upperStar (k₀ := k₁) (l := l) (X := A) (Y := C₀)
      (F := R₀.obj F) (hlisse₀ F hF) p
  · exact powerTransport_comp (k₀ := k₀) (k₁ := k₁) (k₂ := k₁)
      (X := X) (Y := C₀) (Z := A) (R := R₀) (S := P) (c := c₀) (p := p)
      hpoint₀ (hasPointwisePowerTransport_upperStar (k := k₁) (l := l) (Y := A)
        (Z := C₀) p)
  · rw [Category.assoc, hc₀, ← Category.assoc, hp]
  · change (z ≫ p ≫ c₀) s₀.1 = x.1
    rw [← Category.assoc, hz, Category.id_comp]
    exact hs₀
  · change (z ≫ p ≫ c₀) t₀.1 = y.1
    rw [← Category.assoc, hz, Category.id_comp]
    exact ht₀

end AlgebraicGeometry.WeilSheaf
