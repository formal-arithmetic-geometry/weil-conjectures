/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.KrullDimension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.PointCount
import Mathlib.FieldTheory.Finite.GaloisField
/-! # Weighted point counting over the chosen finite extensions
Source: current Euler-product proof Step 3; the finite-field fibre argument of
WeilConjectures/PointCount.lean is extended from its canonical Galois field to any
finite extension, then applied to the chosen subfield of the algebraic closure.
(blueprint: lem-condensed-weil-euler-weighted-point-count).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CondensedWeilEuler.PointCounting
open NativeCondensedModule
variable {X : Scheme.{u}} {k : Type u} [Field k]
/-- The fiber of the point-embedding correspondence over a point `x`: embeddings of the
residue field of `x` into `K` compatible with the base field embeddings. -/
private def FieldPointFiber (f : X.Hom (Spec (.of k))) (K : Type u) [Field K]
    [Algebra k K] (x : X) : Type u :=
  {φ : X.residueField x ⟶ CommRingCat.of K //
    φ.hom.comp (f.residueFieldAlgebraMap x) = algebraMap k K}

/-- The fibers of the point-embedding correspondence are `k`-algebra homomorphisms of
residue fields. -/
private noncomputable def algHomEquivFieldPointFiber (f : X.Hom (Spec (.of k)))
    (K : Type u) [Field K] [Algebra k K] (x : X) :
    let := (f.residueFieldAlgebraMap x).toAlgebra
    (X.residueField x →ₐ[k] K) ≃ FieldPointFiber f K x :=
  let := (f.residueFieldAlgebraMap x).toAlgebra
  { toFun := fun ψ ↦ ⟨CommRingCat.ofHom ψ.toRingHom, ψ.comp_algebraMap⟩
    invFun := fun φ ↦ { toRingHom := φ.1.hom, commutes' := fun a ↦ RingHom.congr_fun φ.2 a }
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- The rational points of `X` over `k` with values in `K` are pairs of a point of `X`
and a compatible embedding of its residue field into `K`. -/
private noncomputable def fieldPointsEquivSigma (f : X.Hom (Spec (.of k))) (K : Type u) [Field K]
    [Algebra k K] :
    f.fieldPoints K ≃ Σ x : X, FieldPointFiber f K x :=
  ((SpecToEquivOfField K X).symm.subtypeEquiv fun p ↦
      (comp_eq_iff f p.1 p.2).symm).symm.trans
    { toFun := fun p ↦ ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun q ↦ ⟨⟨q.1, q.2.1⟩, q.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The rational point attached to a point `x` of `X` and an embedding of its residue field lies
over `x`. -/
private lemma fieldPointsEquivSigma_symm_base (f : X.Hom (Spec (.of k))) (K : Type u) [Field K]
    [Algebra k K] (q : Σ x : X, FieldPointFiber f K x) :
    ((fieldPointsEquivSigma f K).symm q).1.base (IsLocalRing.closedPoint K) = q.1 :=
  X.fromSpecResidueField_apply q.1 _

/-- Counting the fibers of the point-embedding correspondence via the Galois theory of
finite fields: over the degree `n` extension of `k`, the fiber over `x` has `deg x`
elements if `deg x ∣ n` and is empty otherwise. -/
private lemma nat_card_fieldPointFiber [Finite k] (f : X.Hom (Spec (.of k)))
    (K : Type u) [Field K] [Algebra k K] [Finite K] (x : X) :
    Nat.card (FieldPointFiber f (K) x) =
      if f.degreeOver x ∣ Module.finrank k K then f.degreeOver x else 0 := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  rw [← Nat.card_congr (algHomEquivFieldPointFiber f (K) x)]
  by_cases hdvd : f.degreeOver x ∣ Module.finrank k K
  · rw [if_pos hdvd]
    have hdvd' : Module.finrank k (X.residueField x) ∣
        Module.finrank k (K) := by
      exact hdvd
    rw [FiniteField.natCard_algHom_of_finrank_dvd hdvd']
    rfl
  · rw [if_neg hdvd]
    have : IsEmpty (X.residueField x →ₐ[k] K) := by
      rw [← not_nonempty_iff, FiniteField.nonempty_algHom_iff_finrank_dvd]
      exact hdvd
    exact Nat.card_of_isEmpty

private lemma degreeOver_dvd_of_fieldPointFiber [Finite k] (f : X.Hom (Spec (.of k)))
    (K : Type u) [Field K] [Algebra k K] [Finite K] {x : X}
    (φ : FieldPointFiber f (K) x) :
    f.degreeOver x ∣ Module.finrank k K := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have h : Nonempty (X.residueField x →ₐ[k] K) :=
    ⟨(algHomEquivFieldPointFiber f (K) x).symm φ⟩
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd] at h
  exact h

/-- A point with nonempty fiber of the point-embedding correspondence into a finite field
has finite residue field. -/
private lemma mem_finitePoints_of_fieldPointFiber (f : X.Hom (Spec (.of k))) {K : Type u}
    [Field K] [Algebra k K] [Finite K] {x : X} (φ : FieldPointFiber f K x) :
    x ∈ X.finitePoints :=
  X.mem_finitePoints.mpr (Finite.of_injective _ φ.1.hom.injective)

/-- The fibers of the point-embedding correspondence over points with finite residue field
are finite. -/
private lemma finite_fieldPointFiber (f : X.Hom (Spec (.of k))) {K : Type u} [Field K]
    [Algebra k K] [Finite K] {x : X} (hx : x ∈ X.finitePoints) :
    Finite (FieldPointFiber f K x) := by
  have : Finite (X.residueField x) := X.mem_finitePoints.mp hx
  exact Finite.of_injective
    (fun φ : FieldPointFiber f K x ↦ (φ.1.hom : X.residueField x → K))
    fun φ ψ h ↦ Subtype.ext (CommRingCat.hom_ext (DFunLike.coe_injective h))

/-- Group a function on extension-valued points by its closed image.
Source: current Euler-product proof Step 3.
Proof: the residue-field correspondence identifies points with pairs (x, embedding).
Finite-field Galois theory counts these embeddings by deg(x) when deg(x) divides the
extension degree, and by zero otherwise. Sum over the finite fibres and their images.
(blueprint: lem-condensed-weil-euler-weighted-point-count). -/
theorem weighted_fieldPoints [Finite k] (f : X.Hom (Spec (.of k)))
    [QuasiCompact f] [LocallyOfFiniteType f]
    (K : Type u) [Field K] [Algebra k K] [Finite K] {M : Type*} [AddCommMonoid M]
    (φ : f.fieldPoints (K) → M) (g : X.finitePoints → M)
    (hφ : ∀ y (x : X.finitePoints), y.1.base (IsLocalRing.closedPoint _) = x.1 → φ y = g x)
    {T : Finset X.finitePoints}
    (hT : ∀ x : X.finitePoints, f.degreeOver x.1 ∣ Module.finrank k K → x ∈ T) :
    ∑ᶠ y, φ y = ∑ x ∈ T with f.degreeOver x.1 ∣ Module.finrank k K, f.degreeOver x.1 • g x := by
  classical
  set T' : Finset X.finitePoints :=
    T.filter (fun x ↦ f.degreeOver x.1 ∣ Module.finrank k K) with hT'
  have h₁ : ∀ (x : X), FieldPointFiber f K x → x ∈ X.finitePoints := fun x φ ↦
    mem_finitePoints_of_fieldPointFiber f φ
  have h₂ : ∀ (x : X) (φ : FieldPointFiber f K x), (⟨x, h₁ x φ⟩ : X.finitePoints) ∈ T' :=
    fun x φ ↦ Finset.mem_filter.mpr
      ⟨hT _ (degreeOver_dvd_of_fieldPointFiber f K φ),
        degreeOver_dvd_of_fieldPointFiber f K φ⟩
  let E : (Σ x : X, FieldPointFiber f K x) ≃ Σ x : T', FieldPointFiber f K x.1.1 :=
    { toFun := fun p ↦ ⟨⟨⟨p.1, h₁ p.1 p.2⟩, h₂ p.1 p.2⟩, p.2⟩
      invFun := fun q ↦ ⟨q.1.1.1, q.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have : ∀ q : T', Finite (FieldPointFiber f K q.1.1) := fun q ↦
    finite_fieldPointFiber f q.1.2
  let _ : ∀ q : T', Fintype (FieldPointFiber f K q.1.1) := fun q ↦ Fintype.ofFinite _
  rw [← finsum_comp_equiv ((fieldPointsEquivSigma f K).trans E).symm,
    finsum_eq_sum_of_fintype, Fintype.sum_sigma]
  calc ∑ q : T', ∑ p : FieldPointFiber f K q.1.1,
        φ (((fieldPointsEquivSigma f K).trans E).symm ⟨q, p⟩)
      = ∑ q : T', ∑ _p : FieldPointFiber f K q.1.1, g q.1 :=
        Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ hφ _ _ (by
          rw [Equiv.symm_trans_apply]
          exact fieldPointsEquivSigma_symm_base f K _)
    _ = ∑ q : T', f.degreeOver q.1.1 • g q.1 := Finset.sum_congr rfl fun q _ ↦ by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
          nat_card_fieldPointFiber f K, if_pos (Finset.mem_filter.mp q.2).2]
    _ = ∑ x ∈ T', f.degreeOver x.1 • g x :=
        Finset.sum_coe_sort T' (fun x : X.finitePoints ↦ f.degreeOver x.1 • g x)


private theorem extension_finrank (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m) :
    letI := (D.extensionEmbedding m hm).toAlgebra
    Module.finrank D.k₀ (D.extensionSubfield m hm) = m := by
  let := (D.extensionEmbedding m hm).toAlgebra
  have hc : Nat.card (D.extensionSubfield m hm) = D.q ^ m :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.1
  have : Finite (D.extensionSubfield m hm) := Nat.finite_of_card_ne_zero (by
    rw [hc, ← D.card_base]
    exact pow_ne_zero m Nat.card_pos.ne')
  apply Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card D.k₀)
  dsimp only
  rw [← Module.natCard_eq_pow_finrank, hc, D.card_base]

private def extensionPointsEquiv (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) :
    letI := (D.extensionEmbedding m hm).toAlgebra
    D.extensionPoints X₀ m hm ≃ X₀.hom.fieldPoints (D.extensionSubfield m hm) := by
  letI := (D.extensionEmbedding m hm).toAlgebra
  exact
    { toFun := fun y ↦ ⟨y.left, Over.w y⟩
      invFun := fun y ↦ Over.homMk y.1 y.2
      left_inv := fun y ↦ by apply Over.OverMorphism.ext; rfl
      right_inv := fun y ↦ rfl }

/-- The weighted point sum for the finite subfield fixed by the finite-field datum.
Source: current Euler-product proof Step 3.
Proof: its cardinality q^m gives extension degree m, by the finite-vector-space
cardinality formula and injectivity of powers of q > 1. Morphisms over the base are
exactly field-valued points. Finite residue fields are exactly closed points. Apply
the arbitrary-extension fibre count and transport the finite indexing set through
these identifications. Empty point sets give empty sums.
(blueprint: lem-condensed-weil-euler-weighted-point-count). -/
theorem weighted_extensionPoints (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) {M : Type*} [AddCommMonoid M]
    (φ : D.extensionPoints X₀ m hm → M) (g : ClosedPoint D X₀ → M)
    (hφ : ∀ y (x : ClosedPoint D X₀),
      y.left (IsLocalRing.closedPoint _) = x.1 → φ y = g x)
    {T : Finset (ClosedPoint D X₀)}
    (hT : ∀ x, localClosedPointDegree D X₀ x ∣ m → x ∈ T) :
    ∑ᶠ y, φ y = ∑ x ∈ T with localClosedPointDegree D X₀ x ∣ m,
      localClosedPointDegree D X₀ x • g x := by
  classical
  let := (D.extensionEmbedding m hm).toAlgebra
  have hc : Nat.card (D.extensionSubfield m hm) = D.q ^ m :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.1
  have : Finite (D.extensionSubfield m hm) := Nat.finite_of_card_ne_zero (by
    rw [hc, ← D.card_base]
    exact pow_ne_zero m Nat.card_pos.ne')
  let e : X₀.left.finitePoints ≃ ClosedPoint D X₀ :=
    Equiv.setCongr (X₀.hom.finitePoints_eq_closedPoints)
  let p := extensionPointsEquiv D X₀ m hm
  let S := T.map e.symm.toEmbedding
  have he (x : X₀.left.finitePoints) :
      X₀.hom.degreeOver x.1 = localClosedPointDegree D X₀ (e x) := rfl
  have h := weighted_fieldPoints X₀.hom (D.extensionSubfield m hm)
    (φ ∘ p.symm) (g ∘ e) (fun y x h ↦ hφ (p.symm y) (e x) h)
    (T := S) (by
      intro x hx
      apply Finset.mem_map.mpr
      refine ⟨e x, hT (e x) ?_, e.symm_apply_apply x⟩
      simpa only [he, extension_finrank D m hm] using hx)
  simp only [Function.comp_apply] at h
  rw [finsum_comp_equiv p.symm] at h
  rw [h]
  apply Finset.sum_bij (fun x _ ↦ e x)
  · intro x hx
    obtain ⟨hx, hd⟩ := Finset.mem_filter.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_filter.mpr ⟨by simpa using hy, by
      simpa only [he, extension_finrank D m hm] using hd⟩
  · intro x hx y hy hxy
    exact e.injective hxy
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_map.mpr ⟨y, (Finset.mem_filter.mp hy).1, rfl⟩, ?_⟩
    simpa only [he, e.apply_symm_apply, extension_finrank D m hm]
      using (Finset.mem_filter.mp hy).2
  · intro x hx
    rfl

/-- An extension-valued point above x forces deg(x) to divide the extension degree.
Source: Euler-product proof Steps 2 and 3.
Proof: the residue-field correspondence supplies a base-compatible embedding of
kappa(x) in the chosen extension. Finite-field Galois theory makes its degree divide
the extension degree, which is m by its cardinality q^m.
(blueprint: lem-condensed-weil-euler-weighted-point-count). -/
theorem degree_dvd_of_extensionPoint (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) (x : ClosedPoint D X₀)
    (hy : y.left (IsLocalRing.closedPoint _) = x.val) :
    localClosedPointDegree D X₀ x ∣ m := by
  let := (D.extensionEmbedding m hm).toAlgebra
  have hc : Nat.card (D.extensionSubfield m hm) = D.q ^ m :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.1
  have : Finite (D.extensionSubfield m hm) := Nat.finite_of_card_ne_zero (by
    rw [hc, ← D.card_base]
    exact pow_ne_zero m Nat.card_pos.ne')
  let q := fieldPointsEquivSigma X₀.hom (D.extensionSubfield m hm)
    ((extensionPointsEquiv D X₀ m hm) y)
  have hbase : q.1 = x.val := by
    have h := fieldPointsEquivSigma_symm_base X₀.hom (D.extensionSubfield m hm) q
    rw [Equiv.symm_apply_apply] at h
    exact h.symm.trans hy
  have hd := degreeOver_dvd_of_fieldPointFiber X₀.hom (D.extensionSubfield m hm) q.2
  change X₀.hom.degreeOver x.val ∣ m
  simpa only [extension_finrank D m hm, hbase] using hd


end WeilConjectures.CondensedWeilEuler.PointCounting
