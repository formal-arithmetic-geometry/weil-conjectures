/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.GroupTheory.Index
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# The trace-polynomial morphism of Artin–Schreier covers

Source: Laumon, Transformation de Fourier (1987), (1.1.3), pp. 139–140, Lang torsor
pushout; the explicit polynomial realization is supplied by the DAG proof
(blueprint: lem-a1-artin-schreier-trace-cover-map).

The covers are the actual pullbacks of the upstream Artin–Schreier map along the section
specified by the function. Thus their affine charts are the displayed polynomial quotients.
The structure below specifies the translations and trace map by their coordinate formulas,
which uniquely determine these morphisms over the base. No maps are chosen arbitrarily.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section



/-- The cover `y^n-y=f`, constructed as the pullback of the upstream Artin–Schreier map.
Source: Laumon (1.1.3), pp. 139–140; affine charts as in Stacks 01LX
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierFunctionCover (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)) : Scheme.{u} :=
  pullback (AffineSpace.artinSchreierMap PUnit X n)
    (AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit ↦ f))

/-- The structural projection of `y^n-y=f` to `X`.
Source: Laumon (1.1.3), pp. 139–140
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierFunctionProjection (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)) :
    artinSchreierFunctionCover X n f ⟶ X :=
  pullback.snd _ _

/-- The tautological root `y` on the cover `y^n-y=f`.
Source: the explicit coordinates in the DAG proof of Laumon (1.1.3)
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierFunctionRoot (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)) :
    Γ(artinSchreierFunctionCover X n f, ⊤) :=
  (pullback.fst (AffineSpace.artinSchreierMap PUnit X n)
    (AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit ↦ f))).appTop
      (AffineSpace.coord X PUnit.unit)

/-- A constant from the base field, as a global regular function.
Source: Laumon (0.2), (1.1.3); the given scheme-over-field structure
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierBaseConstants (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] : k →+* Γ(X, ⊤) :=
  (X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The polynomial `Θ_b = ∑ i < r, (b y)^(p^i)`, over any ring of sections, including zero.
Source: the explicit realization of Laumon (1.1.3) in the DAG proof
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierTracePolynomial {A : Type u} [CommRing A] (p r : ℕ) (b : A) : Polynomial A :=
  ∑ i ∈ Finset.range r, (Polynomial.C b * Polynomial.X) ^ (p ^ i)

/-- The canonical map of geometric fibre schemes induced by a morphism over `X`.
Source: base change of the maps in Laumon (1.1.3), Stacks 01LX
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
def artinSchreierFibreMap {X Y Z T : Scheme.{u}} (π : Y ⟶ X) (ρ : Z ⟶ X)
    (x : T ⟶ X) (a : Y ⟶ Z) (ha : a ≫ ρ = π) : pullback π x ⟶ pullback ρ x :=
  pullback.map π x ρ x a (𝟙 T) (𝟙 X)
    (by simpa only [Category.comp_id] using ha.symm) (by simp)

attribute [local irreducible] artinSchreierFunctionCover artinSchreierFunctionProjection
  artinSchreierFunctionRoot artinSchreierBaseConstants

/-- The canonical translations and trace morphism on the two explicit covers. The fields
`σ_root`, `τ_root`, and `θ_root`, together with being over `X`, uniquely specify the maps.
Source: the coordinate construction in Laumon (1.1.3), pp. 139–140, expanded in the DAG proof
(blueprint: lem-a1-artin-schreier-trace-cover-map). -/
structure ArtinSchreierTraceMaps (k : Type u) [Field k] (p r : ℕ) [Algebra (ZMod p) k]
    (b : k) (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) where
  σ : k → (artinSchreierFunctionCover X (p ^ r) f ≅ artinSchreierFunctionCover X (p ^ r) f)
  τ : ZMod p →
    (artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f) ≅
      artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f))
  θ : artinSchreierFunctionCover X (p ^ r) f ⟶
    artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f)
  σ_over (c : k) : (σ c).hom ≫ artinSchreierFunctionProjection X (p ^ r) f =
    artinSchreierFunctionProjection X (p ^ r) f
  τ_over (d : ZMod p) : (τ d).hom ≫
    artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f) =
      artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)
  θ_over : θ ≫
    artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f) =
      artinSchreierFunctionProjection X (p ^ r) f
  σ_root (c : k) : (σ c).hom.appTop (artinSchreierFunctionRoot X (p ^ r) f) =
    artinSchreierFunctionRoot X (p ^ r) f +
      (artinSchreierFunctionProjection X (p ^ r) f).appTop (artinSchreierBaseConstants k X c)
  τ_root (d : ZMod p) : (τ d).hom.appTop
    (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
      artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f) +
        (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)).appTop
          (artinSchreierBaseConstants k X (algebraMap (ZMod p) k d))
  θ_root : θ.appTop
    (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
      (artinSchreierTracePolynomial p r
        ((artinSchreierFunctionProjection X (p ^ r) f).appTop
          (artinSchreierBaseConstants k X b))).eval (artinSchreierFunctionRoot X (p ^ r) f)
  σ_zero : (σ 0).hom = 𝟙 _
  σ_add (c d : k) : (σ (c + d)).hom = (σ c).hom ≫ (σ d).hom
  τ_zero : (τ 0).hom = 𝟙 _
  τ_add (c d : ZMod p) : (τ (c + d)).hom = (τ c).hom ≫ (τ d).hom

private lemma trace_telescopes {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime)
    (hA : (p : A) = 0) (z : A) (r : ℕ) :
    (∑ i ∈ Finset.range r, z ^ (p ^ i)) ^ p -
      (∑ i ∈ Finset.range r, z ^ (p ^ i)) = z ^ (p ^ r) - z := by
  have hadd (a b : A) : (a + b) ^ p = a ^ p + b ^ p := by
    simpa using (iterateFrobeniusOfPrime A hp hA 1).map_add a b
  induction r with
  | zero => simp [hp.ne_zero]
  | succ r ih =>
    rw [Finset.sum_range_succ, hadd, pow_succ, pow_mul]
    linear_combination ih

private lemma trace_polynomial_identity {k A : Type*} [Field k] [Fintype k] [CommRing A]
    (p r : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ r)
    (φ : k →+* A) (b : k) :
    artinSchreierTracePolynomial p r (φ b) ^ p -
      artinSchreierTracePolynomial p r (φ b) =
      Polynomial.C (φ b) * (Polynomial.X ^ (p ^ r) - Polynomial.X) := by
  have hp : (p : Polynomial A) = 0 := by
    rw [← map_natCast (Polynomial.C.comp φ), CharP.cast_eq_zero, map_zero]
  have hb : (φ b) ^ (p ^ r) = φ b := by
    rw [← map_pow, ← hcard, FiniteField.pow_card]
  rw [artinSchreierTracePolynomial, trace_telescopes p Fact.out hp,
    mul_pow, ← Polynomial.C_pow, hb]
  ring

private lemma appTop_comp_apply {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (s : Γ(Z, ⊤)) : (a ≫ b).appTop s = a.appTop (b.appTop s) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

attribute [local semireducible] artinSchreierFunctionCover artinSchreierFunctionProjection
  artinSchreierFunctionRoot

private lemma cover_root_equation (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)) :
    artinSchreierFunctionRoot X n f ^ n - artinSchreierFunctionRoot X n f =
      (artinSchreierFunctionProjection X n f).appTop f := by
  unfold artinSchreierFunctionRoot artinSchreierFunctionProjection artinSchreierFunctionCover
  have h := congrArg (fun g ↦ g.appTop (AffineSpace.coord X PUnit.unit))
    (pullback.condition (f := AffineSpace.artinSchreierMap PUnit X n)
      (g := AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit ↦ f)))
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow,
    AffineSpace.homOfVector_appTop_coord, artinSchreierFunctionRoot,
    artinSchreierFunctionProjection] using h

private lemma cover_fst_over (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)) :
    pullback.fst (AffineSpace.artinSchreierMap PUnit X n)
      (AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit ↦ f)) ≫ 𝔸(PUnit; X) ↘ X =
      artinSchreierFunctionProjection X n f := by
  rw [← AffineSpace.artinSchreierMap_over PUnit X n, pullback.condition_assoc,
    AffineSpace.homOfVector_over, Category.comp_id]
  rfl

private lemma cover_hom_ext {X T : Scheme.{u}} {n : ℕ} {f : Γ(X, ⊤)}
    {a b : T ⟶ artinSchreierFunctionCover X n f}
    (ho : a ≫ artinSchreierFunctionProjection X n f =
      b ≫ artinSchreierFunctionProjection X n f)
    (hy : a.appTop (artinSchreierFunctionRoot X n f) =
      b.appTop (artinSchreierFunctionRoot X n f)) : a = b := by
  apply pullback.hom_ext _ ho
  apply AffineSpace.hom_ext
  · simpa only [Category.assoc, cover_fst_over] using ho
  · intro i
    cases i
    exact hy

private def cover_lift {X T : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤))
    (h : T ⟶ X) (y : Γ(T, ⊤)) (hy : y ^ n - y = h.appTop f) :
    T ⟶ artinSchreierFunctionCover X n f :=
  pullback.lift (AffineSpace.homOfVector h (fun _ : PUnit ↦ y)) h (by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      cases i
      simpa using hy)

private lemma cover_lift_over {X T : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤))
    (h : T ⟶ X) (y : Γ(T, ⊤)) (hy : y ^ n - y = h.appTop f) :
    cover_lift n f h y hy ≫ artinSchreierFunctionProjection X n f = h := by
  simp [cover_lift, artinSchreierFunctionProjection]

private lemma cover_lift_root {X T : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤))
    (h : T ⟶ X) (y : Γ(T, ⊤)) (hy : y ^ n - y = h.appTop f) :
    (cover_lift n f h y hy).appTop (artinSchreierFunctionRoot X n f) = y := by
  unfold artinSchreierFunctionRoot artinSchreierFunctionCover cover_lift
  rw [← appTop_comp_apply]
  simp

attribute [local irreducible] cover_lift

private lemma cover_finite_etale {k : Type*} [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] (hr : 1 ≤ r)
    (hcard : Fintype.card k = p ^ r) (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤))
    (f : Γ(X, ⊤)) :
    IsFinite (artinSchreierFunctionProjection X (p ^ r) f) ∧
      Etale (artinSchreierFunctionProjection X (p ^ r) f) := by
  have hn : p ^ r ≠ 1 := by
    rw [← hcard]
    exact ne_of_gt Fintype.one_lt_card
  have hp : (p : Γ(X, ⊤)) = 0 := by
    rw [← map_natCast φ, CharP.cast_eq_zero, map_zero]
  have hq : ((p ^ r : ℕ) : Γ(X, ⊤)) = 0 := by
    rw [Nat.cast_pow, hp, zero_pow (by omega)]
  have := AffineSpace.isFinite_artinSchreierMap PUnit X hn
  have := AffineSpace.etale_artinSchreierMap PUnit X hq
  constructor <;> unfold artinSchreierFunctionProjection <;> infer_instance

private lemma cover_finite (X : Scheme.{u}) (n : ℕ) (hn : n ≠ 1)
    (f : Γ(X, ⊤)) : IsFinite (artinSchreierFunctionProjection X n f) := by
  have := AffineSpace.isFinite_artinSchreierMap PUnit X hn
  unfold artinSchreierFunctionProjection
  infer_instance

-- Use the coordinate API instead of unfolding the chosen categorical pullbacks.
attribute [local irreducible] artinSchreierFunctionCover artinSchreierFunctionProjection
  artinSchreierFunctionRoot

private lemma finite_field_add_pow {k A : Type*} [Field k] [Fintype k] [CommRing A]
    (n : ℕ) (hcard : Fintype.card k = n) (φ : k →+* A) (a b : A) :
    (a + b) ^ n = a ^ n + b ^ n := by
  obtain ⟨r, hp, hr⟩ := FiniteField.card k (ringChar k)
  have hz : (ringChar k : A) = 0 := by
    rw [← map_natCast φ, ringChar.Nat.cast_ringChar, map_zero]
  rw [← hcard, hr]
  exact (iterateFrobeniusOfPrime A hp hz r).map_add a b

private lemma cover_translation_equation {k : Type*} [Field k] [Fintype k]
    (n : ℕ) (hcard : Fintype.card k = n)
    (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤)) (f : Γ(X, ⊤)) (c : k) :
    (artinSchreierFunctionRoot X n f +
      (artinSchreierFunctionProjection X n f).appTop (φ c)) ^ n -
        (artinSchreierFunctionRoot X n f +
          (artinSchreierFunctionProjection X n f).appTop (φ c)) =
      (artinSchreierFunctionProjection X n f).appTop f := by
  let ψ := (artinSchreierFunctionProjection X n f).appTop.hom.comp φ
  have hadd := finite_field_add_pow n hcard ψ (artinSchreierFunctionRoot X n f) (ψ c)
  have hc : ψ c ^ n = ψ c := by
    rw [← map_pow]
    exact congrArg ψ (hcard ▸ FiniteField.pow_card c)
  change (_ + ψ c) ^ n - (_ + ψ c) = _
  rw [hadd, hc]
  linear_combination cover_root_equation X n f

private def cover_translation {k : Type*} [Field k] [Fintype k]
    (n : ℕ) (hcard : Fintype.card k = n)
    (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤)) (f : Γ(X, ⊤)) (c : k) :
    artinSchreierFunctionCover X n f ⟶ artinSchreierFunctionCover X n f :=
  cover_lift n f (artinSchreierFunctionProjection X n f)
    (artinSchreierFunctionRoot X n f +
      (artinSchreierFunctionProjection X n f).appTop (φ c))
    (cover_translation_equation n hcard X φ f c)

private lemma cover_translation_over {k : Type*} [Field k] [Fintype k]
    (n : ℕ) (hcard : Fintype.card k = n)
    (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤)) (f : Γ(X, ⊤)) (c : k) :
    cover_translation n hcard X φ f c ≫ artinSchreierFunctionProjection X n f =
      artinSchreierFunctionProjection X n f :=
  cover_lift_over _ _ _ _ _

private lemma cover_translation_root {k : Type*} [Field k] [Fintype k]
    (n : ℕ) (hcard : Fintype.card k = n)
    (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤)) (f : Γ(X, ⊤)) (c : k) :
    (cover_translation n hcard X φ f c).appTop (artinSchreierFunctionRoot X n f) =
      artinSchreierFunctionRoot X n f +
        (artinSchreierFunctionProjection X n f).appTop (φ c) :=
  cover_lift_root _ _ _ _ _

attribute [local irreducible] cover_translation

private lemma cover_translation_zero {k : Type*} [Field k] [Fintype k]
    (n : ℕ) (hcard : Fintype.card k = n)
    (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤)) (f : Γ(X, ⊤)) :
    cover_translation n hcard X φ f 0 = 𝟙 _ := by
  apply cover_hom_ext
  · simp [cover_translation_over]
  · simp [cover_translation_root]

private lemma cover_translation_add {k : Type*} [Field k] [Fintype k]
    (n : ℕ) (hcard : Fintype.card k = n)
    (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤)) (f : Γ(X, ⊤)) (c d : k) :
    cover_translation n hcard X φ f (c + d) =
      cover_translation n hcard X φ f c ≫ cover_translation n hcard X φ f d := by
  apply cover_hom_ext
  · simp [Category.assoc, cover_translation_over]
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, cover_translation_root, map_add]
    rw [← appTop_comp_apply, cover_translation_over]
    simp [add_assoc]

private def cover_translation_iso {k : Type*} [Field k] [Fintype k]
    (n : ℕ) (hcard : Fintype.card k = n)
    (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤)) (f : Γ(X, ⊤)) (c : k) :
    artinSchreierFunctionCover X n f ≅ artinSchreierFunctionCover X n f where
  hom := cover_translation n hcard X φ f c
  inv := cover_translation n hcard X φ f (-c)
  hom_inv_id := by rw [← cover_translation_add, add_neg_cancel, cover_translation_zero]
  inv_hom_id := by rw [← cover_translation_add, neg_add_cancel, cover_translation_zero]

private lemma trace_polynomial_eval {A : Type*} [CommRing A] (p r : ℕ) (b y : A) :
    (artinSchreierTracePolynomial p r b).eval y =
      ∑ i ∈ Finset.range r, (b * y) ^ (p ^ i) := by
  simp [artinSchreierTracePolynomial, Polynomial.eval_finsetSum]

private lemma trace_polynomial_map_eval {A B : Type*} [CommRing A] [CommRing B]
    (p r : ℕ) (φ : A →+* B) (b y : A) :
    φ ((artinSchreierTracePolynomial p r b).eval y) =
      (artinSchreierTracePolynomial p r (φ b)).eval (φ y) := by
  simp [trace_polynomial_eval, map_sum, map_pow, map_mul]

private lemma trace_polynomial_eval_equation {k A : Type*} [Field k] [Fintype k] [CommRing A]
    (p r : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ r)
    (φ : k →+* A) (b : k) (a : A) :
    (artinSchreierTracePolynomial p r (φ b)).eval a ^ p -
      (artinSchreierTracePolynomial p r (φ b)).eval a = φ b * (a ^ (p ^ r) - a) := by
  have h := congrArg (Polynomial.evalRingHom a)
    (trace_polynomial_identity p r hcard φ b)
  simpa using h

private lemma trace_polynomial_add {k A : Type*} [Field k] [Fintype k] [CommRing A]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hcard : Fintype.card k = p ^ r) (φ : k →+* A) (b c : k) (y : A) :
    (artinSchreierTracePolynomial p r (φ b)).eval (y + φ c) =
      (artinSchreierTracePolynomial p r (φ b)).eval y +
        φ (algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (b * c))) := by
  have hn : Module.finrank (ZMod p) k = r := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
    simpa [ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := k)).symm.trans hcard
  have ht := FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) k (b * c)
  rw [hn, Nat.card_eq_fintype_card, ZMod.card] at ht
  rw [ht, trace_polynomial_eval, trace_polynomial_eval, map_sum]
  have hp : (p : A) = 0 := by
    rw [← map_natCast φ, CharP.cast_eq_zero, map_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_add, ← map_mul, map_pow]
  exact (iterateFrobeniusOfPrime A Fact.out hp i).map_add _ _

attribute [local irreducible] artinSchreierTracePolynomial

private lemma trace_kernel_card {k : Type*} [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hcard : Fintype.card k = p ^ r) (b : k) (hb : b ≠ 0) :
    Nat.card {c : k // Algebra.trace (ZMod p) k (b * c) = 0} = p ^ r / p := by
  let T : k →+ ZMod p :=
    { toFun := fun c ↦ Algebra.trace (ZMod p) k (b * c)
      map_zero' := by simp
      map_add' := by intros; simp [mul_add] }
  have hs : Function.Surjective T := by
    intro d
    obtain ⟨a, ha⟩ := Algebra.trace_surjective (ZMod p) k d
    exact ⟨b⁻¹ * a, by simpa [T, ← mul_assoc, hb] using ha⟩
  have hidx : T.ker.index = p := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hc := T.ker.card_mul_index
  simp only [hidx, Nat.card_eq_fintype_card, hcard] at hc
  change Nat.card T.ker = _
  rw [Nat.card_eq_fintype_card]
  exact (Nat.div_eq_of_eq_mul_left (Fact.out : p.Prime).pos hc.symm).symm

private lemma trace_map_equation {k : Type u} [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ r)
    (b : k) (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    ((artinSchreierTracePolynomial p r
      ((artinSchreierFunctionProjection X (p ^ r) f).appTop
        (artinSchreierBaseConstants k X b))).eval
          (artinSchreierFunctionRoot X (p ^ r) f)) ^ p -
    (artinSchreierTracePolynomial p r
      ((artinSchreierFunctionProjection X (p ^ r) f).appTop
        (artinSchreierBaseConstants k X b))).eval
          (artinSchreierFunctionRoot X (p ^ r) f) =
    (artinSchreierFunctionProjection X (p ^ r) f).appTop
      (artinSchreierBaseConstants k X b * f) := by
  have he := trace_polynomial_eval_equation p r hcard
    ((artinSchreierFunctionProjection X (p ^ r) f).appTop.hom.comp
      (artinSchreierBaseConstants k X)) b (artinSchreierFunctionRoot X (p ^ r) f)
  simpa only [RingHom.comp_apply, cover_root_equation, map_mul] using he

private def trace_cover_map {k : Type u} [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ r)
    (b : k) (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    artinSchreierFunctionCover X (p ^ r) f ⟶
      artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f) :=
  cover_lift p _ (artinSchreierFunctionProjection X (p ^ r) f)
    ((artinSchreierTracePolynomial p r
      ((artinSchreierFunctionProjection X (p ^ r) f).appTop
        (artinSchreierBaseConstants k X b))).eval
          (artinSchreierFunctionRoot X (p ^ r) f))
    (trace_map_equation p r hcard b X f)

private def trace_cover_maps {k : Type u} [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hcard : Fintype.card k = p ^ r) (b : k)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    ArtinSchreierTraceMaps k p r b X f where
  σ := cover_translation_iso (p ^ r) hcard X (artinSchreierBaseConstants k X) f
  τ := by
    exact cover_translation_iso p (ZMod.card p) X
      ((artinSchreierBaseConstants k X).comp (algebraMap (ZMod p) k))
      (artinSchreierBaseConstants k X b * f)
  θ := trace_cover_map p r hcard b X f
  σ_over c := cover_translation_over (p ^ r) hcard X _ f c
  τ_over d := by
    exact cover_translation_over p (ZMod.card p) X
      ((artinSchreierBaseConstants k X).comp (algebraMap (ZMod p) k))
      (artinSchreierBaseConstants k X b * f) d
  θ_over := cover_lift_over _ _ _ _ _
  σ_root c := cover_translation_root (p ^ r) hcard X _ f c
  τ_root d := by
    exact cover_translation_root p (ZMod.card p) X
      ((artinSchreierBaseConstants k X).comp (algebraMap (ZMod p) k))
      (artinSchreierBaseConstants k X b * f) d
  θ_root := cover_lift_root _ _ _ _ _
  σ_zero := cover_translation_zero (p ^ r) hcard X _ f
  σ_add := cover_translation_add (p ^ r) hcard X _ f
  τ_zero := by
    exact cover_translation_zero p (ZMod.card p) X
      ((artinSchreierBaseConstants k X).comp (algebraMap (ZMod p) k))
      (artinSchreierBaseConstants k X b * f)
  τ_add c d := by
    exact cover_translation_add p (ZMod.card p) X
      ((artinSchreierBaseConstants k X).comp (algebraMap (ZMod p) k))
      (artinSchreierBaseConstants k X b * f) c d

attribute [local irreducible] trace_cover_maps

private lemma trace_maps_equivariance {k : Type u} [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hcard : Fintype.card k = p ^ r) (b : k)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤))
    (M : ArtinSchreierTraceMaps k p r b X f) (c : k) :
    (M.σ c).hom ≫ M.θ =
      M.θ ≫ (M.τ (Algebra.trace (ZMod p) k (b * c))).hom := by
  apply cover_hom_ext (X := X) (n := p)
    (f := artinSchreierBaseConstants k X b * f)
  · simp [Category.assoc, M.σ_over, M.τ_over, M.θ_over]
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, M.θ_root, M.τ_root,
      map_add]
    rw [trace_polynomial_map_eval]
    rw [← appTop_comp_apply, M.σ_over, M.σ_root]
    rw [← appTop_comp_apply, M.θ_over]
    exact trace_polynomial_add p r hcard
      ((artinSchreierFunctionProjection X (p ^ r) f).appTop.hom.comp
        (artinSchreierBaseConstants k X)) b c _

private lemma trace_quotient_identity {k A : Type*} [Field k] [Fintype k] [CommRing A]
    (p r : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ r)
    (φ : k →+* A) (b : k) (f : A) :
    (AdjoinRoot.mk (Polynomial.X ^ (p ^ r) - Polynomial.X - Polynomial.C f)
      (artinSchreierTracePolynomial p r (φ b))) ^ p -
    AdjoinRoot.mk (Polynomial.X ^ (p ^ r) - Polynomial.X - Polynomial.C f)
      (artinSchreierTracePolynomial p r (φ b)) =
    AdjoinRoot.of (Polynomial.X ^ (p ^ r) - Polynomial.X - Polynomial.C f) (φ b * f) := by
  let P : Polynomial A := Polynomial.X ^ (p ^ r) - Polynomial.X - Polynomial.C f
  have hrel := AdjoinRoot.mk_self (f := P)
  change AdjoinRoot.mk P _ ^ p - AdjoinRoot.mk P _ = AdjoinRoot.of P _
  rw [← map_pow, ← map_sub, trace_polynomial_identity p r hcard φ b, map_mul]
  have heq : AdjoinRoot.mk P (Polynomial.X ^ (p ^ r) - Polynomial.X) =
      AdjoinRoot.mk P (Polynomial.C f) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact hrel
  rw [heq, ← map_mul, ← Polynomial.C_mul]
  rfl

private def cover_base_map {X X' : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤)) (h : X' ⟶ X) :
    artinSchreierFunctionCover X' n (h.appTop f) ⟶ artinSchreierFunctionCover X n f :=
  cover_lift n f (artinSchreierFunctionProjection X' n (h.appTop f) ≫ h)
    (artinSchreierFunctionRoot X' n (h.appTop f)) (by
      rw [cover_root_equation, Scheme.Hom.comp_appTop]
      rfl)

private lemma cover_base_map_over {X X' : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤)) (h : X' ⟶ X) :
    cover_base_map n f h ≫ artinSchreierFunctionProjection X n f =
      artinSchreierFunctionProjection X' n (h.appTop f) ≫ h :=
  cover_lift_over _ _ _ _ _

private lemma cover_base_map_root {X X' : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤)) (h : X' ⟶ X) :
    (cover_base_map n f h).appTop (artinSchreierFunctionRoot X n f) =
      artinSchreierFunctionRoot X' n (h.appTop f) :=
  cover_lift_root _ _ _ _ _

attribute [local irreducible] cover_base_map

private lemma cover_base_map_cartesian {X X' : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤))
    (h : X' ⟶ X) :
    IsPullback (cover_base_map n f h) (artinSchreierFunctionProjection X' n (h.appTop f))
      (artinSchreierFunctionProjection X n f) h := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ (cover_base_map_over n f h))
  apply PullbackCone.isLimitAux'
  intro s
  dsimp only [PullbackCone.mk_fst, PullbackCone.mk_snd, PullbackCone.mk_pt]
  let y := s.fst.appTop (artinSchreierFunctionRoot X n f)
  have hy : y ^ n - y = s.snd.appTop (h.appTop f) := by
    rw [← map_pow, ← map_sub, cover_root_equation,
      ← appTop_comp_apply, s.condition,
      Scheme.Hom.comp_appTop]
    rfl
  refine ⟨cover_lift n (h.appTop f) s.snd y hy, ?_, cover_lift_over _ _ _ _ _, ?_⟩
  · apply cover_hom_ext
    · simp only [Category.assoc, cover_base_map_over]
      rw [← Category.assoc, cover_lift_over]
      exact s.condition.symm
    · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      exact (congrArg (fun t ↦ (cover_lift n (h.appTop f) s.snd y hy).appTop t)
        (cover_base_map_root n f h)).trans (cover_lift_root _ _ _ _ _)
  · intro m hm ho
    apply cover_hom_ext (ho.trans (cover_lift_over _ _ _ _ _).symm)
    rw [cover_lift_root]
    have he := congrArg (fun a ↦ a.appTop (artinSchreierFunctionRoot X n f)) hm
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at he
    exact (congrArg (fun t ↦ m.appTop t) (cover_base_map_root n f h).symm).trans he

private lemma constants_base_change {k : Type u} [Field k]
    {X X' : Scheme.{u}} [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]
    (h : X' ⟶ X) [h.IsOver (Spec (.of k))] (b : k) :
    h.appTop (artinSchreierBaseConstants k X b) = artinSchreierBaseConstants k X' b := by
  unfold artinSchreierBaseConstants
  simp only [RingHom.comp_apply]
  rw [← appTop_comp_apply, comp_over]

private lemma constants_pullback {k : Type u} [Field k]
    {X X' Y Y' : Scheme.{u}} [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]
    (h : X' ⟶ X) [h.IsOver (Spec (.of k))] (a : Y' ⟶ Y)
    (π : Y ⟶ X) (π' : Y' ⟶ X') (ha : a ≫ π = π' ≫ h) (c : k) :
    a.appTop (π.appTop (artinSchreierBaseConstants k X c)) =
      π'.appTop (artinSchreierBaseConstants k X' c) := by
  rw [← appTop_comp_apply, ha, appTop_comp_apply, constants_base_change h]

private def fibre_point_lift {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (z : (pullback π x : Scheme.{u})) : Spec (.of Ω) ⟶ Y := by
  have : IsLocallyArtinian (pullback π x) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd π x)
  exact pointOfClosedPoint (pullback.snd π x) z isClosed_singleton ≫ pullback.fst π x

attribute [local irreducible] fibre_point_lift

private lemma fibre_point_lift_over {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (z : (pullback π x : Scheme.{u})) : fibre_point_lift π x z ≫ π = x := by
  unfold fibre_point_lift
  simp [pullback.condition]

private lemma fibre_point_lift_value {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (z : (pullback π x : Scheme.{u})) :
    (pullback.lift (fibre_point_lift π x z) (𝟙 _) (by
      simpa using fibre_point_lift_over π x z)) (IsLocalRing.closedPoint Ω) = z := by
  have : IsLocallyArtinian (pullback π x) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd π x)
  unfold fibre_point_lift
  have he : pullback.lift
      (pointOfClosedPoint (pullback.snd π x) z isClosed_singleton ≫ pullback.fst π x)
      (𝟙 _) (by simp [pullback.condition]) =
      pointOfClosedPoint (pullback.snd π x) z isClosed_singleton := by
    apply pullback.hom_ext <;> simp
  rw [he, pointOfClosedPoint_apply]

private lemma fibre_point_lift_injective {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Function.Injective (fibre_point_lift π x) := by
  intro z z' he
  have hh : pullback.lift (fibre_point_lift π x z) (𝟙 _) (by
      simpa using fibre_point_lift_over π x z) =
      pullback.lift (fibre_point_lift π x z') (𝟙 _) (by
        simpa using fibre_point_lift_over π x z') := by
    apply pullback.hom_ext <;> simp [he]
  have hv := congrArg (fun g ↦ g (IsLocalRing.closedPoint Ω)) hh
  simpa only [fibre_point_lift_value] using hv

private lemma fibre_point_lift_map {X Y Z : Scheme.{u}} (π : Y ⟶ X) (ρ : Z ⟶ X)
    [IsFinite π] [IsFinite ρ] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (a : Y ⟶ Z) (ha : a ≫ ρ = π)
    (z : (pullback π x : Scheme.{u})) :
    fibre_point_lift ρ x (artinSchreierFibreMap π ρ x a ha z) = fibre_point_lift π x z ≫ a := by
  let l := pullback.lift (fibre_point_lift π x z ≫ a) (𝟙 _) (by
    rw [Category.assoc, ha, fibre_point_lift_over, Category.id_comp])
  have hv : l (IsLocalRing.closedPoint Ω) = artinSchreierFibreMap π ρ x a ha z := by
    have hh : l = pullback.lift (fibre_point_lift π x z) (𝟙 _) (by
        simpa using fibre_point_lift_over π x z) ≫ artinSchreierFibreMap π ρ x a ha := by
      apply pullback.hom_ext <;> simp [l, artinSchreierFibreMap]
    rw [hh, Scheme.Hom.comp_apply, fibre_point_lift_value]
  have he : pullback.lift
      (fibre_point_lift ρ x (artinSchreierFibreMap π ρ x a ha z)) (𝟙 _)
      (by simpa using fibre_point_lift_over ρ x _) = l := by
    apply ext_of_apply_closedPoint_eq (pullback.snd ρ x)
    · simp
    · simp [l]
    · rw [fibre_point_lift_value, hv]
  have hh := congrArg (fun g ↦ g ≫ pullback.fst ρ x) he
  simpa [l] using hh

attribute [local irreducible] artinSchreierFibreMap

private lemma cover_fibre_nonempty {X : Scheme.{u}} (n : ℕ) (hn : 1 < n)
    (f : Γ(X, ⊤)) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    Nonempty (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u}) := by
  let a := (Scheme.ΓSpecIso (.of Ω)).hom.hom (x.appTop f)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ n - Polynomial.X - Polynomial.C a) (by
      rw [Polynomial.degree_sub_C, Polynomial.degree_sub_eq_left_of_degree_lt,
        Polynomial.degree_X_pow]
      · exact_mod_cast (by omega : n ≠ 0)
      · simpa using (show (1 : WithBot ℕ) < n by exact_mod_cast hn)
      · rw [Polynomial.degree_sub_eq_left_of_degree_lt]
        · rw [Polynomial.degree_X_pow]
          exact_mod_cast (by omega : 0 < n)
        · simpa using (show (1 : WithBot ℕ) < n by exact_mod_cast hn))
  have he : y ^ n - y = a := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using hy
  let z := (Scheme.ΓSpecIso (.of Ω)).inv.hom y
  have hz : z ^ n - z = x.appTop f := by
    simpa [z, a, ← map_pow, ← map_sub] using
      congrArg (Scheme.ΓSpecIso (.of Ω)).inv.hom he
  let s := cover_lift n f x z hz
  exact ⟨pullback.lift s (𝟙 _) (by simp [s, cover_lift_over])
    (IsLocalRing.closedPoint Ω)⟩

private def cover_fibre_coord {X : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤))
    [IsFinite (artinSchreierFunctionProjection X n f)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (z : (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u})) : Ω :=
  (Scheme.ΓSpecIso (.of Ω)).hom.hom
    ((fibre_point_lift (artinSchreierFunctionProjection X n f) x z).appTop
      (artinSchreierFunctionRoot X n f))

attribute [local irreducible] cover_fibre_coord

private lemma cover_fibre_coord_injective {X : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤))
    [IsFinite (artinSchreierFunctionProjection X n f)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Function.Injective (cover_fibre_coord n f x) := by
  intro z z' he
  apply fibre_point_lift_injective (artinSchreierFunctionProjection X n f) x
  apply cover_hom_ext
  · rw [fibre_point_lift_over, fibre_point_lift_over]
  · unfold cover_fibre_coord at he
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of Ω)).hom).1 he

private lemma cover_fibre_coord_equation {X : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤))
    [IsFinite (artinSchreierFunctionProjection X n f)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (z : (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u})) :
    cover_fibre_coord n f x z ^ n - cover_fibre_coord n f x z =
      (Scheme.ΓSpecIso (.of Ω)).hom.hom (x.appTop f) := by
  unfold cover_fibre_coord
  rw [← map_pow, ← map_sub, ← map_pow, ← map_sub, cover_root_equation]
  congr 1
  rw [← appTop_comp_apply, fibre_point_lift_over]

private lemma cover_fibre_coord_translation {k : Type*} [Field k] {X : Scheme.{u}}
    (n : ℕ) (f : Γ(X, ⊤)) [IsFinite (artinSchreierFunctionProjection X n f)]
    (φ : k →+* Γ(X, ⊤)) (σ : k → (artinSchreierFunctionCover X n f ⟶
      artinSchreierFunctionCover X n f))
    (ho : ∀ c, σ c ≫ artinSchreierFunctionProjection X n f =
      artinSchreierFunctionProjection X n f)
    (hy : ∀ c, (σ c).appTop (artinSchreierFunctionRoot X n f) =
      artinSchreierFunctionRoot X n f + (artinSchreierFunctionProjection X n f).appTop (φ c))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (z : (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u})) (c : k) :
    cover_fibre_coord n f x (artinSchreierFibreMap _ _ x (σ c) (ho c) z) =
      cover_fibre_coord n f x z + (Scheme.ΓSpecIso (.of Ω)).hom.hom (x.appTop (φ c)) := by
  unfold cover_fibre_coord
  rw [fibre_point_lift_map, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hy,
    map_add, map_add]
  congr 1
  congr 1
  rw [← appTop_comp_apply, fibre_point_lift_over]

private lemma cover_fibre_torsor {k : Type*} [Field k] [Fintype k] {X : Scheme.{u}}
    (n : ℕ) (hcard : Fintype.card k = n) (f : Γ(X, ⊤))
    [IsFinite (artinSchreierFunctionProjection X n f)]
    (φ : k →+* Γ(X, ⊤)) (σ : k → (artinSchreierFunctionCover X n f ⟶
      artinSchreierFunctionCover X n f))
    (ho : ∀ c, σ c ≫ artinSchreierFunctionProjection X n f =
      artinSchreierFunctionProjection X n f)
    (hy : ∀ c, (σ c).appTop (artinSchreierFunctionRoot X n f) =
      artinSchreierFunctionRoot X n f + (artinSchreierFunctionProjection X n f).appTop (φ c))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Nonempty (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u}) ∧
    (∀ z z' : (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u}),
      ∃! c : k, artinSchreierFibreMap _ _ x (σ c) (ho c) z = z') ∧
    Nat.card (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u}) = n := by
  classical
  let ψ : k →+* Ω := (Scheme.ΓSpecIso (.of Ω)).hom.hom.comp (x.appTop.hom.comp φ)
  let v := cover_fibre_coord n f x
  have htrans z c : v (artinSchreierFibreMap _ _ x (σ c) (ho c) z) = v z + ψ c :=
    cover_fibre_coord_translation n f φ σ ho hy x z c
  have huni (z z' : (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u})) :
      ∃! c : k, artinSchreierFibreMap _ _ x (σ c) (ho c) z = z' := by
    have hd : (v z' - v z) ^ Fintype.card k = v z' - v z := by
      apply FiniteField.sub_pow_card_eq_of_pow_card_sub_eq ψ
      rw [hcard, cover_fibre_coord_equation, cover_fibre_coord_equation]
    have hp := FiniteField.prod_sub_eq_zero_of_pow_card_eq ψ hd
    obtain ⟨c, -, hc⟩ := Finset.prod_eq_zero_iff.mp hp
    have hv : v z + ψ c = v z' := by
      linear_combination -hc
    refine ⟨c, cover_fibre_coord_injective n f x (by change v _ = v z'; rw [htrans, hv]), ?_⟩
    intro d hd'
    apply ψ.injective
    have he := congrArg v hd'
    rw [htrans, ← hv] at he
    exact add_left_cancel he
  have hn : 1 < n := hcard ▸ Fintype.one_lt_card
  have hne := cover_fibre_nonempty n hn f x
  obtain ⟨z⟩ := hne
  have hne' : Nonempty (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u}) := ⟨z⟩
  let t : k → (pullback (artinSchreierFunctionProjection X n f) x : Scheme.{u}) :=
    fun c ↦ artinSchreierFibreMap _ _ x (σ c) (ho c) z
  have ht : Function.Bijective t := by
    constructor
    · intro c d he
      exact (huni z (t d)).unique he rfl
    · intro z'
      obtain ⟨c, hc, -⟩ := huni z z'
      exact ⟨c, hc⟩
  exact ⟨hne', huni, (Nat.card_congr (Equiv.ofBijective t ht)).symm.trans
    ((Nat.card_eq_fintype_card (α := k)).trans hcard)⟩

private lemma cover_base_change_general {X X' : Scheme.{u}} (n : ℕ) (f : Γ(X, ⊤))
    (f' : Γ(X', ⊤)) (h : X' ⟶ X) (hf : h.appTop f = f') :
    ∃ u : artinSchreierFunctionCover X' n f' ⟶ artinSchreierFunctionCover X n f,
      IsPullback u (artinSchreierFunctionProjection X' n f')
        (artinSchreierFunctionProjection X n f) h ∧
      u.appTop (artinSchreierFunctionRoot X n f) = artinSchreierFunctionRoot X' n f' := by
  subst f'
  exact ⟨cover_base_map n f h, cover_base_map_cartesian n f h, cover_base_map_root n f h⟩

private lemma trace_maps_base_change {k : Type u} [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (_hcard : Fintype.card k = p ^ r) (b : k)
    (X X' : Scheme.{u}) [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]
    (f : Γ(X, ⊤)) (h : X' ⟶ X) [h.IsOver (Spec (.of k))]
    (M : ArtinSchreierTraceMaps k p r b X f)
    (N : ArtinSchreierTraceMaps k p r b X' (h.appTop f)) :
    ∃ (uq : artinSchreierFunctionCover X' (p ^ r) (h.appTop f) ⟶
          artinSchreierFunctionCover X (p ^ r) f)
      (up : artinSchreierFunctionCover X' p
          (artinSchreierBaseConstants k X' b * h.appTop f) ⟶
        artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f)),
      IsPullback uq (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f))
        (artinSchreierFunctionProjection X (p ^ r) f) h ∧
      IsPullback up (artinSchreierFunctionProjection X' p
          (artinSchreierBaseConstants k X' b * h.appTop f))
        (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)) h ∧
      uq.appTop (artinSchreierFunctionRoot X (p ^ r) f) =
        artinSchreierFunctionRoot X' (p ^ r) (h.appTop f) ∧
      up.appTop (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
        artinSchreierFunctionRoot X' p (artinSchreierBaseConstants k X' b * h.appTop f) ∧
      (∀ c : k, (N.σ c).hom ≫ uq = uq ≫ (M.σ c).hom) ∧
      (∀ d : ZMod p, (N.τ d).hom ≫ up = up ≫ (M.τ d).hom) ∧
      N.θ ≫ up = uq ≫ M.θ := by
  obtain ⟨uq, hq, hqy⟩ := cover_base_change_general (p ^ r) f (h.appTop f) h rfl
  obtain ⟨up, hp, hpy⟩ := cover_base_change_general p
    (artinSchreierBaseConstants k X b * f)
    (artinSchreierBaseConstants k X' b * h.appTop f) h
    (by rw [map_mul, constants_base_change])
  refine ⟨uq, up, hq, hp, hqy, hpy, ?_, ?_, ?_⟩
  · intro c
    apply cover_hom_ext (X := X) (n := p ^ r) (f := f)
    · rw [Category.assoc, hq.w, ← Category.assoc, N.σ_over,
        Category.assoc, M.σ_over, hq.w]
    · have hconst := constants_pullback h uq _ _ hq.w c
      simp only [appTop_comp_apply]
      calc
        _ = (N.σ c).hom.appTop
            (artinSchreierFunctionRoot X' (p ^ r) (h.appTop f)) :=
          congrArg (fun t ↦ (N.σ c).hom.appTop t) hqy
        _ = _ := N.σ_root c
        _ = uq.appTop (artinSchreierFunctionRoot X (p ^ r) f) + uq.appTop
            ((artinSchreierFunctionProjection X (p ^ r) f).appTop
              (artinSchreierBaseConstants k X c)) :=
          congrArg₂ (· + ·) hqy.symm hconst.symm
        _ = _ := (map_add uq.appTop.hom _ _).symm
        _ = _ := congrArg (fun t ↦ uq.appTop t) (M.σ_root c).symm
  · intro d
    apply cover_hom_ext (X := X) (n := p)
      (f := artinSchreierBaseConstants k X b * f)
    · rw [Category.assoc, hp.w, ← Category.assoc, N.τ_over,
        Category.assoc, M.τ_over, hp.w]
    · have hconst := constants_pullback h up _ _ hp.w (algebraMap (ZMod p) k d)
      simp only [appTop_comp_apply]
      calc
        _ = (N.τ d).hom.appTop (artinSchreierFunctionRoot X' p
            (artinSchreierBaseConstants k X' b * h.appTop f)) :=
          congrArg (fun t ↦ (N.τ d).hom.appTop t) hpy
        _ = _ := N.τ_root d
        _ = up.appTop (artinSchreierFunctionRoot X p
            (artinSchreierBaseConstants k X b * f)) + up.appTop
              ((artinSchreierFunctionProjection X p
                (artinSchreierBaseConstants k X b * f)).appTop
                  (artinSchreierBaseConstants k X (algebraMap (ZMod p) k d))) :=
          congrArg₂ (· + ·) hpy.symm hconst.symm
        _ = _ := (map_add up.appTop.hom _ _).symm
        _ = _ := congrArg (fun t ↦ up.appTop t) (M.τ_root d).symm
  · apply cover_hom_ext (X := X) (n := p)
      (f := artinSchreierBaseConstants k X b * f)
    · rw [Category.assoc, hp.w, ← Category.assoc, N.θ_over,
        Category.assoc, M.θ_over, hq.w]
    · have hconst := constants_pullback h uq _ _ hq.w b
      simp only [appTop_comp_apply]
      calc
        _ = N.θ.appTop (artinSchreierFunctionRoot X' p
            (artinSchreierBaseConstants k X' b * h.appTop f)) :=
          congrArg (fun t ↦ N.θ.appTop t) hpy
        _ = _ := N.θ_root
        _ = (artinSchreierTracePolynomial p r
            (uq.appTop ((artinSchreierFunctionProjection X (p ^ r) f).appTop
              (artinSchreierBaseConstants k X b)))).eval
                (uq.appTop (artinSchreierFunctionRoot X (p ^ r) f)) :=
          congrArg₂ (fun a y ↦ (artinSchreierTracePolynomial p r a).eval y)
            hconst.symm hqy.symm
        _ = _ := (trace_polynomial_map_eval p r uq.appTop.hom _ _).symm
        _ = _ := congrArg (fun t ↦ uq.appTop t) M.θ_root.symm

private lemma trace_fibre_coord {k : Type u} [Field k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (b : k) (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤))
    [IsFinite (artinSchreierFunctionProjection X (p ^ r) f)]
    [IsFinite (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))]
    (M : ArtinSchreierTraceMaps k p r b X f)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (z : (pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u})) :
    cover_fibre_coord p (artinSchreierBaseConstants k X b * f) x
        (artinSchreierFibreMap _ _ x M.θ M.θ_over z) =
      (artinSchreierTracePolynomial p r
        ((Scheme.ΓSpecIso (.of Ω)).hom.hom (x.appTop (artinSchreierBaseConstants k X b)))).eval
          (cover_fibre_coord (p ^ r) f x z) := by
  unfold cover_fibre_coord
  rw [fibre_point_lift_map, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, M.θ_root,
    trace_polynomial_map_eval, trace_polynomial_map_eval]
  congr 2
  congr 1
  rw [← appTop_comp_apply, fibre_point_lift_over]


private lemma trace_fibre_orbits {k : Type u} [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hcard : Fintype.card k = p ^ r) (b : k) (hb : b ≠ 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤))
    [IsFinite (artinSchreierFunctionProjection X (p ^ r) f)]
    [IsFinite (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f))]
    (M : ArtinSchreierTraceMaps k p r b X f)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Function.Surjective (artinSchreierFibreMap _ _ x M.θ M.θ_over) ∧
      ∀ z z' : (pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}),
        artinSchreierFibreMap _ _ x M.θ M.θ_over z =
          artinSchreierFibreMap _ _ x M.θ M.θ_over z' ↔
        ∃ c : k, Algebra.trace (ZMod p) k (b * c) = 0 ∧
          artinSchreierFibreMap _ _ x (M.σ c).hom (M.σ_over c) z = z' := by
  let π := artinSchreierFunctionProjection X (p ^ r) f
  let ρ := artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)
  let F := artinSchreierFibreMap π ρ x M.θ M.θ_over
  let S c := artinSchreierFibreMap π π x (M.σ c).hom (M.σ_over c)
  let T d := artinSchreierFibreMap ρ ρ x (M.τ d).hom (M.τ_over d)
  let ψ : k →+* Ω := (Scheme.ΓSpecIso (.of Ω)).hom.hom.comp
    (x.appTop.hom.comp (artinSchreierBaseConstants k X))
  let ι := ψ.comp (algebraMap (ZMod p) k)
  let v := cover_fibre_coord (p ^ r) f x
  let w := cover_fibre_coord p (artinSchreierBaseConstants k X b * f) x
  have hq := cover_fibre_torsor (p ^ r) hcard f (artinSchreierBaseConstants k X)
    (fun c ↦ (M.σ c).hom) M.σ_over M.σ_root x
  have hp := cover_fibre_torsor p (ZMod.card p) (artinSchreierBaseConstants k X b * f)
    ((artinSchreierBaseConstants k X).comp (algebraMap (ZMod p) k))
    (fun d ↦ (M.τ d).hom) M.τ_over M.τ_root x
  have hs z c : v (S c z) = v z + ψ c :=
    cover_fibre_coord_translation (p ^ r) f (artinSchreierBaseConstants k X)
      (fun c ↦ (M.σ c).hom) M.σ_over M.σ_root x z c
  have ht z d : w (T d z) = w z + ι d :=
    cover_fibre_coord_translation p (artinSchreierBaseConstants k X b * f)
      ((artinSchreierBaseConstants k X).comp (algebraMap (ZMod p) k))
      (fun d ↦ (M.τ d).hom) M.τ_over M.τ_root x z d
  have hf z : w (F z) = (artinSchreierTracePolynomial p r (ψ b)).eval (v z) :=
    trace_fibre_coord p r b X f M x z
  have heq z c : F (S c z) = T (Algebra.trace (ZMod p) k (b * c)) (F z) := by
    apply cover_fibre_coord_injective p (artinSchreierBaseConstants k X b * f) x
    change w (F (S c z)) = w (T _ (F z))
    rw [hf (S c z), hs z c, trace_polynomial_add p r hcard ψ b c,
      ht (F z) (Algebra.trace (ZMod p) k (b * c)), hf z]
    rfl
  have hsurj : Function.Surjective (fun c : k ↦ Algebra.trace (ZMod p) k (b * c)) := by
    intro d
    obtain ⟨a, ha⟩ := Algebra.trace_surjective (ZMod p) k d
    exact ⟨b⁻¹ * a, by simpa [← mul_assoc, hb] using ha⟩
  constructor
  · obtain ⟨z⟩ := hq.1
    intro t
    obtain ⟨d, hd, -⟩ := hp.2.1 (F z) t
    obtain ⟨c, hc⟩ := hsurj d
    change Algebra.trace (ZMod p) k (b * c) = d at hc
    exact ⟨S c z, by rw [heq, hc]; exact hd⟩
  · intro z z'
    obtain ⟨c, hc, hu⟩ := hq.2.1 z z'
    constructor
    · intro he
      refine ⟨c, ?_, hc⟩
      have hz : T (Algebra.trace (ZMod p) k (b * c)) (F z) = F z := by
        rw [← heq z c, hc, he]
      have hh := congrArg w hz
      rw [ht (F z) (Algebra.trace (ZMod p) k (b * c))] at hh
      have hi : ι (Algebra.trace (ZMod p) k (b * c)) = 0 := by
        linear_combination hh
      exact ι.injective (hi.trans (map_zero ι).symm)
    · rintro ⟨d, hd, hz⟩
      have hd' : d = c := hu d hz
      subst d
      apply cover_fibre_coord_injective p (artinSchreierBaseConstants k X b * f) x
      change w (F z) = w (F z')
      rw [← hc, heq z c, ht (F z) (Algebra.trace (ZMod p) k (b * c)), hd,
        map_zero, add_zero]

/-- All five assertions for the trace-polynomial morphism of Artin–Schreier covers.
Source: Laumon (1.1.3), pp. 139–140 (Lang torsor pushout), with the explicit construction
and calculations of the DAG proof (blueprint: lem-a1-artin-schreier-trace-cover-map).

Proof:
1. On each affine chart use the monic-quotient basis (lem-weil-pbc-monic-quotient-free).
   The derivative is -1, so the standard-etale presentation is etale
   (lem-weil-pbc-standard-etale-monic-derivative). Relative-Spec charts glue these assertions
   (lem-weil-pbc-affine-morphism-relative-spec); the quotient algebras are quasi-coherent
   (pqf-def-coherent). The identical argument works on empty charts using the zero ring.
2. Relative-Spec base change and the affine-sections formula for module pullback identify
   the quotient after any base change with the same quotient in the new coefficient ring
   (lem-weil-pbc-relative-spec-base-change, lem-weil-pbc-module-pullback-affine-sections).
3. Frobenius and c^q=c preserve the equation under y ↦ y+c; the inverse is y ↦ y-c
   (def-weil-ring-frobenius, lem-weil-finite-field-pow-card). These substitutions glue.
4. On a geometric fibre the separable monic polynomial has q distinct roots
   (def-pc-separable-polynomial, lem-pc-separable-polynomial-distinct-roots-alg-closed).
   If α is one root, the α+c are all its roots. Thus translation is simply transitive.
5. Frobenius telescopes Θ_b^p-Θ_b to (by)^(p^r)-by = b(y^q-y). Reducing by the equation
   gives bf, hence the coordinate substitution t ↦ Θ_b descends and glues to θ.
6. The finite-field trace formula (lem-a1-finite-field-trace-frobenius-sum) identifies
   ∑ (bc)^(p^i) with Tr(bc), since finrank over F_p is r. Hence Θ_b(y+c)=Θ_b(y)+Tr(bc),
   proving equivariance on generators and thus on schemes by the relative-Spec equivalence.
7. The map c ↦ Tr(bc) is F_p-linear and surjective by trace-pairing nondegeneracy
   (lem-a1-trace-pairing-nondegenerate), since b≠0. Its p equal-sized cosets partition k,
   so its kernel has q/p elements. This does not assume Tr(1)≠0.
8. On geometric fibres θ sends α+c to Θ_b(α)+Tr(bc). Surjectivity of trace proves
   surjectivity of θ; equal images are exactly differences in the trace kernel.
9. Every coefficient pullback fixes b, c and the prime-field constants and carries f to h^*f.
   The three displayed substitutions therefore commute with arbitrary base change, on
   coefficients and the coordinate generator, and then globally by relative Spec. The
   comparison squares are cartesian and give the canonical isomorphisms to the pullbacks.
-/
theorem artinSchreier_trace_cover_map (k : Type u) [Field k] [Fintype k]
    (p r : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hr : 1 ≤ r) (hcard : Fintype.card k = p ^ r) (b : k) (hb : b ≠ 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (f : Γ(X, ⊤)) :
    ∃ M : ArtinSchreierTraceMaps k p r b X f,
      IsFinite (artinSchreierFunctionProjection X (p ^ r) f) ∧
      Etale (artinSchreierFunctionProjection X (p ^ r) f) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Nonempty ↥(pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}) ∧
        (∀ z z' : ↥(pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}),
          ∃! c : k, artinSchreierFibreMap _ _ x (M.σ c).hom (M.σ_over c) z = z') ∧
        Nat.card ↥(pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}) = p ^ r) ∧
      (∀ U : X.Opens,
        artinSchreierTracePolynomial p r
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b)) ^ p -
          artinSchreierTracePolynomial p r
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b)) =
          Polynomial.C
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b)) *
            (Polynomial.X ^ (p ^ r) - Polynomial.X)) ∧
      (∀ U : X.Opens,
        (AdjoinRoot.mk (Polynomial.X ^ (p ^ r) - Polynomial.X -
          Polynomial.C (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f))
          (artinSchreierTracePolynomial p r
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
              (artinSchreierBaseConstants k X b)))) ^ p -
        AdjoinRoot.mk (Polynomial.X ^ (p ^ r) - Polynomial.X -
          Polynomial.C (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f))
          (artinSchreierTracePolynomial p r
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b))) =
        AdjoinRoot.of (Polynomial.X ^ (p ^ r) - Polynomial.X -
          Polynomial.C (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f))
          (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (artinSchreierBaseConstants k X b) *
            X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f)) ∧
      (∀ c : k, (M.σ c).hom ≫ M.θ =
        M.θ ≫ (M.τ (Algebra.trace (ZMod p) k (b * c))).hom) ∧
      Nat.card {c : k // Algebra.trace (ZMod p) k (b * c) = 0} = p ^ r / p ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Function.Surjective (artinSchreierFibreMap _ _ x M.θ M.θ_over) ∧
        ∀ z z' : ↥(pullback (artinSchreierFunctionProjection X (p ^ r) f) x : Scheme.{u}),
          artinSchreierFibreMap _ _ x M.θ M.θ_over z =
            artinSchreierFibreMap _ _ x M.θ M.θ_over z' ↔
          ∃ c : k, Algebra.trace (ZMod p) k (b * c) = 0 ∧
            artinSchreierFibreMap _ _ x (M.σ c).hom (M.σ_over c) z = z') ∧
      (∀ (X' : Scheme.{u}) [X'.Over (Spec (.of k))]
          [IsSeparated (X' ↘ Spec (.of k))] [LocallyOfFiniteType (X' ↘ Spec (.of k))]
          [QuasiCompact (X' ↘ Spec (.of k))] (h : X' ⟶ X) [h.IsOver (Spec (.of k))],
        ∃ (M' : ArtinSchreierTraceMaps k p r b X' (h.appTop f))
          (uq : artinSchreierFunctionCover X' (p ^ r) (h.appTop f) ⟶
            artinSchreierFunctionCover X (p ^ r) f)
          (up : artinSchreierFunctionCover X' p
              (artinSchreierBaseConstants k X' b * h.appTop f) ⟶
            artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f)),
          IsPullback uq (artinSchreierFunctionProjection X' (p ^ r) (h.appTop f))
            (artinSchreierFunctionProjection X (p ^ r) f) h ∧
          IsPullback up (artinSchreierFunctionProjection X' p
              (artinSchreierBaseConstants k X' b * h.appTop f))
            (artinSchreierFunctionProjection X p (artinSchreierBaseConstants k X b * f)) h ∧
          uq.appTop (artinSchreierFunctionRoot X (p ^ r) f) =
            artinSchreierFunctionRoot X' (p ^ r) (h.appTop f) ∧
          up.appTop (artinSchreierFunctionRoot X p (artinSchreierBaseConstants k X b * f)) =
            artinSchreierFunctionRoot X' p (artinSchreierBaseConstants k X' b * h.appTop f) ∧
          (∀ c : k, (M'.σ c).hom ≫ uq = uq ≫ (M.σ c).hom) ∧
          (∀ d : ZMod p, (M'.τ d).hom ≫ up = up ≫ (M.τ d).hom) ∧
          M'.θ ≫ up = uq ≫ M.θ) := by
  obtain ⟨M⟩ : Nonempty (ArtinSchreierTraceMaps k p r b X f) :=
    ⟨trace_cover_maps p r hcard b X f⟩
  obtain ⟨hqf, hqe⟩ := cover_finite_etale p r hr hcard X (artinSchreierBaseConstants k X) f
  have hpf := cover_finite X p (Fact.out : p.Prime).ne_one
    (artinSchreierBaseConstants k X b * f)
  have htor (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
    cover_fibre_torsor (p ^ r) hcard f (artinSchreierBaseConstants k X)
      (fun c ↦ (M.σ c).hom) M.σ_over M.σ_root x
  have hpoly (U : X.Opens) := trace_polynomial_identity p r hcard
    ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
      (artinSchreierBaseConstants k X)) b
  have hquot (U : X.Opens) := trace_quotient_identity p r hcard
    ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
      (artinSchreierBaseConstants k X)) b
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f)
  have horbit (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
    trace_fibre_orbits p r hcard b hb X f M x
  exact ⟨M, hqf, hqe, htor, hpoly, hquot,
    trace_maps_equivariance p r hcard b X f M, trace_kernel_card p r hcard b hb,
    horbit, fun X' _ _ _ _ h _ ↦ by
      obtain ⟨N⟩ : Nonempty (ArtinSchreierTraceMaps k p r b X' (h.appTop f)) :=
        ⟨trace_cover_maps p r hcard b X' (h.appTop f)⟩
      obtain ⟨uq, up, huq, hup, hyq, hyp, hσ, hτ, hθ⟩ :=
        trace_maps_base_change p r hcard b X X' f h M N
      exact ⟨N, uq, up, huq, hup, hyq, hyp, hσ, hτ, hθ⟩⟩

end

end AlgebraicGeometry
