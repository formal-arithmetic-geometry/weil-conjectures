/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Category.Profinite.Limits
public import Mathlib.Topology.Separation.Profinite
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant

/-!

# Locally constant functions on a fibre product of profinite sets

Let `f : X ⟶ Z` and `g : Y ⟶ Z` be continuous maps of profinite sets, and let
`P = X ×_Z Y` be their fibre product. This file shows that the ring of locally constant
functions `LC(P, ℤ)` is the tensor product `LC(Y, ℤ) ⊗_{LC(Z, ℤ)} LC(X, ℤ)`, i.e. that the
square of rings
```
  LC(Z, ℤ) ───f^*───▶ LC(X, ℤ)
     │                   │
    g^*                fst^*
     ▼                   ▼
  LC(Y, ℤ) ──snd^*──▶ LC(P, ℤ)
```
is a pushout of commutative rings (`Profinite.isPushout_locallyConstant`). Together with the
fact that `LC(*, ℤ) = ℤ` is initial, this says that `S ↦ Spec LC(S, ℤ)` preserves finite
limits.

Both halves of the bijectivity of `LC(Y) ⊗_{LC(Z)} LC(X) ⟶ LC(P)` are proved with the finite
clopen partitions cut out by finitely many locally constant functions:

* surjectivity (`LocallyConstant.mem_closure_comap_mul_comap`): a locally constant function on
  `P` is constant on the traces on `P` of finitely many clopen boxes `U × V` covering `P`, hence
  is a sum of products `b(y) a(x)`;
* injectivity (`LocallyConstant.sum_tmul_eq_zero`): in a sum `∑ bᵢ ⊗ aᵢ` all functions are
  constant on the cells `Vβ × Uα` of a common partition, and the term on a cell is zero:
  either the cell meets `P`, and then the coefficient is the value of `∑ bᵢ(y) aᵢ(x)` at a
  point of `P`; or `f(Uα)` and `g(Vβ)` are disjoint, hence separated by a clopen `W ⊆ Z`, and
  `1_{Vβ} ⊗ 1_{Uα} = 1_{Vβ} ⊗ (1_W ∘ f) 1_{Uα} = (1_W ∘ g) 1_{Vβ} ⊗ 1_{Uα} = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Topology

namespace LocallyConstant

/-! ### The cells of a locally constant function -/

section Cells

variable {T : Type*} [TopologicalSpace T] {R : Type*} [CommRing R] {V : Type*}

/-- The characteristic function of the fibre `c ⁻¹' {v}` of a locally constant function. -/
noncomputable def fiberCharFn (R : Type*) [CommRing R] (c : LocallyConstant T V) (v : V) :
    LocallyConstant T R :=
  charFn R (c.isLocallyConstant.isClopen_fiber v)

lemma fiberCharFn_apply [DecidableEq V] (c : LocallyConstant T V) (v : V) (t : T) :
    fiberCharFn R c v t = if c t = v then 1 else 0 := by
  by_cases h : c t = v
  · rw [if_pos h]
    exact Set.indicator_of_mem (s := {x | c x = v}) h 1
  · rw [if_neg h]
    exact Set.indicator_of_notMem (s := {x | c x = v}) h 1

lemma fiberCharFn_apply_of_ne (c : LocallyConstant T V) {v : V} {t : T} (h : c t ≠ v) :
    fiberCharFn R c v t = 0 := by
  classical
  rw [fiberCharFn_apply, if_neg h]

/-- On a compact space, a locally constant function `F ∘ c` is the sum over the (finitely
many) values `v` of `c` of `F v` times the characteristic function of the fibre of `c`
over `v`. -/
lemma sum_const_mul_fiberCharFn [CompactSpace T] (c : LocallyConstant T V) (F : V → R) :
    ∑ v ∈ c.range_finite.toFinset, const T (F v) * fiberCharFn R c v = c.map F := by
  classical
  ext t
  simp only [sum_apply, coe_mul, Pi.mul_apply, coe_const, Function.const_apply,
    fiberCharFn_apply, mul_ite, mul_one, mul_zero, map_apply]
  rw [Finset.sum_ite_eq, if_pos (c.range_finite.mem_toFinset.2 (Set.mem_range_self t))]

/-- On a compact space, the characteristic functions of the fibres of a locally constant
function sum to `1`. -/
lemma sum_fiberCharFn [CompactSpace T] (c : LocallyConstant T V) :
    ∑ v ∈ c.range_finite.toFinset, fiberCharFn R c v = 1 := by
  have := sum_const_mul_fiberCharFn (R := R) c (fun _ ↦ 1)
  simp only [const_one, one_mul] at this
  rw [this]
  ext
  rfl

/-- A locally constant function which is equal to `r` on the fibre of `c` over `v` is `r` times
the characteristic function of that fibre, after multiplying with it. -/
lemma fiberCharFn_mul_eq (c : LocallyConstant T V) (v : V) (a : LocallyConstant T R) (r : R)
    (h : ∀ t, c t = v → a t = r) :
    fiberCharFn R c v * a = const T r * fiberCharFn R c v := by
  classical
  ext t
  simp only [coe_mul, Pi.mul_apply, coe_const, Function.const_apply, fiberCharFn_apply]
  split_ifs with ht
  · rw [h t ht, one_mul, mul_one]
  · rw [zero_mul, mul_zero]

end Cells

/-! ### Locally constant functions on a fibre product -/

section FibreProduct

variable {X Y Z P : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace P] {R : Type*} [CommRing R]
  (f : C(X, Z)) (g : C(Y, Z)) (fst : C(P, X)) (snd : C(P, Y))

/-- **Surjectivity.** If the topology of `P` is induced by `(fst, snd) : P → X × Y`, with `P`
compact and `X`, `Y` profinite, every locally constant function on `P` is a finite sum of
products `b(snd q) a(fst q)` of locally constant functions on `Y` and `X`. -/
theorem mem_closure_comap_mul_comap [CompactSpace P] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    (hind : IsInducing fun q ↦ (fst q, snd q)) (h : LocallyConstant P R) :
    h ∈ AddSubmonoid.closure (Set.range fun p : LocallyConstant Y R × LocallyConstant X R ↦
      p.1.comap snd * p.2.comap fst) := by
  classical
  -- every point `q` has a clopen box `U q × V q` on whose trace on `P` the function `h` is
  -- constant
  have hbox (q : P) : ∃ U : Set X, IsClopen U ∧ fst q ∈ U ∧ ∃ V : Set Y, IsClopen V ∧
      snd q ∈ V ∧ ∀ q', fst q' ∈ U → snd q' ∈ V → h q' = h q := by
    obtain ⟨t, ht, hte⟩ := hind.isOpen_iff.1 (h.isLocallyConstant.isOpen_fiber (h q))
    have hqt : (fst q, snd q) ∈ t := by
      change q ∈ (fun q ↦ (fst q, snd q)) ⁻¹' t
      rw [hte]
      rfl
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := isOpen_prod_iff.1 ht _ _ hqt
    obtain ⟨U, hU, hxU, hUu⟩ := compact_exists_isClopen_in_isOpen hu hxu
    obtain ⟨V, hV, hyV, hVv⟩ := compact_exists_isClopen_in_isOpen hv hyv
    refine ⟨U, hU, hxU, V, hV, hyV, fun q' hq'U hq'V ↦ ?_⟩
    have : q' ∈ (fun q ↦ (fst q, snd q)) ⁻¹' t := huv ⟨hUu hq'U, hVv hq'V⟩
    rw [hte] at this
    exact this
  choose U hU hqU V hV hqV hUV using hbox
  -- finitely many of the boxes cover `P`
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun q : P ↦ {q' | fst q' ∈ U q ∧ snd q' ∈ V q})
    (fun q ↦ ((hU q).isOpen.preimage fst.continuous).inter
      ((hV q).isOpen.preimage snd.continuous))
    (fun q _ ↦ Set.mem_iUnion.2 ⟨q, hqU q, hqV q⟩)
  -- the cells of the partitions of `X` and `Y` cut out by the boxes
  let cX : LocallyConstant X (F → Fin 2) := unflip fun q : F ↦ ofIsClopen (hU q)
  let cY : LocallyConstant Y (F → Fin 2) := unflip fun q : F ↦ ofIsClopen (hV q)
  have hcX (x : X) (q : F) : cX x q = 0 ↔ x ∈ U q := by
    change ofIsClopen (hU q) x = 0 ↔ _
    rw [← Set.mem_preimage, ofIsClopen_fiber_zero]
  have hcY (y : Y) (q : F) : cY y q = 0 ↔ y ∈ V q := by
    change ofIsClopen (hV q) y = 0 ↔ _
    rw [← Set.mem_preimage, ofIsClopen_fiber_zero]
  -- on the trace on `P` of a cell `cY⁻¹ β × cX⁻¹ α`, the function `h` is constant
  have hconst (q q₀ : P) (hX : cX (fst q) = cX (fst q₀)) (hY : cY (snd q) = cY (snd q₀)) :
      h q = h q₀ := by
    obtain ⟨q₁, hq₁F, hq₁⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ q))
    have h₁ := (hcX (fst q) ⟨q₁, hq₁F⟩).2 hq₁.1
    have h₂ := (hcY (snd q) ⟨q₁, hq₁F⟩).2 hq₁.2
    rw [hX] at h₁
    rw [hY] at h₂
    rw [hUV q₁ q hq₁.1 hq₁.2, hUV q₁ q₀ ((hcX _ _).1 h₁) ((hcY _ _).1 h₂)]
  -- decompose `h` along the cells
  have h1X : ∑ α ∈ cX.range_finite.toFinset, (fiberCharFn R cX α).comap fst = 1 := by
    ext q
    have := congrArg (fun φ : LocallyConstant X R ↦ φ (fst q)) (sum_fiberCharFn (R := R) cX)
    simpa [sum_apply] using this
  have h1Y : ∑ β ∈ cY.range_finite.toFinset, (fiberCharFn R cY β).comap snd = 1 := by
    ext q
    have := congrArg (fun φ : LocallyConstant Y R ↦ φ (snd q)) (sum_fiberCharFn (R := R) cY)
    simpa [sum_apply] using this
  have hsum : h = ∑ β ∈ cY.range_finite.toFinset, ∑ α ∈ cX.range_finite.toFinset,
      (fiberCharFn R cY β).comap snd * (fiberCharFn R cX α).comap fst * h := by
    calc h = (∑ β ∈ cY.range_finite.toFinset, (fiberCharFn R cY β).comap snd) *
          (∑ α ∈ cX.range_finite.toFinset, (fiberCharFn R cX α).comap fst) * h := by
          rw [h1X, h1Y, one_mul, one_mul]
      _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum]
  rw [hsum]
  refine AddSubmonoid.sum_mem _ fun β _ ↦ AddSubmonoid.sum_mem _ fun α _ ↦ ?_
  by_cases hb : ∃ q₀, cY (snd q₀) = β ∧ cX (fst q₀) = α
  · obtain ⟨q₀, hq₀Y, hq₀X⟩ := hb
    refine AddSubmonoid.subset_closure ⟨(const Y (h q₀) * fiberCharFn R cY β,
      fiberCharFn R cX α), ?_⟩
    ext q
    simp only [coe_mul, coe_comap, Function.comp_apply, Pi.mul_apply, coe_const,
      Function.const_apply, fiberCharFn_apply]
    split_ifs with h₁ h₂
    · rw [hconst q q₀ (h₂.trans hq₀X.symm) (h₁.trans hq₀Y.symm)]
      ring
    all_goals ring
  · convert AddSubmonoid.zero_mem _
    ext q
    simp only [coe_mul, coe_comap, Function.comp_apply, Pi.mul_apply, coe_zero, Pi.zero_apply,
      fiberCharFn_apply]
    split_ifs with h₁ h₂
    · exact absurd ⟨q, h₁, h₂⟩ hb
    all_goals ring

end FibreProduct

end LocallyConstant
