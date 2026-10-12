/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# Coordinates and the dimension of generic fibres

Let `X` be a scheme over a field `k`. A global section `t` of `X` defines a coordinate
`X ⟶ 𝔸¹_k = Spec k[t]` (`AlgebraicGeometry.Scheme.coordinate`). If `X` is affine and `x` is a
nonclosed point of `X`, some coordinate sends `x` to the generic point of `𝔸¹_k`
(`AlgebraicGeometry.Scheme.exists_coordinate_apply_eq_genericPoint`). For `f : X ⟶ Y` locally of
finite type with `X` quasi-compact and `Y` Jacobson, the fibre of `f` over a field-valued point
`s` of `Y` with nonclosed image has dimension at most `dim X - 1`
(`AlgebraicGeometry.topologicalKrullDim_pullback_add_one_le`): no point of the fibre is closed in
`X`, so every chain of irreducible closed subsets of the fibre extends by a closed point.

These are the dimension facts behind the inductive step of Verdier biduality
(`thm-weil-etale-geometric-biduality`): the geometric generic fibre of a coordinate has smaller
dimension (compare `lem-fin-coordinate-generic-dimension`), and algebraic field extensions do
not raise this dimension bound.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace

/-- To prove `a + 1 ≤ b` in `WithBot ℕ∞`, it suffices to prove `n + 1 ≤ b` for every natural
number `n ≤ a`. -/
lemma WithBot.add_one_le_of_forall_natCast_le {a b : WithBot ℕ∞}
    (h : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ a → ((n + 1 : ℕ) : WithBot ℕ∞) ≤ b) : a + 1 ≤ b := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      induction b using WithBot.recBotCoe with
      | bot => simpa using h 0 (by simp)
      | coe b =>
        induction b using ENat.recTopCoe with
        | top => exact le_top
        | coe b =>
          have := h (b + 1) (by exact_mod_cast le_top)
          norm_cast at this
          omega
    | coe m => exact_mod_cast h m le_rfl

/-- If no point of a subset `Z` of a quasi-compact `T₀` space `X` is closed in `X`, then
`dim Z + 1 ≤ dim X`: the closure of the smallest member of a chain of irreducible closed subsets
of `Z` contains a closed point of `X`, which extends the chain. -/
theorem topologicalKrullDim_add_one_le_of_forall_not_isClosed {X : Type*} [TopologicalSpace X]
    [T0Space X] [CompactSpace X] (Z : Set X) (hZ : ∀ z ∈ Z, ¬ IsClosed ({z} : Set X)) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim X := by
  refine WithBot.add_one_le_of_forall_natCast_le fun n hn ↦ ?_
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hn
  let f := IrreducibleCloseds.map (Subtype.val : Z → X) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  let l' := l.map f hf
  obtain ⟨y, hy, hyc⟩ := l'.head.isClosed.exists_closed_singleton l'.head.isIrreducible.nonempty
  let c : IrreducibleCloseds X := ⟨{y}, isIrreducible_singleton, hyc⟩
  have hc : c < l'.head := by
    refine lt_of_le_of_ne (Set.singleton_subset_iff.2 hy) fun h ↦ ?_
    obtain ⟨z, hz⟩ := l.head.isIrreducible.nonempty
    have hz' : (z : X) ∈ (l'.head : Set X) := subset_closure ⟨z, hz, rfl⟩
    rw [← h] at hz'
    refine hZ z z.2 ?_
    rw [Set.mem_singleton_iff.1 hz']
    exact hyc
  have := Order.LTSeries.length_le_krullDim (l'.cons c hc)
  rwa [RelSeries.cons_length, LTSeries.map_length, hl, Nat.cast_add_one] at this

namespace AlgebraicGeometry

/-- For `f : X ⟶ Y` locally of finite type and a point `s : Spec K ⟶ Y` with values in a field,
with image `y`, the dimension of `X ×_Y Spec K` is at most that of the fibre `f⁻¹{y}`. -/
theorem topologicalKrullDim_pullback_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {K : Type u} [Field K] (s : Spec (.of K) ⟶ Y) {y : Y}
    (hy : y ∈ Set.range s) :
    topologicalKrullDim (pullback f s : Scheme.{u}) ≤ topologicalKrullDim (f ⁻¹' {y}) := by
  obtain ⟨⟨y', t⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective s
  obtain ⟨z, rfl⟩ := hy
  rw [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply]
  calc topologicalKrullDim (pullback f (Spec.map t ≫ Y.fromSpecResidueField y') : Scheme.{u})
      _ = topologicalKrullDim (pullback (pullback.snd f (Y.fromSpecResidueField y'))
          (Spec.map t) : Scheme) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (pullbackLeftPullbackSndIso f
          (Y.fromSpecResidueField y') (Spec.map t)).hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim (f.fiber y') :=
        topologicalKrullDim_pullback_le_of_field (k := Y.residueField y') _ _
      _ = topologicalKrullDim (f ⁻¹' {y'}) :=
        IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y').isHomeomorph

/-- **Fibres over nonclosed points lose a dimension.** Let `f : X ⟶ Y` be locally of finite type
with `X` quasi-compact and `Y` Jacobson, and let `s : Spec K ⟶ Y` be a point with values in a
field whose image `y` is not closed. Then `dim (X ×_Y Spec K) + 1 ≤ dim X`: since `f` maps
closed points to closed points, no point of the fibre is closed in `X`. -/
theorem topologicalKrullDim_pullback_add_one_le {X Y : Scheme.{u}} [CompactSpace X]
    [JacobsonSpace Y] (f : X ⟶ Y) [LocallyOfFiniteType f] {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ Y) {y : Y} (hy : y ∈ Set.range s) (hs : ¬ IsClosed ({y} : Set Y)) :
    topologicalKrullDim (pullback f s : Scheme.{u}) + 1 ≤ topologicalKrullDim X := by
  refine (add_le_add_left (topologicalKrullDim_pullback_le_preimage f s hy) 1).trans
    (topologicalKrullDim_add_one_le_of_forall_not_isClosed _ fun z hz hzc ↦ hs ?_)
  have := f.closePoints_subset_preimage_closedPoints hzc
  rwa [Set.mem_preimage, Set.mem_singleton_iff.1 hz] at this

namespace Scheme

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))

/-- The coordinate `X ⟶ 𝔸¹_k = Spec k[t]` of a `k`-scheme `X` given by a global section `t`:
it corresponds to the `k`-algebra map `k[t] ⟶ Γ(X, ⊤)` sending the variable to `t`. -/
noncomputable def coordinate (t : Γ(X, ⊤)) : X ⟶ Spec (.of (Polynomial k)) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom ((Scheme.ΓSpecIso (.of k)).inv ≫ a.appTop).hom t))

/-- The coordinate given by a global section is a morphism of `k`-schemes. -/
@[reassoc (attr := simp)]
lemma coordinate_comp (t : Γ(X, ⊤)) :
    coordinate a t ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = a := by
  have : CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((Scheme.ΓSpecIso (.of k)).inv ≫ a.appTop).hom t) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ a.appTop := by
    ext r
    simp
  rw [coordinate, Category.assoc, ← Spec.map_comp, this, Spec.map_comp,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **A coordinate through a nonclosed point.** Let `X` be an affine scheme over a field `k` and
`x` a nonclosed point of `X`. Some global section `t` has transcendental image in `κ(x)`, i.e.
the coordinate given by `t` sends `x` to the generic point of `𝔸¹_k`: otherwise `Γ(X, ⊤)/𝔭ₓ`
would be a domain algebraic over `k`, hence a field, and `x` would be closed. -/
theorem exists_coordinate_apply_eq_genericPoint {k : Type u} [Field k] [IsAffine X]
    (a : X ⟶ Spec (.of k)) {x : X} (hx : ¬ IsClosed ({x} : Set X)) :
    ∃ t : Γ(X, ⊤), coordinate a t x = genericPoint (Spec (.of (Polynomial k))) := by
  classical
  by_contra! h
  let φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ a.appTop).hom
  let P := (X.toSpecΓ x).asIdeal
  let : Algebra k (Γ(X, ⊤) ⧸ P) := ((Ideal.Quotient.mk P).comp φ).toAlgebra
  have : Algebra.IsAlgebraic k (Γ(X, ⊤) ⧸ P) := by
    refine ⟨fun q ↦ ?_⟩
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hne : Ideal.comap (Polynomial.eval₂RingHom φ t) P ≠ ⊥ := fun h0 ↦ h t (by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext h0)
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨f, hf0, ?_⟩
    rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra, ← Polynomial.hom_eval₂,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hf
  have hP : P.IsMaximal := Ideal.Quotient.maximal_of_isField P
    (isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k))
  refine hx ?_
  have hinj : Function.Injective X.toSpecΓ := X.toSpecΓ.isOpenEmbedding.injective
  rw [← Set.preimage_image_eq {x} hinj, Set.image_singleton]
  exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hP).preimage
    X.toSpecΓ.continuous

end Scheme

end AlgebraicGeometry
