/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusElement
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HomotopyExactSequence
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Weil groups after a finite constant field extension

Let `p : X₀ ⟶ Spec K` be a scheme over a finite field `K` with `q` elements, let `L / K` be a
finite field extension of degree `m`, and let `X₀' = X₀ ×_K Spec L`, the constant cover of `X₀`
attached to `L`, regarded as an `L`-scheme through the second projection `p'`. Base change along
the projection `π : X₀' ⟶ X₀` and a path `τ` induce an injective map
`ρ : π₁(X₀', s') → π₁(X₀, s)` (`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap`).

This file shows that `ρ` identifies the Weil group of `X₀'` over `L` with the elements of degree
divisible by `m` of the Weil group of `X₀` over `K`, the degree being divided by `m`
(blueprint `lem-wf-weil-group-constant-extension`):

* `(g, n) ∈ W(X₀', s')` if and only if `(ρ g, m n) ∈ W(X₀, s)`
  (`AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_constantExtension_iff`);
* if `(ρ g, n) ∈ W(X₀, s)` then `m ∣ n`
  (`AlgebraicGeometry.Scheme.FiniteEtale.dvd_of_mem_weilGroup_constantExtension`);
* if `(h, n) ∈ W(X₀, s)` and `m ∣ n`, then `h` is in the image of `ρ`
  (`AlgebraicGeometry.Scheme.FiniteEtale.mem_range_of_mem_weilGroup_constantExtension`).

The comparison of the Frobenius actions rests on the constant covers: for a finite étale
`K`-algebra `A`, the base change to `X₀'` of `X₀ ×_K Spec A` is `X₀' ×_L Spec (L ⊗_K A)`, on
whose geometric fibre the `q ^ m`-power Frobenius of `L ⊗_K A` acts as the `m`-th power of the
`q`-power Frobenius of `A`. Conversely the constant cover `X₀' ×_L Spec B` of a finite étale
`L`-algebra `B` embeds into the base change of `X₀ ×_K Spec B`. Both are instances of the map of
geometric fibres induced by a ring homomorphism `φ : A → B` over `K → L`
(`AlgebraicGeometry.Scheme.FiniteEtale.constantExtensionFiberMap`), which on the descriptions of
the fibres as sets of ring homomorphisms is precomposition with `φ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

namespace FiniteEtaleAlgebra

variable {k₀ : Type u} [Field k₀]

/-- A finite étale `k₀`-algebra `A`, as an object of `FiniteEtaleAlgebra k₀`. -/
noncomputable abbrev of (A : Type u) [CommRing A] [Algebra k₀ A] [Module.Finite k₀ A]
    [Algebra.Etale k₀ A] : FiniteEtaleAlgebra k₀ :=
  ⟨CommAlgCat.of k₀ A, inferInstanceAs (Module.Finite k₀ A), inferInstanceAs (Algebra.Etale k₀ A)⟩

variable {L : Type u} [Field L]

/-- A finite étale `L`-algebra, for a finite étale field extension `L / k₀`, regarded as a finite
étale `k₀`-algebra. -/
noncomputable def restrictScalars (k₀ : Type u) [Field k₀] [Algebra k₀ L] [Module.Finite k₀ L]
    [Algebra.Etale k₀ L] (B : FiniteEtaleAlgebra L) : FiniteEtaleAlgebra k₀ :=
  letI : Algebra k₀ B.1 := ((algebraMap L B.1).comp (algebraMap k₀ L)).toAlgebra
  haveI : IsScalarTower k₀ L B.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  ⟨CommAlgCat.of k₀ B.1, Module.Finite.trans L B.1, Algebra.Etale.comp k₀ L B.1⟩


/-- The base change `L ⊗_{k₀} A` of a finite étale `k₀`-algebra `A`, a finite étale
`L`-algebra. -/
noncomputable def baseChange [Algebra k₀ L] (A : FiniteEtaleAlgebra k₀) : FiniteEtaleAlgebra L :=
  of (TensorProduct k₀ L A.1)

/-- The ring homomorphism `a ↦ 1 ⊗ a : A → L ⊗_{k₀} A`. -/
noncomputable def includeRight [Algebra k₀ L] (A : FiniteEtaleAlgebra k₀) :
    A.1 →+* (baseChange (L := L) A).1 :=
  Algebra.TensorProduct.includeRight.toRingHom

end FiniteEtaleAlgebra

section Frobenius

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of k₀))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀) (A : FiniteEtaleAlgebra k₀)


/-- If an integral power `Φ ^ n` of the geometric Frobenius fixes a point of the geometric fibre
of the constant cover attached to a finite field extension `L` of degree `m`, then `m ∣ n`. -/
lemma dvd_of_geometricFrobenius_zpow_apply (L : Type u) [Field L] [Algebra k₀ L]
    [Module.Finite k₀ L] [Algebra.Etale k₀ L]
    (z : (fiber s).obj (constantCover p (FiniteEtaleAlgebra.of L))) (n : ℤ)
    (h : (geometricFrobenius p s (FiniteEtaleAlgebra.of L) ^ n) z = z) :
    (Module.finrank k₀ L : ℤ) ∣ n := by
  have : Finite L := Module.finite_of_finite k₀
  have := Fintype.ofFinite k₀
  set Φ := geometricFrobenius p s (FiniteEtaleAlgebra.of L)
  have h' : (Φ⁻¹ ^ n.natAbs) z = z := by
    rcases Int.natAbs_eq n with hn | hn
    · rw [hn, zpow_natCast] at h
      rw [inv_pow]
      exact Equiv.Perm.inv_eq_iff_eq.2 h.symm
    · rw [hn, zpow_neg, zpow_natCast, ← inv_pow] at h
      exact h
  rw [Int.natCast_dvd, ← FiniteField.orderOf_frobeniusAlgHom k₀ L,
    orderOf_dvd_iff_pow_eq_one]
  refine AlgHom.ext fun x ↦ ?_
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
    ← Nat.card_eq_fintype_card]
  have hx : (fiberConstantCoverEquiv p s _ ((Φ⁻¹ ^ n.natAbs) z)).1 x =
      (fiberConstantCoverEquiv p s _ z).1 x := by rw [h']
  rw [fiberConstantCoverEquiv_geometricFrobenius_inv_pow] at hx
  apply (fiberConstantCoverEquiv p s _ z).1.injective
  rw [map_pow]
  exact hx

end Frobenius

variable {K : Type u} [Field K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.Etale K L]

/-- The constant field extension `X₀ ×_K Spec L` of a `K`-scheme `X₀` along a finite field
extension `L / K`: the underlying scheme of the constant cover attached to `L`. -/
noncomputable abbrev constantExtension : Scheme.{u} :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.left

/-- The structure morphism `X₀ ×_K Spec L ⟶ Spec L` of the constant field extension. -/
noncomputable abbrev constantExtensionHom : constantExtension p L ⟶ Spec (.of L) :=
  pullback.snd p (FiniteEtaleAlgebra.of (k₀ := K) L).specHom

/-- The projection `π : X₀ ×_K Spec L ⟶ X₀` of the constant field extension. -/
noncomputable abbrev constantExtensionProj : constantExtension p L ⟶ X₀ :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.hom

lemma constantExtensionProj_comp :
    constantExtensionProj p L ≫ p =
      constantExtensionHom p L ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
  pullback.condition

instance : IsFinite (constantExtensionProj p L) :=
  (constantCover p (FiniteEtaleAlgebra.of L)).property

instance : Etale (constantExtensionProj p L) :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.prop

variable {L} {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s' : Spec (.of Ω') ⟶ constantExtension p L)


section FiberMap

variable {A : FiniteEtaleAlgebra K} {B : FiniteEtaleAlgebra L} (φ : A.1 →+* B.1)
  (hφ : φ.comp (algebraMap K A.1) = (algebraMap L B.1).comp (algebraMap K L))

include hφ

/-- The morphism `X₀' ×_L Spec B ⟶ X₀ ×_K Spec A` induced by a ring homomorphism `φ : A → B`
over `K → L`. -/
noncomputable def constantExtensionLeftMap :
    (constantCover (constantExtensionHom p L) B).obj.left ⟶ (constantCover p A).obj.left :=
  pullback.lift (pullback.fst _ _ ≫ constantExtensionProj p L)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ)) (by
      rw [Category.assoc, constantExtensionProj_comp, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 3
      exact hφ.symm)

@[reassoc (attr := simp)]
lemma constantExtensionLeftMap_fst :
    constantExtensionLeftMap p φ hφ ≫ pullback.fst p A.specHom =
      pullback.fst _ _ ≫ constantExtensionProj p L :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma constantExtensionLeftMap_snd :
    constantExtensionLeftMap p φ hφ ≫ pullback.snd p A.specHom =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

/-- The map `y ↦ y ≫ (π ×_φ 1)` from the geometric fibre of `X₀' ×_L Spec B` at `s'` to that of
`X₀ ×_K Spec A` at `s' ≫ π`. -/
noncomputable def constantExtensionFiberMap
    (y : (fiber s').obj (constantCover (constantExtensionHom p L) B)) :
    (fiber (s' ≫ constantExtensionProj p L)).obj (constantCover p A) :=
  fiberMk _ (constantCover p A) (y.left ≫ constantExtensionLeftMap p φ hφ) (by
    change (y.left ≫ constantExtensionLeftMap p φ hφ) ≫ pullback.fst p A.specHom = _
    rw [Category.assoc, constantExtensionLeftMap_fst, ← Category.assoc]
    exact congrArg (· ≫ constantExtensionProj p L) (fiber_left_comp s' y))


/-- The morphism `X₀' ×_L Spec B ⟶ π^* (X₀ ×_K Spec A)` of finite étale `X₀'`-schemes. -/
noncomputable def constantExtensionToPullback :
    constantCover (constantExtensionHom p L) B ⟶
      (pullback (constantExtensionProj p L)).obj (constantCover p A) :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.lift (constantExtensionLeftMap p φ hφ) (pullback.fst _ _)
      (constantExtensionLeftMap_fst p φ hφ))
    (pullback.lift_snd _ _ _))


variable [Finite K] [Finite L]


end FiberMap

section WeilGroup

variable [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ X₀}
  (τ : pullback (constantExtensionProj p L) ⋙ fiber s' ≅ fiber s)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]


variable (G' : Type u) [Group G'] [∀ P, MulAction G' ((fiber s').obj P)]
  [IsNaturalSMul (fiber s') G']


/-- The diagonal point of the geometric fibre at `s'` of `π^* (X₀ ×_K Spec L)`, the point on the
diagonal section `X₀' ⟶ X₀' ×_{X₀} X₀'`. -/
noncomputable def diagonalPoint :
    (fiber s').obj ((pullback (constantExtensionProj p L)).obj
      (constantCover p (FiniteEtaleAlgebra.of L))) :=
  fiberMk s' _ (s' ≫ pullback.lift (𝟙 _) (𝟙 _) rfl) (by
    change (s' ≫ pullback.lift _ _ _) ≫ pullback.snd _ _ = s'
    simp)


end WeilGroup

section Range

variable [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀]
  [ConnectedSpace (constantExtension p L)]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ X₀}
  (τ : pullback (constantExtensionProj p L) ⋙ fiber s' ≅ fiber s)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
  (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [∀ P, MulAction G' ((fiber s').obj P)] [IsFundamentalGroup (fiber s') G']


end Range

section Exact

variable {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)

omit [Finite K] in
/-- Every finite subset of `K̄` lies in a finite subextension of `K̄ / K`. -/
lemma FiniteSubfield.exists_forall_mem (T : Finset (AlgebraicClosure K)) :
    ∃ L : FiniteSubfield K, ∀ x ∈ T, x ∈ L.1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨⟨⊥, inferInstance⟩, by simp⟩
  | insert a T _ ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨L', h₁, h₂⟩ := FiniteSubfield.exists_ge L (FiniteSubfield.adjoin a)
    refine ⟨L', fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h₂ (FiniteSubfield.mem_adjoin x)
    · exact h₁ (hL x hx)

/-- There are finite subextensions of `K̄ / K` of arbitrarily large degree. -/
lemma FiniteSubfield.exists_lt_finrank (N : ℕ) :
    ∃ L : FiniteSubfield K, N < Module.finrank K L.1 := by
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (AlgebraicClosure K) (Nat.card K ^ N + 1)
  obtain ⟨L, hL⟩ := FiniteSubfield.exists_forall_mem S
  refine ⟨L, ?_⟩
  have := L.2
  have : Finite L.1 := Module.finite_of_finite K
  have hcard : S.card ≤ Nat.card L.1 := by
    change S.card ≤ Nat.card (L.1 : Set (AlgebraicClosure K))
    rw [← Set.ncard_coe_finset, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fun x hx ↦ hL x hx) (Set.toFinite _)
  rw [hS, Module.natCard_eq_pow_finrank (K := K) (V := L.1)] at hcard
  exact (Nat.pow_lt_pow_iff_right Finite.one_lt_card).1 (Nat.lt_of_succ_le hcard)

/-- The geometric Frobenius has infinite order: on the geometric fibre of the constant cover
attached to a finite field extension of degree `m`, it has order `m`, and there are such
extensions of every degree. -/
theorem not_isOfFinOrder_geometricFrobenius : ¬IsOfFinOrder (geometricFrobenius p s) := by
  intro hfin
  obtain ⟨d, hd, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  obtain ⟨L, hL⟩ := FiniteSubfield.exists_lt_finrank (K := K) d
  have := L.2
  have : Algebra.Etale K L.1 := L.toFiniteEtaleAlgebra.2.2
  let : Algebra K Ω := (baseRingHom p s).toAlgebra
  let φ : L.1 →ₐ[K] Ω := IsSepClosed.lift
  let z := (fiberConstantCoverEquiv p s (FiniteEtaleAlgebra.of L.1)).symm
    ⟨φ.toRingHom, φ.comp_algebraMap⟩
  have hz : (geometricFrobenius p s (FiniteEtaleAlgebra.of L.1) ^ (d : ℤ)) z = z := by
    rw [zpow_natCast, ← Pi.pow_apply, hpow]
    rfl
  have hdvd := dvd_of_geometricFrobenius_zpow_apply p s L.1 z d hz
  have := Int.le_of_dvd (by exact_mod_cast hd) hdvd
  omega

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [ConnectedSpace X₀] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- Blueprint `rem-ptr-wf-weil-group-1`: Pointer to the properties of `def-wf-weil-group`.

The exact sequence of `lem-wf-weil-group-exact-sequence` for the Weil group of a connected,
geometrically connected scheme over a finite field: the degree map is surjective, the elements of
degree zero are those of `π₁(X₀, s)` acting trivially on the constant covers, and every lift of
the geometric Frobenius has degree one. -/
theorem exact_weilGroupDeg [GeometricallyConnected p] :
    Function.Surjective (weilGroupDeg p s G) ∧
      Function.Injective ((constantCoverAction p s G).kerToWeilGroup (geometricFrobenius p s)) ∧
      ((constantCoverAction p s G).kerToWeilGroup (geometricFrobenius p s)).range =
        (weilGroupDeg p s G).ker ∧
      ∀ w : weilGroup p s G, constantCoverAction p s G (w : G × Multiplicative ℤ).1 =
        geometricFrobenius p s → weilGroupDeg p s G w = Multiplicative.ofAdd 1 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_geometricFrobenius p s G
  refine (constantCoverAction p s G).exact_weilGroupDeg (geometricFrobenius p s)
    ⟨g, funext fun A ↦ Equiv.ext fun y ↦ hg A y⟩ (not_isOfFinOrder_geometricFrobenius p s)

end Exact

end AlgebraicGeometry.Scheme.FiniteEtale
