/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.TraceFormula.Frobenius

/-!

# The fixed scheme of a Frobenius

For a finite type `σ`, the disjoint union `∐_σ Spec k` of copies of the base point is a scheme
finite over `Spec k` (`ProEtale.CondensedRing.sigmaPoint`), whose components are open and
closed points (`ProEtale.CondensedRing.sigmaPointι`).

For the model Frobenius `Φ` of `X = X₀ ×_{k₀} k`, the rational points fixed by the iterate `Φ_m`
induce a morphism `∐_{x ∈ X(k)^{Φ_m}} Spec k ⟶ X` equalizing `𝟙` and `Φ_m`
(`ProEtale.CondensedRing.fixedPointsι`).

## Sorried input

- `ProEtale.CondensedRing.IsModelFrobenius.nonempty_isLimit_fixedPointsFork`: this
  morphism is an equalizer of `𝟙` and `Φ_m`, i.e. the fixed scheme `Fix(Φ_m)` is the disjoint
  union of copies of `Spec k` indexed by the fixed rational points (blueprint
  `thm-trf-frobenius-fixed-points`, a node of the six-functor chapter).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-! ### Disjoint unions of points -/

section SigmaPoint

variable (k) (σ : Type u)

/-- The disjoint union `∐_σ Spec k` of copies of the base point, over `Spec k`. -/
noncomputable def sigmaPoint : Over (Spec (.of k)) :=
  Over.mk (Sigma.desc fun _ : σ ↦ 𝟙 (Spec (.of k)))

/-- The structure morphism of `∐_σ Spec k` is `∐_σ Spec k ≅ Spec (σ → k) ⟶ Spec k`. -/
lemma sigmaDesc_id_eq_sigmaSpec_comp :
    (Sigma.desc fun _ : σ ↦ 𝟙 (Spec (.of k))) =
      sigmaSpec (fun _ : σ ↦ CommRingCat.of k) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (σ → k))) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [Sigma.ι_desc, ι_sigmaSpec_assoc, ← Spec.map_comp, ← Spec.map_id]
  rfl

/-- The inclusion of a component of `∐_σ Spec k` is `Spec k ⟶ Spec (σ → k) ≅ ∐_σ Spec k`. -/
lemma sigmaι_eq_specMap_comp [Finite σ] (i : σ) :
    Sigma.ι (fun _ : σ ↦ Spec (.of k)) i =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : σ ↦ k) i)) ≫
        inv (sigmaSpec fun _ : σ ↦ CommRingCat.of k) :=
  (IsIso.eq_comp_inv _).2 (ι_sigmaSpec _ i)

instance [Finite σ] : IsFinite (sigmaPoint k σ).hom := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (σ → k)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have h : (sigmaPoint k σ).hom = sigmaSpec (fun _ : σ ↦ CommRingCat.of k) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (σ → k))) :=
    sigmaDesc_id_eq_sigmaSpec_comp k σ
  rw [h]
  infer_instance

/-- The inclusion of the component `i` of `∐_σ Spec k`. -/
noncomputable def sigmaPointι (i : σ) : point k ⟶ sigmaPoint k σ :=
  Over.homMk (Sigma.ι (fun _ : σ ↦ Spec (.of k)) i) (by simp [sigmaPoint])

@[simp]
lemma sigmaPointι_left (i : σ) :
    (sigmaPointι k σ i).left = Sigma.ι (fun _ : σ ↦ Spec (.of k)) i :=
  rfl

instance [Finite σ] (i : σ) : IsOpenImmersion (sigmaPointι k σ i).left := by
  rw [sigmaPointι_left, sigmaι_eq_specMap_comp]
  infer_instance

instance [Finite σ] (i : σ) : IsClosedImmersion (sigmaPointι k σ i).left := by
  rw [sigmaPointι_left, sigmaι_eq_specMap_comp]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : σ ↦ k) i))) :=
    IsClosedImmersion.spec_of_surjective _ (Function.surjective_eval i)
  infer_instance

/-- The components of `∐_σ Spec k` are pairwise disjoint. -/
lemma disjoint_range_sigmaPointι {i i' : σ} (h : i ≠ i') :
    Disjoint (Set.range (sigmaPointι k σ i).left.base)
      (Set.range (sigmaPointι k σ i').left.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  exact h (congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : σ ↦ Spec (.of k)) i' i b a).mp hb)).symm

/-- The components of `∐_σ Spec k` cover it. -/
lemma iUnion_range_sigmaPointι :
    ⋃ i, Set.range (sigmaPointι k σ i).left.base = Set.univ := by
  refine Set.eq_univ_of_forall fun p ↦ ?_
  obtain ⟨⟨i, a⟩, rfl⟩ := (sigmaMk (fun _ : σ ↦ Spec (.of k))).surjective p
  exact Set.mem_iUnion.mpr ⟨i, a, (sigmaMk_mk (fun _ : σ ↦ Spec (.of k)) i a).symm⟩

end SigmaPoint

/-! ### The fixed points of a Frobenius -/

section FixedPoints

variable {X : Over (Spec (.of k))} (Φ : X ⟶ X) (m : ℕ)

/-- The morphism `∐_{x ∈ X(k)^{Φ_m}} Spec k ⟶ X` given by the rational points fixed by `Φ_m`. -/
noncomputable def fixedPointsι : sigmaPoint k (FixedPoint Φ m) ⟶ X :=
  Over.homMk (Sigma.desc fun x ↦ x.1.left) (by
    refine Sigma.hom_ext _ _ fun x ↦ ?_
    simp [sigmaPoint])

@[reassoc (attr := simp)]
lemma sigmaPointι_fixedPointsι (x : FixedPoint Φ m) :
    sigmaPointι k (FixedPoint Φ m) x ≫ fixedPointsι Φ m = x.1 := by
  ext1
  simp [fixedPointsι, sigmaPointι_left]

/-- The fixed rational points are equalized by `𝟙` and `Φ_m`. -/
lemma fixedPointsι_comp :
    fixedPointsι Φ m ≫ 𝟙 X = fixedPointsι Φ m ≫ frobeniusIterate Φ m := by
  ext1
  refine Sigma.hom_ext _ _ fun x ↦ ?_
  have hx := congrArg Over.Hom.left x.2
  rw [Over.comp_left] at hx
  simp [fixedPointsι, hx]

set_option linter.overlappingInstances false in
/-- **The fixed scheme of a Frobenius** (blueprint `thm-trf-frobenius-fixed-points`, a node of
the six-functor chapter): for the model Frobenius `Φ` of `X = X₀ ×_{k₀} k` and `m ≥ 1`, the
fixed scheme `Fix(Φ_m)`, the equalizer of `𝟙` and `Φ_m`, is the disjoint union
`∐ Spec k` of copies of the base point, one for each rational point fixed by `Φ_m` (these
correspond to the `𝔽_{q^m}`-points of `X₀`, `IsModelFrobenius.fixedPointEquiv`). On affine
charts the fixed algebra is `k[t] / (t_i^{q^m} - t_i) + 𝔞`, a finite product of copies of `k`. -/
theorem IsModelFrobenius.nonempty_isLimit_fixedPointsFork [IsAlgClosed k]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}
    {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ} (hm : 1 ≤ m)
    [Finite (FixedPoint Φ m)] :
    Nonempty (IsLimit (Fork.ofι (fixedPointsι Φ m) (fixedPointsι_comp Φ m))) :=
  sorry

end FixedPoints

end AlgebraicGeometry.ProEtale.CondensedRing
