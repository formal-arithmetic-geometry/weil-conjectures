/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Abelian algebraic l-adic representations -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

open scoped TensorProduct Matrix ZeroObject

namespace AlgebraicGeometry.Scheme

noncomputable section

universe v w

private theorem isLAdic_of_basis_model
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module K V]
    (τ : G →* (V ≃ₗ[K] V)) (E : IntermediateField ℚ_[l] K)
    [FiniteDimensional ℚ_[l] E] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V)
    (σ : G →* ((ι → E) ≃ₗ[E] (ι → E)))
    (hc : Representation.IsContinuousCoefficient l E G (ι → E) σ)
    (ha : letI := Module.compHom V (algebraMap E K)
      ∀ g v, Fintype.linearCombination E b (σ g v) =
        τ g (Fintype.linearCombination E b v)) :
    Representation.IsLAdic l K G V τ := by
  classical
  let := Module.compHom V (algebraMap E K)
  let f : (ι → E) →ₗ[E] V := Fintype.linearCombination E b
  have hf : Function.Injective f :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp
      (b.linearIndependent.restrict_scalars' E)
  let W : Submodule E V := f.range
  let c : (ι → E) ≃ₗ[E] W := LinearEquiv.ofInjective f hf
  let τW : G →* (W ≃ₗ[E] W) :=
    { toFun g := (c.symm.trans (σ g)).trans c
      map_one' := by ext v; simp
      map_mul' g h := by ext v; simp }
  have hW : FiniteDimensional E W := Module.Finite.equiv c
  refine ⟨Module.Finite.of_basis b, E, inferInstance, W, τW, ⟨hW, ?_⟩, ?_, ?_⟩
  · let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace (ι → E) := moduleTopology E (ι → E)
    let : TopologicalSpace W := moduleTopology E W
    have : IsTopologicalAddGroup (ι → E) := IsModuleTopology.topologicalAddGroup E _
    have : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup E _
    have : ContinuousSMul E (ι → E) := IsModuleTopology.toContinuousSMul E _
    have : ContinuousSMul E W := IsModuleTopology.toContinuousSMul E _
    have : ContinuousAdd (ι → E) :=
      (IsModuleTopology.topologicalAddGroup E (ι → E)).toContinuousAdd
    have : ContinuousAdd W := (IsModuleTopology.topologicalAddGroup E W).toContinuousAdd
    have hc' := IsModuleTopology.continuous_of_linearMap c.toLinearMap
    have hci := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
    exact hc'.comp (hc.2.comp (continuous_fst.prodMk (hci.comp continuous_snd)))
  · intro g x
    change f (σ g (c.symm x)) = τ g (x : V)
    rw [ha]
    congr 1
    exact congrArg Subtype.val (c.apply_symm_apply x)
  · let e := (c.symm.baseChange E K _ _).trans (IsBaseChange.of_fintype_basis E b).equiv
    refine ⟨e, ?_⟩
    intro a x
    change (IsBaseChange.of_fintype_basis E b).equiv
      (c.symm.baseChange E K _ _ (a ⊗ₜ[E] x)) = _
    rw [LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul]
    congr 1
    exact congrArg Subtype.val (c.apply_symm_apply x)

private theorem isLAdic_of_matrix_model
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module K V]
    (τ : G →* (V ≃ₗ[K] V)) (E : IntermediateField ℚ_[l] K)
    [FiniteDimensional ℚ_[l] E] {ι : Type*} [Finite ι]
    (b : Module.Basis ι K V) (M : G → Matrix ι ι E)
    (he : ∀ g i j, algebraMap E K (M g i j) = b.repr (τ g (b j)) i)
    (hc : letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
      ∀ i j, Continuous (fun g ↦ M g i j)) :
    Representation.IsLAdic l K G V τ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let r : Representation K G V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp τ
  have he' (g : G) : (M g).map (algebraMap E K) = LinearMap.toMatrix b b (r g) := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply]
    exact he g i j
  let m : G →* Matrix ι ι E :=
    { toFun := M
      map_one' := by
        apply Matrix.map_injective (algebraMap E K).injective
        change (M 1).map (algebraMap E K) = (1 : Matrix ι ι E).map (algebraMap E K)
        rw [he', Matrix.map_one _ (map_zero _) (map_one _), map_one,
          LinearMap.toMatrix_one]
      map_mul' g h := by
        apply Matrix.map_injective (algebraMap E K).injective
        change (M (g * h)).map (algebraMap E K) =
          (M g * M h).map (algebraMap E K)
        rw [Matrix.map_mul, he', he', he', map_mul, LinearMap.toMatrix_mul] }
  let σ : G →* ((ι → E) ≃ₗ[E] (ι → E)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E (ι → E)).toMonoidHom.comp
      ((Units.map (Matrix.toLinAlgEquiv' : Matrix ι ι E ≃ₐ[E] _).toMonoidHom).comp
        m.toHomUnits)
  have hσ (g : G) (v : ι → E) : σ g v = M g *ᵥ v := by
    change Matrix.toLinAlgEquiv' (M g) v = _
    exact Matrix.toLinAlgEquiv'_apply _ _
  have hcont : Representation.IsContinuousCoefficient l E G (ι → E) σ := by
    refine ⟨inferInstance, ?_⟩
    let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace (ι → E) := moduleTopology E (ι → E)
    have : IsTopologicalAddGroup (ι → E) := IsModuleTopology.topologicalAddGroup E _
    have : ContinuousSMul E (ι → E) := IsModuleTopology.toContinuousSMul E _
    have hcoord (j : ι) : Continuous (fun v : (ι → E) ↦ v j) :=
      IsModuleTopology.continuous_of_linearMap (LinearMap.proj j : (ι → E) →ₗ[E] E)
    have : ContinuousAdd (ι → E) :=
      (IsModuleTopology.topologicalAddGroup E (ι → E)).toContinuousAdd
    have hsum : Continuous (fun p : G × (ι → E) ↦ M p.1 *ᵥ p.2) := by
      have hvec : Continuous (fun p : G × (ι → E) ↦
          ∑ i, (∑ j, M p.1 i j * p.2 j) • Pi.single i (1 : E)) :=
        continuous_finsetSum _ (fun i _ ↦
          (continuous_finsetSum _ (fun j _ ↦
            ((hc i j).comp continuous_fst).mul ((hcoord j).comp continuous_snd))).smul
              continuous_const)
      exact hvec.congr (fun p ↦ by
        funext i
        simp [Matrix.mulVec, dotProduct, Pi.single_apply])
    exact hsum.congr (fun p ↦ (hσ p.1 p.2).symm)
  let := Module.compHom V (algebraMap E K)
  let f := Fintype.linearCombination E b
  have hcoord (v : ι → E) :
      (fun i ↦ algebraMap E K (v i)) = b.equivFun (f v) :=
    (IsBaseChange.of_fintype_basis_eq (A := E) (b := b)).mp rfl
  apply isLAdic_of_basis_model l K G V τ E b σ hcont
  intro g v
  apply (IsBaseChange.of_fintype_basis_eq (A := E) (b := b)).mpr
  funext i
  change algebraMap E K ((σ g v) i) = b.repr (τ g (f v)) i
  rw [hσ, RingHom.map_mulVec]
  change ((M g).map (algebraMap E K) *ᵥ (fun j ↦ algebraMap E K (v j))) i = _
  rw [he', hcoord]
  exact congrFun (LinearMap.toMatrix_mulVec_repr b b (r g) (f v)) i

private theorem isLAdic_of_matrix_compression
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module K V]
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : Representation.IsLAdic l K G V ρ)
    (U : Type w) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : G →* (U ≃ₗ[K] U))
    (i : U →ₗ[K] V) (p : V →ₗ[K] U)
    (hτ : ∀ (g : G) (v : U), p (ρ g (i v)) = τ g v) :
    Representation.IsLAdic l K G U τ := by
  classical
  obtain ⟨hfin, E, hE, W, τE, hcE, hτE, e, he⟩ := hρ
  have := hfin
  have := hE
  let := Module.compHom V (algebraMap E K)
  have : FiniteDimensional E W := hcE.1
  let c := Module.finBasis E W
  let a := (c.baseChange K).map e
  let b := Module.finBasis K U
  let A := LinearMap.toMatrix b a i
  let D := LinearMap.toMatrix a b p
  let B (g : G) := LinearMap.toMatrix c c (τE g).toLinearMap
  have hai (i) : a i = (c i : V) := by
    change e (c.baseChange K i) = _
    rw [Module.Basis.baseChange_apply, he, one_smul]
  have har (v : W) (i) : a.repr (v : V) i = algebraMap E K (c.repr v i) := by
    have hv : e (1 ⊗ₜ[E] v) = (v : V) := by rw [he, one_smul]
    rw [← hv]
    change (c.baseChange K).repr (e.symm (e (1 ⊗ₜ[E] v))) i = _
    rw [e.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
    simp [Algebra.smul_def]
  have hB (g : G) : (B g).map (algebraMap E K) =
      LinearMap.toMatrix a a (ρ g).toLinearMap := by
    ext i j
    simp only [Matrix.map_apply, B, LinearMap.toMatrix_apply]
    change algebraMap E K (c.repr (τE g (c j)) i) = a.repr (ρ g (a j)) i
    rw [hai, ← hτE, har]
  let C : ((Fin (Module.finrank E W) × Fin (Module.finrank K U)) ⊕
      (Fin (Module.finrank K U) × Fin (Module.finrank E W))) → K :=
    fun s ↦ match s with
    | .inl ij => A ij.1 ij.2
    | .inr ij => D ij.1 ij.2
  let J := IntermediateField.adjoin ℚ_[l] (Set.range C)
  have : Finite (Set.range C) := (Set.finite_range C).to_subtype
  have : FiniteDimensional ℚ_[l] J :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  let L : IntermediateField ℚ_[l] K := E ⊔ J
  have : FiniteDimensional ℚ_[l] L := inferInstance
  have hC (z) : C z ∈ L :=
    (show J ≤ L from le_sup_right)
      (IntermediateField.subset_adjoin ℚ_[l] (Set.range C) (Set.mem_range_self z))
  let A' : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank K U)) L :=
    fun i j ↦ ⟨A i j, hC (.inl (i, j))⟩
  let D' : Matrix (Fin (Module.finrank K U)) (Fin (Module.finrank E W)) L :=
    fun i j ↦ ⟨D i j, hC (.inr (i, j))⟩
  let inc : E →ₐ[ℚ_[l]] L := IntermediateField.inclusion le_sup_left
  let M (g : G) := D' * (B g).map inc * A'
  have hM (g : G) : (M g).map (algebraMap L K) =
      LinearMap.toMatrix b b (τ g).toLinearMap := by
    have hA : A'.map (algebraMap L K) = A := rfl
    have hD : D'.map (algebraMap L K) = D := rfl
    have hi : ((B g).map inc).map (algebraMap L K) = (B g).map (algebraMap E K) := rfl
    change (D' * (B g).map inc * A').map (algebraMap L K) = _
    rw [Matrix.map_mul, Matrix.map_mul, hA, hD, hi, hB]
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    apply LinearMap.ext
    intro v
    exact hτ g v
  apply isLAdic_of_matrix_model l K G U τ L b M
    (fun g i j ↦ by
      have h := congrFun (congrFun (hM g) i) j
      rw [Matrix.map_apply, LinearMap.toMatrix_apply] at h
      exact h)
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let := spectralNorm.nontriviallyNormedField ℚ_[l] L
  let : NormedAlgebra ℚ_[l] E := spectralNorm.normedAlgebra ℚ_[l] E
  let : NormedAlgebra ℚ_[l] L := spectralNorm.normedAlgebra ℚ_[l] L
  have hi : Continuous inc := inc.toLinearMap.continuous_of_finiteDimensional
  have hbc (i j) : Continuous (fun g ↦ B g i j) := by
    let : TopologicalSpace W := moduleTopology E W
    have : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup E W
    have : ContinuousSMul E W := IsModuleTopology.toContinuousSMul E W
    have hr : Continuous (c.coord i) :=
      IsModuleTopology.continuous_of_linearMap (c.coord i)
    have h := hr.comp (hcE.2.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : G ↦ c j))))
    exact h.congr (fun g ↦ by
      change c.coord i (τE g (c j)) = B g i j
      rw [Module.Basis.coord_apply]
      exact (LinearMap.toMatrix_apply c c (τE g).toLinearMap i j).symm)
  intro i j
  change Continuous (fun g ↦ ∑ k, (∑ t, D' i t * inc (B g t k)) * A' k j)
  exact continuous_finsetSum _ (fun k _ ↦
    (continuous_finsetSum _ (fun t _ ↦
      continuous_const.mul (hi.comp (hbc t k)))).mul continuous_const)

private theorem isLAdic_matrix_model
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module K V]
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : Representation.IsLAdic l K G V ρ) :
    ∃ (E : IntermediateField ℚ_[l] K) (_ : FiniteDimensional ℚ_[l] E)
      (n : ℕ) (b : Module.Basis (Fin n) K V) (M : G → Matrix (Fin n) (Fin n) E),
      (∀ g i j, algebraMap E K (M g i j) = b.repr (ρ g (b j)) i) ∧
      (letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
       ∀ i j, Continuous (fun g ↦ M g i j)) := by
  classical
  obtain ⟨hfin, E, hE, W, τE, hcE, hτE, e, he⟩ := hρ
  have := hfin
  have := hE
  let := Module.compHom V (algebraMap E K)
  have : FiniteDimensional E W := hcE.1
  let c := Module.finBasis E W
  let a := (c.baseChange K).map e
  let B (g : G) := LinearMap.toMatrix c c (τE g).toLinearMap
  have hai (i) : a i = (c i : V) := by
    change e (c.baseChange K i) = _
    rw [Module.Basis.baseChange_apply, he, one_smul]
  have har (v : W) (i) : a.repr (v : V) i = algebraMap E K (c.repr v i) := by
    have hv : e (1 ⊗ₜ[E] v) = (v : V) := by rw [he, one_smul]
    rw [← hv]
    change (c.baseChange K).repr (e.symm (e (1 ⊗ₜ[E] v))) i = _
    rw [e.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
    simp [Algebra.smul_def]
  refine ⟨E, hE, Module.finrank E W, a, B, ?_, ?_⟩
  · intro g i j
    rw [hai, ← hτE, har]
    exact congrArg (algebraMap E K) (LinearMap.toMatrix_apply c c
      (τE g).toLinearMap i j)
  · let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace W := moduleTopology E W
    have : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup E W
    have : ContinuousSMul E W := IsModuleTopology.toContinuousSMul E W
    intro i j
    have hr : Continuous (c.coord i) :=
      IsModuleTopology.continuous_of_linearMap (c.coord i)
    have h := hr.comp (hcE.2.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : G ↦ c j))))
    exact h.congr (fun g ↦ by
      change c.coord i (τE g (c j)) = B g i j
      rw [Module.Basis.coord_apply]
      exact (LinearMap.toMatrix_apply c c (τE g).toLinearMap i j).symm)

private theorem isLAdic_product
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V U : Type w) [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    (ρ : G →* (V ≃ₗ[K] V)) (τ : G →* (U ≃ₗ[K] U))
    (hρ : Representation.IsLAdic l K G V ρ) (hτ : Representation.IsLAdic l K G U τ)
    (σ : G →* ((V × U) ≃ₗ[K] (V × U)))
    (hσ : ∀ g v, σ g v = (ρ g v.1, τ g v.2)) :
    Representation.IsLAdic l K G (V × U) σ := by
  classical
  obtain ⟨E, hE, n, a, A, hA, hcA⟩ := isLAdic_matrix_model l K G V ρ hρ
  obtain ⟨F, hF, m, b, B, hB, hcB⟩ := isLAdic_matrix_model l K G U τ hτ
  have := hE
  have := hF
  let L : IntermediateField ℚ_[l] K := E ⊔ F
  have : FiniteDimensional ℚ_[l] L := inferInstance
  let incE : E →ₐ[ℚ_[l]] L := IntermediateField.inclusion le_sup_left
  let incF : F →ₐ[ℚ_[l]] L := IntermediateField.inclusion le_sup_right
  let M (g : G) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) L :=
    Matrix.fromBlocks ((A g).map incE) 0 0 ((B g).map incF)
  apply isLAdic_of_matrix_model l K G (V × U) σ L (a.prod b) M
  · intro g i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simpa [M, hσ, Module.Basis.prod_apply, incE] using hA g i j
      | inr j => simp [M, hσ, Module.Basis.prod_apply]
    | inr i =>
      cases j with
      | inl j => simp [M, hσ, Module.Basis.prod_apply]
      | inr j =>
        simpa [M, hσ, Module.Basis.prod_apply, incF] using hB g i j
  · let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let := spectralNorm.nontriviallyNormedField ℚ_[l] F
    let := spectralNorm.nontriviallyNormedField ℚ_[l] L
    let : NormedAlgebra ℚ_[l] E := spectralNorm.normedAlgebra ℚ_[l] E
    let : NormedAlgebra ℚ_[l] F := spectralNorm.normedAlgebra ℚ_[l] F
    let : NormedAlgebra ℚ_[l] L := spectralNorm.normedAlgebra ℚ_[l] L
    have hiE : Continuous incE := incE.toLinearMap.continuous_of_finiteDimensional
    have hiF : Continuous incF := incF.toLinearMap.continuous_of_finiteDimensional
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hiE.comp (hcA i j)
      | inr j => exact continuous_const
    | inr i =>
      cases j with
      | inl j => exact continuous_const
      | inr j => exact hiF.comp (hcB i j)

private theorem adic_of_mono
    (l : ℕ) [Fact l.Prime] (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] {G : Type u} [Group G] [TopologicalSpace G]
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    {X Y : Rep.{u + 1} K G} (f : X ⟶ Y) [Mono f]
    (hY : Representation.IsLAdic l K P Y.V ((galoisRepLinearAction K Y).comp
      δ.symm.toMonoidHom)) :
    Representation.IsLAdic l K P X.V ((galoisRepLinearAction K X).comp
      δ.symm.toMonoidHom) := by
  have : FiniteDimensional K Y.V := hY.1
  have hf := (Rep.mono_iff_injective f).mp inferInstance
  have : FiniteDimensional K X.V := FiniteDimensional.of_injective f.hom.toLinearMap hf
  obtain ⟨p, hp⟩ := f.hom.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  apply isLAdic_of_matrix_compression l K P Y.V _ hY X.V _ f.hom.toLinearMap p
  intro g z
  change p (Y.ρ (δ.symm g) (f.hom z)) = X.ρ (δ.symm g) z
  rw [← Rep.hom_comm_apply f]
  exact congrArg (fun k : X.V →ₗ[K] X.V ↦ k (X.ρ (δ.symm g) z)) hp

private theorem adic_of_epi
    (l : ℕ) [Fact l.Prime] (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] {G : Type u} [Group G] [TopologicalSpace G]
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    {X Y : Rep.{u + 1} K G} (f : X ⟶ Y) [Epi f]
    (hX : Representation.IsLAdic l K P X.V ((galoisRepLinearAction K X).comp
      δ.symm.toMonoidHom)) :
    Representation.IsLAdic l K P Y.V ((galoisRepLinearAction K Y).comp
      δ.symm.toMonoidHom) := by
  have : FiniteDimensional K X.V := hX.1
  have hf := (Rep.epi_iff_surjective f).mp inferInstance
  have : FiniteDimensional K Y.V := FiniteDimensional.of_surjective f.hom.toLinearMap hf
  obtain ⟨i, hi⟩ := f.hom.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  apply isLAdic_of_matrix_compression l K P X.V _ hX Y.V _ i f.hom.toLinearMap
  intro g z
  change f.hom (X.ρ (δ.symm g) (i z)) = Y.ρ (δ.symm g) z
  rw [Rep.hom_comm_apply f]
  exact congrArg (Y.ρ (δ.symm g)) (congrArg (fun k : Y.V →ₗ[K] Y.V ↦ k z) hi)

private def repProductCone {K : Type (u + 1)} [Field K] {G : Type u} [Group G]
    (X Y : Rep.{u + 1} K G) : BinaryFan X Y :=
  BinaryFan.mk (P := Rep.of (X.ρ.prod Y.ρ))
    (Rep.ofHom (.fst K X.ρ Y.ρ)) (Rep.ofHom (.snd K X.ρ Y.ρ))

private def repProductIsLimit {K : Type (u + 1)} [Field K] {G : Type u} [Group G]
    (X Y : Rep.{u + 1} K G) : IsLimit (repProductCone X Y) :=
  BinaryFan.IsLimit.mk _
    (fun f g ↦ Rep.ofHom (f.hom.prod g.hom))
    (by intro P f g; ext z; rfl) (by intro P f g; ext z; rfl)
    (by intro P f g h h₁ h₂; ext z; exact Prod.ext
          (congrArg (fun k ↦ k.hom z) h₁) (congrArg (fun k ↦ k.hom z) h₂))

/-- The full category of algebraic l-adic representations is abelian.
Source: Deligne, Weil II (1.1.1), (1.1.6), and Stanford Weil II seminar L19,
Proposition 1.1.9. (blueprint: new-c5-galois-adic-algebraic-abelian).

Proof: express an l-adic action in a finite basis over a finite coefficient field.
For an invariant subspace, choose a linear retraction; for a quotient choose a section.
Adjoin their finitely many matrix entries to the coefficient field. The compressed
matrices give the induced action, and their entries are continuous since field inclusions
between finite extensions are continuous. A basis model reconstructs the required
coefficient submodule and its scalar-extension equivalence. For products, pass to the
compositum of the two coefficient fields and use block-diagonal matrices in the product
basis. Thus the full subcategory is closed under subobjects, quotients and finite
products. The empty matrix model gives zero closure. Apply
Mathlib's abelian-subcategory construction. The normalized-construction hypothesis is
not needed for this part. The matrix argument generalizes the subrepresentation proof
in `Sheaf.RepresentationTheory.LAdicSubrepresentation` to arbitrary matrix compressions. -/
theorem galois_adic_algebraic_abelian
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) :
    galoisAlgebraicRepresentationsAbelian y G c l Q d := by
  classical
  let S : ObjectProperty (Rep.{u + 1} Q G) := fun X ↦
    Representation.IsLAdic l Q d.P X.V ((galoisRepLinearAction Q X).comp
      d.δ.symm.toMonoidHom)
  have : S.IsClosedUnderSubobjects := ⟨fun f _ hY ↦ adic_of_mono l Q d.P d.δ f hY⟩
  have : S.IsClosedUnderQuotients := ⟨fun f _ hX ↦ adic_of_epi l Q d.P d.δ f hX⟩
  have : S.ContainsZero := by
    refine ⟨⟨0, isZero_zero _, ?_⟩⟩
    have : Subsingleton (0 : Rep.{u + 1} Q G).V :=
      (Rep.isZero_iff Q G _).mp (isZero_zero _)
    apply isLAdic_of_matrix_model l Q d.P (0 : Rep.{u + 1} Q G).V _
      (⊥ : IntermediateField ℚ_[l] Q) (Module.Basis.empty (ι := Fin 0) _) (fun _ ↦ 0)
    · intro g i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  have hprod (X Z : Rep.{u + 1} Q G) (hX : S X) (hZ : S Z) : S (X ⨯ Z) := by
    have hS : S (Rep.of (X.ρ.prod Z.ρ)) :=
      isLAdic_product l Q d.P X.V Z.V _ _ hX hZ _ (fun _ _ ↦ rfl)
    exact S.prop_of_iso ((limit.isLimit _).conePointUniqueUpToIso
      (repProductIsLimit X Z)).symm hS
  have : S.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨D, hD⟩
    exact S.prop_of_iso (HasLimit.isoOfNatIso (diagramIsoPair D)).symm
      (hprod _ _ (hD ⟨.left⟩) (hD ⟨.right⟩)))
  have : S.IsClosedUnderFiniteProducts := .mk'
  exact ⟨inferInstanceAs (Abelian S.FullSubcategory)⟩

end

end AlgebraicGeometry.Scheme
