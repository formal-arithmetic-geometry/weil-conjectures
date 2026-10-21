/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.RepresentationTheory.LAdic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Subrepresentations of algebraic l-adic representations

Source: Deligne, Weil II (1.1.6), and the invariant-subspace argument in the proof of
`lem-zl-common-irreducibility-detecting-cover`.
-/

@[expose] public section
set_option autoImplicit false

universe u v w

namespace Representation

open scoped TensorProduct Matrix

private theorem isLAdic_of_basis_model
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module K V]
    (τ : G →* (V ≃ₗ[K] V)) (E : IntermediateField ℚ_[l] K)
    [FiniteDimensional ℚ_[l] E] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V)
    (σ : G →* ((ι → E) ≃ₗ[E] (ι → E)))
    (hc : IsContinuousCoefficient l E G (ι → E) σ)
    (ha : letI := Module.compHom V (algebraMap E K)
      ∀ g v, Fintype.linearCombination E b (σ g v) =
        τ g (Fintype.linearCombination E b v)) :
    IsLAdic l K G V τ := by
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
    IsLAdic l K G V τ := by
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
  have hcont : IsContinuousCoefficient l E G (ι → E) σ := by
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

/-- Every invariant subspace of an algebraic l-adic representation is l-adic.
The equation on the subtype specifies its action uniquely.

Source: Deligne, Weil II (1.1.6); blueprint main-20261015, proof of
`lem-zl-curve-testing-irreducibility`, first six sentences, invariant-subspace descent
(blueprint: lem-zl-ladic-invariant-subspace-descent).

Proof: choose a continuous model over E and a basis of it, giving an ambient K-basis.
Choose a K-basis of U and a linear projection onto U. If J and P are the matrices of
inclusion and projection, the restricted action matrix is P rho(g) J. Adjoin the finitely
many entries of P and J to E. This gives a finite extension L of Q_l because K is algebraic.
The displayed matrix formula now lies in L. Its group identities follow by injection into K.
The inclusion E to L is Q_l-linear between finite-dimensional normed spaces, so it is
continuous for the spectral norms; hence the formula has continuous entries. Finite matrix
multiplication makes the coordinate action jointly continuous. Map the coordinate L-space
into U by its chosen basis and take the image as an actual submodule. Linear independence
identifies this submodule with the coordinate model, and the finite-basis base-change
theorem supplies the canonical tensor-product comparison with U. This also covers U=0. -/
theorem isLAdic_subrepresentation
    (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [Algebra ℚ_[l] K]
    [IsAlgClosure ℚ_[l] K] (G : ProfiniteGrp.{v})
    (V : Type w) [AddCommGroup V] [Module K V]
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : IsLAdic l K G V ρ)
    (U : Submodule K V) (τ : G →* (U ≃ₗ[K] U))
    (hτ : ∀ (g : G) (v : U), (τ g v : V) = ρ g (v : V)) :
    IsLAdic l K G U τ := by
  classical
  obtain ⟨hfin, E, hE, W, τE, hcE, hτE, e, he⟩ := hρ
  have := hfin
  have := hE
  let := Module.compHom V (algebraMap E K)
  have : FiniteDimensional E W := hcE.1
  let c := Module.finBasis E W
  let a := (c.baseChange K).map e
  let b := Module.finBasis K U
  obtain ⟨U', hU'⟩ := U.exists_isCompl
  let p : V →ₗ[K] U := U.projectionOnto U' hU'
  let A := LinearMap.toMatrix b a U.subtype
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
    change p (ρ g (v : V)) = τ g v
    rw [← hτ]
    exact Submodule.projectionOnto_apply_left hU' _
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


end Representation
