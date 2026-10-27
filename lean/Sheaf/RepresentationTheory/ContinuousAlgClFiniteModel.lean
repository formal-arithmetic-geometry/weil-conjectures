/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.RepresentationTheory.LAdic
public import Mathlib.NumberTheory.Padics.Complex
import WeilConjectures.RepresentationTheory.IntegralModel
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Finite fields of definition for continuous algebraic p-adic representations

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, first bullet.
-/

@[expose] public noncomputable section
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

private theorem continuous_finite_model_entry
    (l : ℕ) [Fact l.Prime] {T : Type u} [TopologicalSpace T]
    {E : Type w} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (i : E →ₐ[ℚ_[l]] PadicAlgCl l) (f : T → E)
    (hf : Continuous fun t ↦ i (f t)) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    Continuous f := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : NormedAlgebra ℚ_[l] E := spectralNorm.normedAlgebra ℚ_[l] E
  have hi := i.toLinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr i.injective)
  exact hi.isEmbedding.continuous_iff.mpr hf

/-- A finite-dimensional representation of a profinite group whose dual matrix
coefficients are continuous has a continuous model over a finite p-adic extension.
The model is an actual invariant subspace, with the canonical scalar-extension map.

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, first bullet
(blueprint: lem-sfb-continuous-algcl-finite-model).

Proof: choose a finite basis. The dual-coordinate continuity hypothesis makes the
associated matrix homomorphism continuous entry by entry. The compact matrix descent
theorem gives a finite intermediate field containing every entry. Corestrict the
matrices to that field; its topology is the subspace topology from the algebraic closure,
so their entries remain continuous. Injectivity of the field inclusion proves the
matrix group laws. The induced action on the finite coordinate space is jointly
continuous, since every output coordinate is a finite sum of products. Map this
coordinate space into the given representation by the chosen basis. Linear independence
identifies its image with the coordinate space, and transport gives a continuous
invariant-subspace action. The finite-basis base-change equivalence sends a pure tensor
to its scalar multiple in the original space. The same argument includes the zero space.
-/
theorem isLAdic_of_continuous_dual_coefficients
    (l : ℕ) [Fact l.Prime] (G : ProfiniteGrp.{u})
    (V : Type v) [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V]
    (ρ : G →* (V ≃ₗ[PadicAlgCl l] V))
    (hρ : ∀ (f : Module.Dual (PadicAlgCl l) V) (v : V),
      Continuous fun g : G ↦ f (ρ g v)) :
    IsLAdic l (PadicAlgCl l) G V ρ := by
  classical
  let b := Module.finBasis (PadicAlgCl l) V
  let r : Representation (PadicAlgCl l) G V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  let m : G →* Matrix (Fin (Module.finrank (PadicAlgCl l) V))
      (Fin (Module.finrank (PadicAlgCl l) V)) (PadicAlgCl l) :=
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp r
  have hm_eq (g : G) (i j : Fin (Module.finrank (PadicAlgCl l) V)) :
      m g i j = b.repr (ρ g (b j)) i :=
    LinearMap.toMatrixAlgEquiv_apply b (r g) i j
  have hm (i j : Fin (Module.finrank (PadicAlgCl l) V)) :
      Continuous fun g : G ↦ m g i j := by
    apply (hρ (b.coord i) (b j)).congr
    intro g
    simpa only [Module.Basis.coord_apply] using (hm_eq g i j).symm
  obtain ⟨E, hE, hmem⟩ := PadicAlgCl.exists_finiteDimensional_forall_mem l m hm
  let : FiniteDimensional ℚ_[l] E := hE
  let M (g : G) (i j : Fin (Module.finrank (PadicAlgCl l) V)) : E :=
    ⟨m g i j, hmem g i j⟩
  apply isLAdic_of_matrix_model l (PadicAlgCl l) G V ρ E b M
  · intro g i j
    exact hm_eq g i j
  · intro i j
    exact continuous_finite_model_entry l E.val (fun g ↦ M g i j) (hm i j)

end Representation
