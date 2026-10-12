module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.DualNumberSchemePushout

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-! Additive and scalar operations on dual-number tangent vectors.
(blueprint: lem-sc-tangent-vectors-operations)

Proof in words: use the dual-number pushout construction for the sum and
scalar maps. The coordinate formulas establish closure in the tangent-vector
subtype; the three-coordinate gluing identities give the additive-group and
module laws, with the constant map as zero and scaling by minus one as inverse. -/
/-- Additive and scalar operations on dual-number tangent vectors.
(blueprint: lem-sc-tangent-vectors-operations)

Proof in words: use the dual-number pushout construction and the local-ring
 description of maps from spectra. The core establishes the pushout, unique
 gluing, and structure-map compatibility; the operations establish closure,
 additive-group laws, and module laws by the coordinate formulas and
 three-coordinate gluing identities. -/
theorem tangentVectors_operations
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    let K := X.residueField x
    let D := Spec (.of (DualNumber K))
    let E := Spec (.of (TrivSqZeroExt K (Fin 2 → K)))
    let b := X.fromSpecResidueField x
    let c : Spec K ⟶ D :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
    let q : D ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
    let j : Fin 2 → (D ⟶ E) := fun i =>
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)
    let s : D ⟶ E := Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map
        ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1)).toRingHom)
    let m : K → (D ⟶ D) := fun t => Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map (t • (LinearMap.id : K →ₗ[K] K))).toRingHom)
    let T := {θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}
    ∃ a : AddCommGroup T, letI := a;
      ∃ v : Module K T, letI := v;
        (0 : T).val = q ≫ b ∧
        (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
          j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → (θ₁ + θ₂).val = s ≫ Θ) ∧
        (∀ (t : K) (θ : T), (t • θ).val = m t ≫ θ.val) := by
  sorry

end AlgebraicGeometry
