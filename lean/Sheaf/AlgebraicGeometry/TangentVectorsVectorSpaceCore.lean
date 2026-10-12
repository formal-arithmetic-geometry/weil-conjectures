module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.DualNumberSchemePushout

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-! Core pushout and gluing assertions for dual-number tangent vectors.
(blueprint: lem-sc-tangent-vectors-core)

Proof in words: apply the dual-number scheme pushout theorem to the two
coordinate projections, then use the local-ring description of maps from
spectra to obtain existence and uniqueness of the glued morphism. The
compatibility with the structure morphism follows by uniqueness after
mapping to `Spec k`. -/
/-- Core pushout and gluing assertions for dual-number tangent vectors.
(blueprint: lem-sc-tangent-vectors-core)

Proof in words: use the dual-number pushout construction and the local-ring
 description of maps from spectra. The core establishes the pushout, unique
 gluing, and structure-map compatibility; the operations establish closure,
 additive-group laws, and module laws by the coordinate formulas and
 three-coordinate gluing identities. -/
theorem tangentVectors_core
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
    let r : E ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K (Fin 2 → K)))
    let j : Fin 2 → (D ⟶ E) := fun i =>
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)
    let T := {θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}
    IsPushout c c (j 0) (j 1) ∧
      (∀ θ₁ θ₂ : T, ∃! Θ : E ⟶ X, j 0 ≫ Θ = θ₁.val ∧ j 1 ≫ Θ = θ₂.val) ∧
      (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
        j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → Θ ≫ p = r ≫ b ≫ p) := by
  sorry

end AlgebraicGeometry
