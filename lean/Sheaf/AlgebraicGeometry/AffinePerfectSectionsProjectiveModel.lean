/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Bounded projective models of ordinary affine sections

Source: Stacks Project, Tags 08EB, 0656, 06Z0 and 01IB.
(blueprint: lem-pc-affine-perfect-sections-projective-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Ordinary sections of a bounded-above quasi-coherent perfect complex on an affine
scheme have a bounded finite-projective representative in the ring derived category.
Source: Stacks Project, Tags 08EB (perfect-lemma-perfect-affine), 0656, 06Z0 and 01IB.
(blueprint: lem-pc-affine-perfect-sections-projective-model).

Proof: Transport D along the canonical affine chart Y.isoSpec to Spec Gamma(Y,O).
The affine quasi-coherent counits, natural in the differentials, identify this
transported complex with the termwise associated sheaf of the ordinary section
complex. Its homology sheaves are quasi-coherent because associated sheaves are
exact, so its derived image is an object of D_QCoh. Perfectness transports across
the scheme isomorphism. Apply the affine bounded-projective characterization to
obtain P with integer bounds and finite projective terms, and a derived isomorphism
between tilde(P) and the transported D. Compose with the termwise counit comparison.
Full faithfulness of the affine derived equivalence then lifts that isomorphism
and its inverse to the ring derived category, yielding the displayed isomorphism
between Q(P) and Q of ordinary sections of D. This argument avoids choosing an
injective resolution of D. For the empty affine scheme the section ring is the
zero ring and the zero complex is a representative. The result is existential;
no construction chooses an arbitrary witness of this unproved theorem. -/
theorem exists_affine_perfect_sections_projective_model
    (Y : Scheme.{u}) (hY : IsAffine Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    [HasDerivedCategory.{v} (ModuleCat.{u} (Γ(Y, ⊤) : Type u))]
    (D : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hDle : D.IsStrictlyLE d)
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (hperfect : Y.IsPerfect ((DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).obj D)) :
    ∃ (P : CochainComplex (ModuleCat.{u} (Γ(Y, ⊤) : Type u)) ℤ) (a b : ℤ),
      (∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (Γ(Y, ⊤) : Type u) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (Γ(Y, ⊤) : Type u) (P.X n)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj
        (((SheafOfModules.evaluation.{u}
          (moduleRings Y.toRingedSpace) (op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D)) := by sorry

end AlgebraicGeometry.Scheme.Modules
