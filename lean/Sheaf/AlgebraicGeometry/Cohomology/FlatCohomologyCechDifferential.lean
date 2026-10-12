/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.Sheaves.CechComparison

/-! # Naturality of canonical Cech base-change components

Source: Stacks Project, Tags 02KH and 02KG, the separated-case Cech argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} {ι : Type u}

/-- Canonical component maps commute with the alternating Cech differential.
This is a naturality assertion and does not assert invertibility of any component.

Source: Stacks Project, Tag 02KH, separated-case Cech argument, and the
coordinate differential formula in WeilConjectures.Topology.Sheaves.CechComparison.
(blueprint: lem-pc-flat-cech-base-change-differential)

Proof: Test the equality on pure tensors b tensor x, which span scalar extension.
Then test each target tuple coordinate; product projections and restriction along
an isomorphism of opens are jointly injective. In the coordinate differential
formula, each summand is the restriction of a face coordinate with sign (-1)^i.
Apply the assumed coordinate equation to each face. Naturality of the module
adjunction unit moves restriction across the pulled-back section. Naturality of
the structure-sheaf map moves the image of b across the same restriction. Inverse
image preserves the finite intersections; all maps between these opens agree
because the category of opens is thin. Linearity distributes b over the finite
alternating sum. The two sides therefore have equal coordinates. Tensor induction
and product extensionality finish. The empty index type gives no coordinates and
zero terms; empty opens have zero sections. There is no affine or flat hypothesis:
only naturality of the unit and the assumed pure-tensor formula are used. -/
theorem cechBaseChange_components_comm (f : X ⟶ Spec (.of R))
    (U : ι → X.Opens) (M : X.Modules)
    (hI : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, baseChangeFst (S := S) f ⁻¹ᵁ U (y l)) ≤
        baseChangeFst (S := S) f ⁻¹ᵁ (⨅ l, U (y l))) :
    let g := baseChangeFst (S := S) f
    let V : ι → (baseChangedScheme (S := S) f).Opens := fun i ↦ g ⁻¹ᵁ U i
    let N := baseChangedModule (S := S) f M
    let P := M.presheafModuleCat ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let Q := N.presheafModuleCat ⋙ ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    let C := (cechComplexFunctor U).obj P
    let A := ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℕ)).obj C
    let B := (cechComplexFunctor V).obj Q
    let a := fun (k : ℕ) (y : Fin (k + 1) → ι) (x : C.X k) ↦
      M.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op
        (TopCat.Presheaf.cechComplexFunctorπ U P k y x)
    let z := fun (k : ℕ) (y : Fin (k + 1) → ι) (x : B.X k) ↦
      N.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op
        (TopCat.Presheaf.cechComplexFunctorπ V Q k y x)
    ∀ c : ∀ k, A.X k ⟶ B.X k,
      (∀ (k : ℕ) (y : Fin (k + 1) → ι) (b : S) (x : C.X k),
      z k y (c k (b ⊗ₜ[R] x)) =
        ((baseChangedScheme (S := S) f).presheaf.map
          (homOfLE (le_top : (⨅ l, V (y l)) ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom b) •
          N.presheaf.map (homOfLE (hI k y)).op
            ((baseChangeUnit (S := S) f M).val.app (op (⨅ l, U (y l))) (a k y x))) →
      ∀ k, c k ≫ B.d k (k + 1) = A.d k (k + 1) ≫ c (k + 1) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
