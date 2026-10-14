/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagramCore
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.FlatTruncationTower

/-! # A compatible flat-tower diagram over a cochain arrow

Source: the diagram construction in lem-sc-flat-telescope-stage-map-refinement,
step 1, using Stacks Project Tags 06YS, 06YJ and 077J.
(blueprint: lem-sc-flat-telescope-arrow-diagram).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Construct the bounded-flat tower diagram over a cochain arrow, together with
its augmentation to the good truncations of the source. This is the construction
step only: the augmentation's quasi-isomorphism and the stage-map predicates are
verified separately by the caller.

Source: step 1 and the diagram-construction portion of step 2 of
lem-sc-flat-telescope-stage-map-refinement; Stacks Project Tags 06YS and 077J,
bounded flat resolutions and compatible-pair lifts. The assertion about maps to
supplied telescope models is an expansion of that plan, not a literal Stacks lemma.

Proof. Choose the towers presenting P and P'. Lift the source arrow f on their
sum-and-cone models. Resolve the arrow diagram over the successive good truncations
of P by flat covers, keeping the preceding stage and the two maps in the resolution
state. Resolve the compatible pairs at each successor stage; adjoining the mapping
cylinders of transition homotopies makes the transition squares strict. All terms
remain flat, since only sums and split extensions of flat terms are used, and each
stage is bounded above. Sort the generators by their finite support in the two
original sums and then diagonalize. Allow cofinal replacement of the two original
towers: a fixed original stage need not contain all the images at the corresponding
source stage. Cofinality gives the homotopy isomorphisms e₁ and e₂. The source tower
comes with its quasi-isomorphic maps q to the good truncations of P, strictly
compatible after the inclusions into P. Its canonical cone augmentation g has zero
shifted-summand component and the displayed unshifted-summand component. The two
strict sum squares give the cone maps m₁ and m₂. The retained arrow homotopies give
Q(g) = Q(m₁);e₁ and Q(g);Q(f) = Q(m₂);e₂. These are homotopy-category equalities,
not merely equalities after derived localization. The zero and identity arrows
use the zero and identical diagram maps; on an empty scheme the construction is
the zero diagram. No projectivity or finite-generation hypothesis is used.
(blueprint: lem-sc-flat-telescope-arrow-diagram-construction).
Proof. Given the structural towers, perform the compatible-pair flat resolutions and
mapping-cylinder strictification described in the construction plan; this supplies
the cone augmentation, truncation quasi-isomorphisms, and homotopy-category
compatibilities. -/
theorem exists_flat_telescope_arrow_diagram_construction (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P')
    (hcore : ∃ (E₀ E₁ E₂ : ℕ →
        CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i))) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (e₁ : Q.obj (CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁)) ≅
          Q.obj P)
        (e₂ : Q.obj (CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂)) ≅
          Q.obj P')
        (g : CochainComplex.mappingCone (flatTelescopeDifferential E₀ t₀) ⟶ P)
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        (CochainComplex.mappingCone.inr _ ≫ g =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))) ∧
        ((CochainComplex.mappingCone.inl _).comp
          (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero _) = 0) ∧
        (Q.map g = Q.map (CochainComplex.mappingCone.map
          (flatTelescopeDifferential E₀ t₀) (flatTelescopeDifferential E₁ t₁)
          (Limits.Sigma.map a) (Limits.Sigma.map a) c₁) ≫ e₁.hom) ∧
        (Q.map g ≫ Q.map f = Q.map (CochainComplex.mappingCone.map
          (flatTelescopeDifferential E₀ t₀) (flatTelescopeDifferential E₂ t₂)
          (Limits.Sigma.map b) (Limits.Sigma.map b) c₂) ≫ e₂.hom) := by sorry


theorem exists_flat_telescope_arrow_diagram (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P') :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (e₁ : Q.obj (CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁)) ≅
          Q.obj P)
        (e₂ : Q.obj (CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂)) ≅
          Q.obj P')
        (g : CochainComplex.mappingCone (flatTelescopeDifferential E₀ t₀) ⟶ P)
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        (CochainComplex.mappingCone.inr _ ≫ g =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))) ∧
        ((CochainComplex.mappingCone.inl _).comp
          (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero _) = 0) ∧
        (Q.map g = Q.map (CochainComplex.mappingCone.map
          (flatTelescopeDifferential E₀ t₀) (flatTelescopeDifferential E₁ t₁)
          (Limits.Sigma.map a) (Limits.Sigma.map a) c₁) ≫ e₁.hom) ∧
        (Q.map g ≫ Q.map f = Q.map (CochainComplex.mappingCone.map
          (flatTelescopeDifferential E₀ t₀) (flatTelescopeDifferential E₂ t₂)
          (Limits.Sigma.map b) (Limits.Sigma.map b) c₂) ≫ e₂.hom) := by
  have hcore := exists_flat_telescope_arrow_core Y P P' hP hP' f
  exact exists_flat_telescope_arrow_diagram_construction Y P P' hP hP' f hcore

end AlgebraicGeometry
