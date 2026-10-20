/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.FlatTelescopeArrowCocycles

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

private theorem telescope_augmentation
    (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1))
    (q : ∀ n : ℕ, E n ⟶ P.truncLE (n : ℤ))
    (hc : ∀ n : ℕ, t n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
      q n ≫ P.ιTruncLE (n : ℤ)) :
    ∃ g : CochainComplex.mappingCone (flatTelescopeDifferential E t) ⟶ P,
      CochainComplex.mappingCone.inr _ ≫ g =
        Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ∧
      (CochainComplex.mappingCone.inl _).comp
        (CochainComplex.HomComplex.Cochain.ofHom g) (add_zero _) = 0 := by
  let s := Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ))
  have hz : flatTelescopeDifferential E t ≫ s = 0 := by
    dsimp [flatTelescopeDifferential, s]
    rw [Preadditive.sub_comp, Category.id_comp]
    apply sub_eq_zero.mpr
    apply Sigma.hom_ext
    intro n
    simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
    exact (hc n).symm
  have hd : CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain (∐ E) P (-1)) =
      CochainComplex.HomComplex.Cochain.ofHom (flatTelescopeDifferential E t ≫ s) := by
    rw [hz]
    simp
  exact ⟨CochainComplex.mappingCone.desc _ 0 s hd,
    CochainComplex.mappingCone.inr_desc _ 0 s hd,
    CochainComplex.mappingCone.inl_desc _ 0 s hd⟩

open CochainComplex.HomComplex in
private theorem cone_comparison
    {Y : Scheme.{u}}
    {F G P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    (φ : F ⟶ F) (ψ : G ⟶ G) (a : F ⟶ G) (hc : φ ≫ a = a ≫ ψ)
    (r : CochainComplex.mappingCone ψ ⟶ P)
    (s : F ⟶ P) (g : CochainComplex.mappingCone φ ⟶ P)
    (hinr : CochainComplex.mappingCone.inr φ ≫ g = s)
    (hinl : (CochainComplex.mappingCone.inl φ).comp (Cochain.ofHom g) (add_zero _) = 0)
    (α : Cochain F P (-2)) (β : Cochain F P (-1))
    (hα : (0 : Cochain F P (-1)) = δ (-2) (-1) α +
      (Cochain.ofHom φ).comp β (zero_add _) +
      (Cochain.ofHom a).comp ((CochainComplex.mappingCone.inl ψ).comp
        (Cochain.ofHom r) (add_zero _)) (zero_add _))
    (hβ : Cochain.ofHom s = δ (-1) 0 β +
      Cochain.ofHom (a ≫ CochainComplex.mappingCone.inr ψ ≫ r)) :
    Nonempty (Homotopy g (CochainComplex.mappingCone.map φ ψ a a hc ≫ r)) := by
  constructor
  apply CochainComplex.mappingCone.descHomotopy φ _ _ α β
  · rw [hinl]
    convert hα using 1
    rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_second_is_zero_cochain]
    simp only [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inl_desc]
    rw [Cochain.comp_assoc_of_third_is_zero_cochain]
  · simpa only [hinr, CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.mappingCone.inr_desc_assoc] using hβ

/-- Assemble a simultaneous flat tower diagram from its summand cocycles.
Source: parent construction steps 1--3; Mathlib mapping-cone descent and homotopy
constructors. The finite-piece bar construction supplies the geometric input.
Proof. Strict truncation compatibility annihilates the one-minus-shift differential.
Descend the sum augmentation to the source cone, with shifted component zero.
The two pairs of summand cochain identities give the two comparison homotopies by
`mappingCone.descHomotopy`. Pass to the homotopy category and take the isomorphisms
associated with the target augmentation maps.
(blueprint: lem-sc-flat-telescope-arrow-diagram). -/
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
  dsimp only
  obtain ⟨E₀, E₁, E₂, t₀, t₁, t₂, a, b, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    c₁, c₂, r₁, r₂, q, hr₁, hr₂, hq, hc, α₁, β₁, α₂, β₂, hα₁, hβ₁, hα₂, hβ₂⟩ :=
    exists_flat_telescope_arrow_cocycles Y P P' hP hP' f
  obtain ⟨g, hinr, hinl⟩ := telescope_augmentation Y P E₀ t₀ q hc
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
  let : IsIso (Q.map r₁) := hr₁
  let : IsIso (Q.map r₂) := hr₂
  refine ⟨E₀, E₁, E₂, t₀, t₁, t₂, a, b, hb₀, hf₀, hb₁, hf₁, hb₂, hf₂,
    c₁, c₂, asIso (Q.map r₁), asIso (Q.map r₂), g, q, hq, hc, hinr, hinl, ?_, ?_⟩
  · obtain ⟨H⟩ := cone_comparison (flatTelescopeDifferential E₀ t₀)
      (flatTelescopeDifferential E₁ t₁) (Limits.Sigma.map a) c₁ r₁ _ g
      hinr hinl α₁ β₁ hα₁ hβ₁
    simpa only [Functor.map_comp, asIso_hom] using
      HomotopyCategory.eq_of_homotopy _ _ H
  · have hinr' : CochainComplex.mappingCone.inr _ ≫ (g ≫ f) =
        Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ≫ f := by
      rw [← Category.assoc, hinr]
    have hinl' : (CochainComplex.mappingCone.inl _).comp
        (CochainComplex.HomComplex.Cochain.ofHom (g ≫ f)) (add_zero _) = 0 := by
      rw [CochainComplex.HomComplex.Cochain.ofHom_comp,
        ← CochainComplex.HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain,
        hinl, CochainComplex.HomComplex.Cochain.zero_comp]
    obtain ⟨H⟩ := cone_comparison (flatTelescopeDifferential E₀ t₀)
      (flatTelescopeDifferential E₂ t₂) (Limits.Sigma.map b) c₂ r₂ _ (g ≫ f)
      hinr' hinl' α₂ β₂ hα₂ hβ₂
    simpa only [Functor.map_comp, asIso_hom] using
      HomotopyCategory.eq_of_homotopy _ _ H


-- Preserve the legacy signature, whose core proposition binds unused maps.
set_option linter.unusedVariables false in
/-- Construct the bounded-flat tower diagram over a cochain arrow, together with
its augmentation to the good truncations of the source. This is the construction
step only: the augmentation's quasi-isomorphism and the stage-map predicates are
verified separately by the caller.

Source: step 1 and the diagram-construction portion of step 2 of
lem-sc-flat-telescope-stage-map-refinement; Stacks Project Tags 06YS and 077J,
bounded flat resolutions and compatible-pair lifts. The assertion about maps to
supplied telescope models is an expansion of that plan, not a literal Stacks lemma.

Proof. Apply the unconditional arrow-diagram theorem proved above; the
legacy structural-core hypothesis is not needed. That theorem constructs the
source augmentation by mapping-cone descent from strictly compatible truncation
maps, and proves both comparisons with the cone homotopy constructor. The tower
and target augmentation input comes from the finite-piece bar construction,
through its zero comparison cochains. This replaces the former invalid claim
that finite support of individual generators gives a single bound for an entire
source stage. The bar construction includes all finite source pieces at each
stage and does not make that claim.
(blueprint: lem-sc-flat-telescope-arrow-diagram-construction). -/
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
          (Limits.Sigma.map b) (Limits.Sigma.map b) c₂) ≫ e₂.hom) := by
  clear hcore
  exact exists_flat_telescope_arrow_diagram Y P P' hP hP' f

end AlgebraicGeometry
